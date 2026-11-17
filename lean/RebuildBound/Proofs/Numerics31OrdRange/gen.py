#!/usr/bin/env python3
"""Complete ordinary range certificates, deriving rows and counts from inventory.

The frozen Lean entrypoint checks every configuration class and every geometry.
Integrated exact-mass chains and pilot row theorems are reused; Python outputs
remain untrusted inputs to the existing kernel checkers.
"""
import argparse
import importlib.util
import json
import math
import multiprocessing as mp
import re
import sys
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
PILOT = None
PILOT_ROOT = None


def helper(source_root):
    global PILOT, PILOT_ROOT
    source_root = Path(source_root).resolve()
    if PILOT_ROOT is not None and PILOT_ROOT != source_root:
        raise ValueError('A generator process may use only one arithmetic source root')
    if PILOT is None:
        PILOT_ROOT = source_root
        path = Path(source_root) / 'RebuildBound/Proofs/Numerics31Range/gen.py'
        spec = importlib.util.spec_from_file_location('ordinary_pilot', path)
        PILOT = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(PILOT)
        PILOT.known_chain = known_chain
    return PILOT


def qualify(namespace, name):
    return namespace + '.' + name if name.startswith('Tab.') else 'RebuildBound.' + name


@lru_cache(None)
def chain_registry(source_root, include_all=False):
    """Index existing theorem signatures; every reused proof is imported by Lean.

    A chain key contains its depth, radix and exact reduced finite-word mass.
    Early population and root count belong only to the fresh final check.
    """
    root = Path(source_root)
    tables, thins, convs = {}, [], {}
    packages = [('SelRange3', 3), ('SelRange5', 5), ('SelRange7', 7), ('NCA5', 5)]
    # Family generators may also reuse previous final packages. The original
    # generator excludes its own output to avoid circular imports on reruns.
    if include_all:
        packages += [('DirectJobANumerics', None), ('Numerics31Range', None),
                     ('Numerics31OrdRange', None), ('TPNum', 1)]
    for package, radix in packages:
        for path in sorted((root / 'RebuildBound/Proofs' / package).glob('*.lean')):
            text = path.read_text()
            if package == 'TPNum':
                text = re.sub(r'checkThin (\d+) 1 2 64 256', r'checkThin \1 1 (2 ^ 1) 64 256', text)
            namespaces = re.findall(r'^namespace (RebuildBound\.\S+)', text, re.M)
            if not namespaces:
                continue
            namespace = namespaces[0]
            module = '.'.join(path.relative_to(root).with_suffix('').parts)
            for name in re.findall(r'def (\w+) : List \(List Nat\)', text):
                tables[namespace + '.' + name] = (path, name)
            for name, width, qc, nb, depth, table in re.findall(
                r'theorem (\w+) : (?:NCA5\.)?checkThin (\d+) (\d+) \(2 \^ (\d+)\) 64 256 NCA1.Tab.t(\d+) (\S+) = true', text):
                thins.append(dict(radix=radix, depth=int(depth), qc=int(qc), nb=int(nb),
                    width=int(width), table=qualify(namespace, table),
                    proof=namespace + '.' + name, module=module))
            for name, width, previous, thin, output in re.findall(
                r'theorem (\w+) : (?:NCA5\.)?checkConv (\d+) \(2 \^ 320\) 256 (\S+) (\S+) (\S+) = true', text):
                previous, thin, output = [qualify(namespace, n) for n in [previous, thin, output]]
                convs[(previous, thin)] = (int(width), output, namespace + '.' + name, module)
    result = {}
    for thin in thins:
        previous = thin['table']; steps = []
        for _ in range(2, (thin['radix'] or 7) + 1):
            conv = convs.get((previous, thin['table']))
            if conv is None:
                break
            steps.append(conv); previous = conv[1]
        radix = thin['radix'] or len(steps) + 1
        if len(steps) != radix - 1:
            continue
        key = (thin['depth'], radix, Fraction(thin['qc'], 2 ** thin['nb']))
        result.setdefault(key, (thin, steps, tables))
    return result


@lru_cache(None)
def loaded_chain(source_root, key, include_all=False):
    found = chain_registry(source_root, include_all).get(key)
    if not found:
        return None
    thin, convs, tables = found
    read = helper(source_root).read_named_table
    def matrix(name):
        path, local = tables[name]
        return read(path, local)
    return dict(reuse='integrated', qc=thin['qc'], nb=thin['nb'], width=thin['width'],
        thin=matrix(thin['table']), steps=[(width, matrix(table)) for width, table, _, _ in convs],
        thin_table=thin['table'], thin_proof=thin['proof'],
        step_tables=[t for _, t, _, _ in convs], conv_proofs=[p for _, _, p, _ in convs],
        imports=list(dict.fromkeys([thin['module']] + [m for _, _, _, m in convs])))


def known_chain(source_root, job):
    if job['kind'] == 'direct':
        return None
    return loaded_chain(str(source_root), (job['t'], job['r'], Fraction(job['qc'], 2 ** job['nb'])))


def compute(inputs):
    source_root, cache, job = inputs
    result = helper(source_root).compute_job((source_root, cache, job))
    reused = known_chain(source_root, job)
    if reused:
        result.update(reused)
    return result


def emitter_class(pilot):
    class Emitter(pilot.Emitter):
        def class_certificate(self, data, tn, td, lane):
            if data.get('reuse') != 'integrated':
                return super().class_certificate(data, tn, td, lane)
            j, fp = data['job'], data['final']
            imports, _ = self.lanes[lane]
            imports.extend(x for x in data['imports'] if x not in imports)
            previous = data['step_tables'][-1] if data['step_tables'] else data['thin_table']
            final_name = self.check(lane, 'final_' + j['label'], data['imports'],
                f'NCA1.checkFinal {fp["wf"]} (2 ^ 320) 100 {fp["rr"]} 32 256 64 (2 ^ {j["i"]}) {j["p"]} {j["qc"]} (2 ^ {j["nb"] + j["t"]}) 32 1 0 {fp["fuel"]} {tn} {td} 0 [NCA5.rootMarg 64 {previous}]')
            steps = ', '.join(f'({w}, {table})' for (w, _), table in zip(data['steps'], data['step_tables']))
            chain = ('⟨' + ', '.join(data['conv_proofs'] + ['trivial']) + '⟩'
                     if data['conv_proofs'] else '(by trivial)')
            return (f'SelRange3.class_bound RebuildBound.P10r (r := {j["r"]}) (t := {j["t"]}) (P := {j["p"]}) (i := {j["i"]}) '
                f'(nb := {j["nb"]}) (qc := {j["qc"]}) (qcT := {data["qc"]}) (nbT := {data["nb"]})\n'
                f'    (steps := [{steps}]) q hq SelRange1.bnd{j["t"]} rfl\n'
                f'    (by norm_num) (by norm_num) (by norm_num) rfl (by norm_num) {data["thin_proof"]} {chain} {final_name}')
    return Emitter


def all_rows(inventory, pilot_spec, ordinary_spec, pilot):
    assert 'def ordinaryRangeBudget31' in ordinary_spec
    assert 'config31.levels - 1, 6' in ordinary_spec
    assert '1 / 2 ^ 71 else 1 / 2 ^ 72' in ordinary_spec
    assert 'config31.ordinaryCount p.1 p.2' in ordinary_spec
    pilots = {(l, d): Fraction(n, den) for l, d, n, den in pilot.parse_rows(pilot_spec)}
    levels = len(inventory['level_fanouts']) + 1
    rows = []
    for g in inventory['shapes']['sep']:
        l, d = g['level'], g['digit']
        count = inventory['clocks'][f'ordinary_L{l}_d{d}']['exposures']
        assert count > 0
        budget = pilots.get((l, d), Fraction(1, 2 ** (71 if (l,d) == (levels-1,6) else 72)) / count)
        row = pilot.row_job((l, d, budget.numerator, budget.denominator), g)
        row['pilot'] = (l, d) in pilots
        # Reuse classification is geometry-derived by the checked inventory.
        cert = next(c for c in inventory['certificate_inventory'] if c['name'] == f'ordinary_L{l}_d{d}')
        row['selected'] = cert['numerics'] == 'reused'
        rows.append(row)
    assert len({(r['level'],r['digit']) for r in rows}) == len(rows)
    return rows


def validate_output(output_dir, module_prefix, source_root):
    output_dir = output_dir.resolve()
    if output_dir.name != module_prefix.rsplit('.', 1)[-1] or output_dir.name != 'Numerics31OrdRange':
        raise ValueError('Output must be a Numerics31OrdRange directory and module')
    entrypoint = output_dir.with_suffix('.lean')
    if entrypoint.resolve() != entrypoint:
        raise ValueError('Refusing an entrypoint symlink')
    own = Path(__file__).resolve().parent
    roots = {Path(source_root).resolve()}
    if len(own.parents) > 2:
        roots.add(own.parents[2])
    for root in roots:
        proofs = root / 'RebuildBound/Proofs'
        if not proofs.exists():
            continue
        for path in proofs.iterdir():
            if path in [own, own.with_suffix('.lean')]:
                continue
            if path.is_dir() and (output_dir.is_relative_to(path) or path.is_relative_to(output_dir)):
                raise ValueError(f'Output overlaps protected proof sources: {path}')
            if path.is_file() and entrypoint == path.resolve():
                raise ValueError(f'Entrypoint overlaps protected proof source: {path}')
    return output_dir


def selected_geometry(source_root, package, theorem):
    matches = []
    for path in (Path(source_root) / 'RebuildBound/Proofs' / package).glob('*.lean'):
        matches.extend(re.findall(r'theorem ' + re.escape(theorem) + r' : selRange (\{[^}]+\}) ≤', path.read_text()))
    if len(matches) != 1:
        raise ValueError(f'Expected exactly one integrated shape theorem {package}.{theorem}')
    return matches[0]


def generate(args):
    args.output_dir = validate_output(args.output_dir, args.module_prefix, args.source_root)
    pilot = helper(args.source_root)
    inventory = json.loads(args.inventory.read_text())
    rows = all_rows(inventory, args.pilot_spec.read_text(), args.spec.read_text(), pilot)
    fresh = [r for r in rows if not r['pilot'] and not r['selected']]
    jobs = [j for r in fresh for j in pilot.class_jobs(r)]
    assert all(j['r'] * (2 ** j['t'] - 1) + 1 <= 4000 for j in jobs)
    inputs = [(str(args.source_root), str(args.cache_dir) if args.cache_dir else None, j) for j in jobs]
    if args.jobs == 1:
        results = list(map(compute, inputs))
    else:
        with mp.Pool(min(args.jobs, len(jobs))) as pool:
            results = pool.map(compute, inputs)
    data = {d['job']['label']: d for d in results}
    emitter = emitter_class(pilot)(args.output_dir, args.module_prefix, args.lanes)
    proof = []; lane_counter = 0
    for row in rows:
        tag = row['tag']; l, d = row['level'], row['digit']
        row_type = (f'selRange {row["geom"]} ≤ ENNReal.ofReal '
                    f'({pilot.lean_fraction(row["bn"], row["bd"])} : ℝ)')
        if row['pilot']:
            proof.append(f'theorem row_{tag} : {row_type} :=\n  RebuildBound.Numerics31Range.row_{tag}\n')
            continue
        if row['selected']:
            namespace = 'SelRange1' if row['r'] == 1 else 'SelRange3'
            shape = selected_geometry(args.source_root, namespace, f'hL{l}d{d}')
            proof.append(f'theorem row_{tag} : {row_type} := by\n'
                f'  have hgeom : {row["geom"]} = {shape} := by decide +kernel\n'
                f'  rw [hgeom]\n'
                f'  have h := RebuildBound.{namespace}.hL{l}d{d}\n'
                f'  exact h.trans (ENNReal.ofReal_le_ofReal (by norm_num))\n')
            continue
        labels = [j['label'] for j in pilot.class_jobs(row)]
        tn, td = pilot.target(max(data[label]['final']['total'] for label in labels))
        if row['kind'] == 'direct':
            tn, td = data[labels[0]]['final']['tn'], data[labels[0]]['final']['td']
        certificates = []
        for label in labels:
            x = data[label]
            assert x['final']['total'] <= Fraction(tn,td)
            body = emitter.class_certificate(x, tn, td, lane_counter % args.lanes);lane_counter += 1
            if row['kind'] == 'direct':
                proof.append(f'theorem range_{label} : stopLoss (rangeLaw 64 32 {row["p"]} (halfPow {row["t"]}) (2 ^ {row["i"]}) {row["t"]}) 64 ≤ ({tn} : ℝ≥0∞) / ({td} : ℕ) :=\n  {body}\n')
                certificates.append('range_' + label)
            else:
                proof.append(f'theorem class_{label} (q : unitInterval) (hq : (q : ℝ) = (({x["job"]["qc"]} : ℕ) : ℝ) / ((2 ^ {row["nb"]} : ℕ) : ℝ)) :\n'
                    f'    stopLoss (rangeLawR 64 32 {row["p"]} (2 ^ {row["i"]}) {row["t"]} {row["r"]} q) 64 ≤\n'
                    f'      ({tn} : ℝ≥0∞) / ({td} : ℕ) + (2 ^ {row["i"]} : ℝ≥0∞) / 10 ^ 46 :=\n  {body}\n')
                certificates.append('class_' + label)
        twom, delta = 2 ** row['m'], row['num'] - 2 ** row['m']
        assert 0 <= delta and row['n'] * delta < twom
        if row['kind'] == 'direct':
            value = Fraction(twom,twom-row['n']*delta) * 2**row['t'] * Fraction(tn,td)
            name, params, premises = ('SelRange1.selRange_le', f'(t := {row["t"]}) (i := {row["i"]}) (P := {row["p"]})', ' '.join(['rfl']*8))
        else:
            value = Fraction(twom,twom-row['n']*delta) * 2**row['t'] * row['r'] * (Fraction(tn,td)+Fraction(2**row['i'],10**46))
            name, params, premises = ('SelRange3.selRange_le', f'(r := {row["r"]}) (t := {row["t"]}) (i := {row["i"]}) (P := {row["p"]}) (nb := {row["nb"]}) (qcA := {2**row["nb"]//row["r"]+1}) (qcB := {2**row["nb"]//row["r"]})', ' '.join(['rfl']*11))
        assert value <= Fraction(row['bn'],row['bd']), (tag,float(value),float(Fraction(row['bn'],row['bd'])))
        print(f'{tag}: log2 {math.log2(float(value)):.8f}; budget {row["bn"]}/{row["bd"]}',flush=True)
        proof.append(f'theorem row_{tag} : {row_type} :=\n  {name} {row["geom"]}\n    {params}\n'
            f'    (n := {row["n"]}) (m := {row["m"]}) (num := {row["num"]}) (tn := {tn}) (td := {td}) (bn := {row["bn"]}) (bd := {row["bd"]})\n'
            f'    {premises} {" ".join(certificates)} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n')
    emitter.emit_lanes()
    imports = ['RebuildBound.Spec.Numerics31Ordinary','RebuildBound.Proofs.Numerics31Range','RebuildBound.Proofs.SelRange3','RebuildBound.Proofs.SelRange1']+[f'{args.module_prefix}.Lane{i}' for i in range(args.lanes)]
    body=''.join(f'import {s}\n' for s in imports)+'\nopen RebuildBound.Spec RebuildBound.Model\nopen scoped ENNReal\n\n'
    body+=f'/-! Complete configuration-derived ordinary ranges. {sum(len(c) for _,c in emitter.lanes)} fresh arithmetic checks in {args.lanes} sequential lanes. -/\n\nnamespace {emitter.ns}\n\n'+'\n'.join(proof)+f'\nend {emitter.ns}\n\n'
    body+='theorem RebuildBound.Numerics31OrdRange : RebuildBound.Spec.Numerics31OrdRange_statement := by\n  unfold Numerics31OrdRange_statement\n  intro p hp\n  have hc : config31.separatedClasses = '+str([(r['level'],r['digit']) for r in rows]).replace("'",'')+' := by decide +kernel\n'
    body+='  rw [hc] at hp\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp\n  rcases hp with '+' | '.join(['rfl']*len(rows))+'\n'
    body+='\n'.join(f'  · have hb : ordinaryRangeBudget31 ({r["level"]}, {r["digit"]}) = ({r["bn"]} / {r["bd"]} : ℚ) := by decide +kernel\n    rw [hb]\n    exact {emitter.ns}.row_{r["tag"]}' for r in rows)+'\n'
    emitter.files[args.output_dir.with_suffix('.lean')]=body
    if not args.dry:
        for path,content in emitter.files.items():
            path.parent.mkdir(parents=True,exist_ok=True)
            if path.resolve() != path:
                raise ValueError(f'Refusing an output file symlink: {path}')
            content = '/- Generated by Numerics31OrdRange/gen.py; do not edit. -/\n' + content
            if not path.exists() or path.read_text() != content:
                path.write_text(content)
    print(f'Fresh checks {sum(len(c) for _,c in emitter.lanes)}; data modules {len(emitter.files)-args.lanes-1}; reused chains {sum(d.get("reuse")=="integrated" for d in results)}',flush=True)


def main():
    here=Path(__file__).resolve().parent
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-root',type=Path,default=here.parents[2])
    p.add_argument('--inventory',type=Path);p.add_argument('--spec',type=Path);p.add_argument('--pilot-spec',type=Path)
    p.add_argument('--output-dir',type=Path,default=here);p.add_argument('--module-prefix',default='RebuildBound.Proofs.Numerics31OrdRange')
    p.add_argument('--jobs',type=int,default=4);p.add_argument('--lanes',type=int,default=2);p.add_argument('--cache-dir',type=Path);p.add_argument('--dry',action='store_true')
    args=p.parse_args();args.source_root=args.source_root.resolve();args.output_dir=args.output_dir.resolve()
    args.inventory=args.inventory or args.source_root.parent/'analysis/bound_certification/code/lean_configuration_2p31.json'
    args.spec=args.spec or args.source_root/'RebuildBound/Spec/Numerics31Ordinary.lean'
    args.pilot_spec=args.pilot_spec or args.source_root/'RebuildBound/Spec/Numerics31Pilot.lean'
    assert args.jobs>0 and 0<args.lanes<=2
    generate(args)


if __name__=='__main__':
    main()
