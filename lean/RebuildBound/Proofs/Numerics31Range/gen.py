#!/usr/bin/env python3
"""Generate kernel-checked range pilots from the frozen budget list and inventory.

The selected generators supply arithmetic functions only. Their globals and
output paths are never changed. Existing certified tree tables are reused.
Two sequential Lean lanes bound concurrent expensive checks during replay.
"""
import argparse
import hashlib
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
C, H, PREC, EPS_EXP = 64, 256, 320, 46
D = 1 << PREC


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_ARITHMETIC_ROOT = None


def validate_arithmetic_source(source_root):
    root = Path(source_root).resolve()
    if _ARITHMETIC_ROOT is not None and _ARITHMETIC_ROOT != root:
        raise ValueError('A generator process may load arithmetic from only one source root')
    imported = sys.modules.get('gen')
    expected = root / 'RebuildBound/Proofs/NCA1/gen.py'
    if imported is not None and Path(imported.__file__).resolve() != expected:
        raise ValueError('Existing gen module belongs to another NCA1 source root')


@lru_cache(None)
def arithmetic(source_root):
    global _ARITHMETIC_ROOT
    validate_arithmetic_source(source_root)
    _ARITHMETIC_ROOT = Path(source_root).resolve()
    base = Path(source_root) / 'RebuildBound/Proofs'
    s1 = load_module('pilot_s1', base / 'SelRange1/gen.py')
    s3 = load_module('pilot_s3', base / 'SelRange3/gen.py')
    assert s1.D == s3.D == D and s1.H == s3.H == H
    return s1, s3


def fraction_json(value):
    if isinstance(value, Fraction):
        return {'fraction': [value.numerator, value.denominator]}
    raise TypeError(type(value).__name__)


def fraction_hook(value):
    return Fraction(*value['fraction']) if set(value) == {'fraction'} else value


def read_table(source_root, depth):
    src = (Path(source_root) / f'RebuildBound/Proofs/NCA1/Tab{depth}.lean').read_text()
    rows = re.findall(rf'def t{depth}_r(\d+) : List Nat := \[([^\]]*)\]', src)
    assert [int(m) for m, _ in rows] == list(range(C + 1))
    return [[int(v) for v in row.split(',')] if row.strip() else [] for _, row in rows]


def parse_rows(spec):
    block = spec.split('def pilotRangeBudgets31', 1)[1].split('/--', 1)[0]
    pattern = r'\(\((\d+),\s*(\d+)\),\s*(\d+)\s*/\s*2\s*\^\s*(\d+)\)'
    rows = [(int(l), int(d), int(n), 2 ** int(e)) for l, d, n, e in re.findall(pattern, block)]
    assert rows and len({(l, d) for l, d, _, _ in rows}) == len(rows)
    # Fail closed if the simple frozen list format changes.
    stripped = re.sub(pattern, '', block.split(':=', 1)[1])
    assert not re.sub(r'[\s\[\],]', '', stripped), stripped
    return rows


def row_job(row, geometry):
    level, digit, bn, bd = row
    g = geometry
    k, i, r = g['K'] + g['e'], g['I'], g['r']
    t = k - i
    early = g['C'] * (g['a_tier_pages'] + i * g['stash_pages'])
    old_d = digit - 1
    e2 = (old_d & -old_d).bit_length() - 1
    m = 64 - g['K'] - e2
    odd = old_d >> e2
    num = odd * ((2 ** m + odd - 1) // odd)
    return dict(tag=f'L{level}D{digit}', level=level, digit=digit, bn=bn, bd=bd,
                kind='direct' if r == 1 else 'odd', t=t, r=r, nb=64-k, i=i,
                p=early, n=32 * old_d * 2 ** g['K'], m=m, num=num,
                geom=f'(separatedGeometry config31 stashPages31 tierPages31 {level} {digit})')


def class_masses(nb, radix):
    """Exact finite-word masses, paired with their multiplicities."""
    quotient, remainder = divmod(2 ** nb, radix)
    return [(quotient + 1, remainder), (quotient, radix - remainder)]


def class_jobs(row):
    if row['kind'] == 'direct':
        return [dict(row, label=row['tag'])]
    nb, r = row['nb'], row['r']
    return [dict(row, label=row['tag'] + x, qc=qc)
            for x, (qc, _) in zip('AB', class_masses(nb, r))]


def source_fingerprint(source_root, depth):
    root = Path(source_root) / 'RebuildBound/Proofs'
    files = ['NCA1/gen.py', 'NCA5/gen.py', 'SelRange1/gen.py', 'SelRange3/gen.py', f'NCA1/Tab{depth}.lean']
    h = hashlib.sha256()
    for name in files:
        h.update(name.encode()); h.update((root / name).read_bytes())
    return h.hexdigest()


def read_named_table(path, name):
    rows = re.findall(rf'def {name}_r(\d+) : List Nat := \[([^\]]*)\]', path.read_text())
    assert [int(i) for i, _ in rows] == list(range(len(rows))) and rows
    return [[int(v) for v in row.split(',')] if row.strip() else [] for _, row in rows]


def known_chain(source_root, job):
    # This integrated chain has the same complete law key; P and I affect only
    # the new final check. Keep the original mass representation for thinA.
    if job['kind'] == 'direct' or (job['t'], job['r'], Fraction(job['qc'], 2 ** job['nb'])) != \
            (5, 5, Fraction(450359962737050, 2 ** 51)):
        return None
    root = Path(source_root) / 'RebuildBound/Proofs/NCA5'
    steps = []
    for n in range(2, 6):
        width = int(re.search(r'checkConv (\d+)', (root / f'ConvA{n}.lean').read_text())[1])
        steps.append((width, read_named_table(root / f'TabSA{n}.lean', f'sA{n}')))
    width = int(re.search(r'checkThin (\d+)', (root / 'ThinA.lean').read_text())[1])
    return dict(reuse='NCA5A', qc=450359962737050, nb=51, width=width,
                thin=read_named_table(root / 'TabThinA.lean', 'thA'), steps=steps)


def compute_job(args):
    source_root, cache_dir, job = args
    cache = Path(cache_dir) / (job['label'] + '.json') if cache_dir else None
    signature = source_fingerprint(source_root, job['t'])
    reused = known_chain(source_root, job)
    if cache and cache.exists():
        data = json.loads(cache.read_text(), object_hook=fraction_hook)
        if data['signature'] == signature and data['job'] == job:
            if reused:
                assert data['thin'] == reused['thin']
                assert [matrix for _, matrix in data['steps']] == [matrix for _, matrix in reused['steps']]
                data.update(reused)
            return data
    s1, s3 = arithmetic(source_root)
    t, i, p = job['t'], job['i'], job['p']
    table = read_table(source_root, t)
    if job['kind'] == 'direct':
        table = [row + [0] * (H + 1 - len(row)) for row in table]
        final = s1.final(table, t, p, i)
        data = dict(job=job, final=final)
    else:
        if reused:
            qc, nb, thin, width, steps = (reused[k] for k in ['qc', 'nb', 'thin', 'width', 'steps'])
            last = steps[-1][1] if steps else thin
        else:
            qc, nb = s3.reduce_mass(job['qc'], job['nb'])
            thin, width = s3.nca5.thin(table, qc, 2 ** nb)
            last, steps = thin, []
            for _ in range(2, job['r'] + 1):
                last, w = s3.nca5.conv(last, thin)
                steps.append((w, last))
        final = s3.final_parts(s3.nca5.root_marg(last), p, i, job['qc'], 2 ** (job['nb'] + t))
        data = dict(job=job, final=final, thin=thin, width=width, qc=qc, nb=nb, steps=steps)
        if reused:
            data['reuse'] = reused['reuse']
    data['signature'] = signature
    if cache:
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_text(json.dumps(data, default=fraction_json) + '\n')
    return data


def target(value, significant=5):
    # Choose the decimal exponent using integer arithmetic only.
    exponent = len(str(value.numerator)) - len(str(value.denominator))
    if value < (Fraction(10 ** exponent) if exponent >= 0 else Fraction(1, 10 ** -exponent)):
        exponent -= 1
    power = significant - 1 - exponent
    assert power >= 0
    denominator = 10 ** power
    return (value.numerator * denominator + value.denominator - 1) // value.denominator, denominator


def lean_fraction(n, d, typ='ℚ'):
    return f'({n} / {d} : {typ})'


class Emitter:
    def __init__(self, directory, prefix, lanes):
        self.directory = directory
        self.prefix = prefix
        assert prefix.startswith('RebuildBound.Proofs.')
        self.ns = 'RebuildBound.' + prefix.removeprefix('RebuildBound.Proofs.')
        self.lanes = [([], []) for _ in range(lanes)]
        self.files = {}

    def write(self, name, text):
        self.files[self.directory / (name + '.lean')] = text

    def table(self, label, matrix):
        rows = [f'def {label}_r{j} : List Nat := [{", ".join(map(str, row))}]' for j, row in enumerate(matrix)]
        rows.append(f'def {label} : List (List Nat) := [{", ".join(f"{label}_r{j}" for j in range(len(matrix)))}]')
        self.write('Tab' + label, f'namespace {self.ns}.Tab\n\n' + '\n'.join(rows) + f'\n\nend {self.ns}.Tab\n')
        return f'{self.prefix}.Tab{label}', f'Tab.{label}'

    def check(self, lane, name, imports, statement):
        imps, checks = self.lanes[lane]
        imps.extend(x for x in imports if x not in imps)
        checks.append(f'theorem {name} : {statement} = true := by\n  decide +kernel\n')
        return name

    def class_certificate(self, data, tn, td, lane):
        j, fp = data['job'], data['final']
        label, t, i, p = j['label'], j['t'], j['i'], j['p']
        if j['kind'] == 'direct':
            final_name = self.check(lane, 'final_' + label, [f'RebuildBound.Proofs.NCA1.Tab{t}'],
                f'NCA1.checkFinal {fp["wf"]} (2 ^ 320) 100 {fp["rr"]} 32 256 64 (2 ^ {i}) {p} 1 (2 ^ {t}) 32 1 {t} {fp["fuel"]} {tn} {td} {fp["s"]} NCA1.Tab.t{t}')
            return f'SelRange1.range_le {final_name} SelRange1.bnd{t} (by norm_num)'
        steps, convs = [], []
        if data.get('reuse') == 'NCA5A':
            im, tab = 'RebuildBound.Proofs.NCA5.ThinA', 'NCA5.Tab.thA'
            thin_name = 'NCA5.thinA'
            imports, _ = self.lanes[lane]
            imports.extend(x for x in [im] + [f'RebuildBound.Proofs.NCA5.ConvA{n}' for n in range(2, 6)] if x not in imports)
            for step, (w, _) in enumerate(data['steps'], 2):
                steps.append(f'({w}, NCA5.Tab.sA{step})')
                convs.append(f'NCA5.convA{step}')
            previous = 'NCA5.Tab.sA5'
        else:
            im, tab = self.table(label + 'th', data['thin'])
            thin_name = self.check(lane, 'thin_' + label, [f'RebuildBound.Proofs.NCA1.Tab{t}', im],
                f'NCA5.checkThin {data["width"]} {data["qc"]} (2 ^ {data["nb"]}) 64 256 NCA1.Tab.t{t} {tab}')
            previous = tab
            for step, (w, matrix) in enumerate(data['steps'], 2):
                sm, st = self.table(label + f's{step}', matrix)
                convs.append(self.check(lane, f'conv_{label}_{step}', [im, sm],
                    f'NCA5.checkConv {w} (2 ^ 320) 256 {previous} {tab} {st}'))
                steps.append(f'({w}, {st})'); previous = st
        final_name = self.check(lane, 'final_' + label, [im],
            f'NCA1.checkFinal {fp["wf"]} (2 ^ 320) 100 {fp["rr"]} 32 256 64 (2 ^ {i}) {p} {j["qc"]} (2 ^ {j["nb"] + t}) 32 1 0 {fp["fuel"]} {tn} {td} 0 [NCA5.rootMarg 64 {previous}]')
        chain = '⟨' + ', '.join(convs + ['trivial']) + '⟩' if convs else '(by trivial)'
        return (f'SelRange3.class_bound RebuildBound.P10r (r := {j["r"]}) (t := {t}) (P := {p}) (i := {i}) '
                f'(nb := {j["nb"]}) (qc := {j["qc"]}) (qcT := {data["qc"]}) (nbT := {data["nb"]})\n'
                f'    (steps := [{", ".join(steps)}]) q hq SelRange1.bnd{t} rfl\n'
                f'    (by norm_num) (by norm_num) (by norm_num) rfl (by norm_num) {thin_name} {chain} {final_name}')

    def emit_lanes(self):
        for j, (imports, checks) in enumerate(self.lanes):
            self.write(f'Lane{j}', 'import RebuildBound.Proofs.NCA5.Checker\n' + ''.join(f'import {x}\n' for x in imports) +
                f'\nset_option Elab.async false\n\nnamespace {self.ns}\n\n' + '\n'.join(checks) + f'\nend {self.ns}\n')


def inventory_jobs(inventory, spec):
    rows = []
    for row in parse_rows(spec):
        matches = [g for g in inventory['shapes']['sep'] if (g['level'], g['digit']) == row[:2]]
        if len(matches) != 1:
            raise ValueError(f'Expected exactly one inventory geometry for {row[:2]}')
        rows.append(row_job(row, matches[0]))
    prep = inventory['shapes']['prep']
    init = inventory['shapes']['init']
    assert all(prep[k] == init[k] for k in ['C', 'k', 'stash_pages', 'a_tier_pages', 'range_bits', 'I', 'dfs'])
    tp = dict(tag='TP', label='TP', kind='half', t=prep['k'] - 1 - prep['I'], r=1, nb=1, qc=1,
              i=prep['I'] + 1, p=prep['C'] * (prep['a_tier_pages'] + prep['I'] * prep['stash_pages']))
    return rows, tp


def validate_output(output_dir, module_prefix, source_root):
    output_dir = output_dir.resolve()
    if output_dir.name != module_prefix.rsplit('.', 1)[-1]:
        raise ValueError('Output directory name must match the module prefix')
    own = Path(__file__).resolve().parent
    entrypoint = (output_dir.parent / (output_dir.name + '.lean')).resolve()
    for root in {Path(source_root).resolve(), own.parents[2]}:
        proofs = root / 'RebuildBound/Proofs'
        for path in proofs.iterdir():
            if path == own or path == own.with_suffix('.lean'):
                continue
            if path.is_dir() and (output_dir.is_relative_to(path) or path.is_relative_to(output_dir)):
                raise ValueError(f'Output overlaps protected proof sources: {path}')
            if path.is_file() and entrypoint == path:
                raise ValueError(f'Entrypoint overlaps protected proof source: {path}')
    return output_dir


def generate(args):
    args.output_dir = validate_output(args.output_dir, args.module_prefix, args.source_root)
    inventory = json.loads(args.inventory.read_text())
    rows, tp = inventory_jobs(inventory, args.spec.read_text())
    prep = inventory['shapes']['prep']
    jobs = [job for row in rows for job in class_jobs(row)] + [tp]
    assert all(job['r'] * (2 ** job['t'] - 1) + 1 <= 4000 for job in jobs)
    inputs = [(str(args.source_root), str(args.cache_dir) if args.cache_dir else None, job) for job in jobs]
    if args.jobs == 1:
        results = list(map(compute_job, inputs))
    else:
        with mp.Pool(min(args.jobs, len(inputs))) as pool:
            results = pool.map(compute_job, inputs)
    by_label = {data['job']['label']: data for data in results}
    emitter = Emitter(args.output_dir, args.module_prefix, args.lanes)
    proof = []
    lane_counter = 0
    for row in rows:
        labels = [j['label'] for j in class_jobs(row)]
        values = [by_label[label]['final']['total'] for label in labels]
        tn, td = target(max(values))
        if row['kind'] == 'direct':
            fp = by_label[labels[0]]['final']; tn, td = fp['tn'], fp['td']
        certificates = []
        for label in labels:
            data = by_label[label]
            assert data['final']['total'] <= Fraction(tn, td)
            body = emitter.class_certificate(data, tn, td, lane_counter % args.lanes); lane_counter += 1
            if row['kind'] == 'direct':
                proof.append(f'theorem range_{label} : stopLoss (rangeLaw 64 32 {row["p"]} (halfPow {row["t"]}) (2 ^ {row["i"]}) {row["t"]}) 64 ≤ ({tn} : ℝ≥0∞) / ({td} : ℕ) :=\n  {body}\n')
                certificates.append('range_' + label)
            else:
                mass = by_label[label]['job']['qc']
                proof.append(f'theorem class_{label} (q : unitInterval) (hq : (q : ℝ) = (({mass} : ℕ) : ℝ) / ((2 ^ {row["nb"]} : ℕ) : ℝ)) :\n'
                    f'    stopLoss (rangeLawR 64 32 {row["p"]} (2 ^ {row["i"]}) {row["t"]} {row["r"]} q) 64 ≤\n'
                    f'      ({tn} : ℝ≥0∞) / ({td} : ℕ) + (2 ^ {row["i"]} : ℝ≥0∞) / 10 ^ 46 :=\n  {body}\n')
                certificates.append('class_' + label)
        two_m, delta = 2 ** row['m'], row['num'] - 2 ** row['m']
        assert 0 <= delta and row['n'] * delta < two_m
        if row['kind'] == 'direct':
            value = Fraction(two_m, two_m-row['n']*delta) * 2 ** row['t'] * Fraction(tn, td)
            call = ('SelRange1.selRange_le', f'(t := {row["t"]}) (i := {row["i"]}) (P := {row["p"]})',
                    ' '.join(['rfl'] * 8) + ' ' + certificates[0])
        else:
            value = Fraction(two_m, two_m-row['n']*delta) * 2 ** row['t'] * row['r'] * (Fraction(tn, td) + Fraction(2 ** row['i'], 10 ** EPS_EXP))
            call = ('SelRange3.selRange_le', f'(r := {row["r"]}) (t := {row["t"]}) (i := {row["i"]}) (P := {row["p"]}) '
                    f'(nb := {row["nb"]}) (qcA := {2 ** row["nb"] // row["r"] + 1}) (qcB := {2 ** row["nb"] // row["r"]})',
                    ' '.join(['rfl'] * 11) + ' ' + ' '.join(certificates))
        assert value <= Fraction(row['bn'], row['bd']), (row['tag'], float(value))
        print(f'{row["tag"]}: bound {float(value):.12e}, log2 {math.log2(float(value)):.8f}; target {tn}/{td}', flush=True)
        proof.append(f'theorem row_{row["tag"]} : selRange {row["geom"]} ≤ ENNReal.ofReal ({lean_fraction(row["bn"], row["bd"])} : ℝ) :=\n'
                     f'  {call[0]} {row["geom"]}\n    {call[1]}\n'
                     f'    (n := {row["n"]}) (m := {row["m"]}) (num := {row["num"]}) (tn := {tn}) (td := {td}) (bn := {row["bn"]}) (bd := {row["bd"]})\n'
                     f'    {call[2]} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n')
    data = by_label['TP']; tn, td = target(data['final']['total'])
    tp_body = emitter.class_certificate(data, tn, td, lane_counter % args.lanes)
    tp_value = 2 ** prep['range_bits'] * (Fraction(tn, td) + Fraction(2 ** tp['i'], 10 ** EPS_EXP))
    assert tp_value <= Fraction(1, 2 ** 101)
    print(f'TP: bound {float(tp_value):.12e}, log2 {math.log2(float(tp_value)):.8f}; target {tn}/{td}', flush=True)
    proof.append(f'theorem tp_class (q : unitInterval) (hq : (q : ℝ) = ((1 : ℕ) : ℝ) / ((2 ^ 1 : ℕ) : ℝ)) :\n'
                 f'    stopLoss (rangeLawR 64 32 {tp["p"]} (2 ^ {tp["i"]}) {tp["t"]} 1 q) 64 ≤\n'
                 f'      ({tn} : ℝ≥0∞) / ({td} : ℕ) + (2 ^ {tp["i"]} : ℝ≥0∞) / 10 ^ 46 :=\n  {tp_body}\n')
    emitter.emit_lanes()
    imports = ['RebuildBound.Spec.Numerics31Pilot', 'RebuildBound.Proofs.SelRange3.Glue'] + [f'{args.module_prefix}.Lane{j}' for j in range(args.lanes)]
    body = ''.join(f'import {x}\n' for x in imports) + '\nopen RebuildBound.Spec RebuildBound.Model\nopen scoped ENNReal\n\n'
    body += ('/-! Numerical range pilots for the frozen capacity-2^31 geometry.\n'
             'Four ordinary range terms and the shared preparation/initialization range\n'
             'term only; other numerical obligations and the hierarchy endpoint remain open.\n'
             'Existing certified trees through Tab9 and the identical NCA5 A chain are reused.\n'
             'Regenerate with `python3 -B RebuildBound/Proofs/Numerics31Range/gen.py`;\n'
             'the optional cache is untrusted input to the same kernel checks.\n'
             f'{args.lanes} sequential lanes contain {sum(len(checks) for _, checks in emitter.lanes)} new arithmetic checks. -/\n\n')
    body += f'namespace {emitter.ns}\n\n' + '\n'.join(proof) + f'\nend {emitter.ns}\n\n'
    body += ('theorem RebuildBound.Numerics31Range : RebuildBound.Spec.Numerics31Range_statement := by\n'
             '  unfold Numerics31Range_statement\n  intro p hp\n'
             '  simp only [pilotRangeBudgets31, List.mem_cons, List.not_mem_nil, or_false] at hp\n'
             '  rcases hp with ' + ' | '.join(['rfl'] * len(rows)) + '\n' +
             '\n'.join(f'  · exact {emitter.ns}.row_{row["tag"]}' for row in rows) + '\n\n')
    body += ('theorem RebuildBound.TPRange31 : RebuildBound.Spec.TPRange31_statement := by\n'
             '  unfold TPRange31_statement tpRangeTerm\n'
             f'  change (2 : ℝ≥0∞) ^ {prep["range_bits"]} * stopLoss (rangeLawR 64 32 {tp["p"]} (2 ^ {tp["i"]}) {tp["t"]} 1 half) 64 ≤ _\n'
             f'  have h := {emitter.ns}.tp_class half (by norm_num [half])\n'
             f'  calc _ ≤ (2 : ℝ≥0∞) ^ {prep["range_bits"]} * (({tn} : ℝ≥0∞) / ({td} : ℕ) + (2 ^ {tp["i"]} : ℝ≥0∞) / 10 ^ 46) := by gcongr\n'
             '       _ ≤ _ := by\n'
             f'         have h1 : ({tn} : ℝ≥0∞) / ({td} : ℕ) = ENNReal.ofReal (({tn} : ℝ) / {td}) := by\n'
             '           rw [ENNReal.ofReal_div_of_pos (by positivity)]; norm_num\n'
             f'         have h2 : (2 ^ {tp["i"]} : ℝ≥0∞) / 10 ^ 46 = ENNReal.ofReal ((2 ^ {tp["i"]} : ℝ) / 10 ^ 46) := by\n'
             '           rw [ENNReal.ofReal_div_of_pos (by positivity)]; norm_num\n'
             f'         have hpow : (2 : ℝ≥0∞) ^ {prep["range_bits"]} = ENNReal.ofReal ((2 : ℝ) ^ {prep["range_bits"]}) := by norm_num\n'
             '         rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity), hpow,\n'
             '           ← ENNReal.ofReal_mul (by positivity)]\n'
             '         exact ENNReal.ofReal_le_ofReal (by norm_num)\n')
    emitter.files[args.output_dir.parent / (args.output_dir.name + '.lean')] = body
    if not args.dry:
        for path, content in emitter.files.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            content = '/- Generated by Numerics31Range/gen.py; do not edit. -/\n' + content
            if not path.exists() or path.read_text() != content:
                path.write_text(content)


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=here.parents[2])
    parser.add_argument('--inventory', type=Path)
    parser.add_argument('--spec', type=Path)
    parser.add_argument('--output-dir', type=Path, default=here)
    parser.add_argument('--module-prefix', default='RebuildBound.Proofs.Numerics31Range')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--lanes', type=int, default=2)
    parser.add_argument('--cache-dir', type=Path)
    parser.add_argument('--dry', action='store_true')
    args = parser.parse_args()
    args.source_root = args.source_root.resolve()
    args.inventory = args.inventory or args.source_root.parent / 'analysis/bound_certification/code/lean_configuration_2p31.json'
    args.spec = args.spec or args.source_root / 'RebuildBound/Spec/Numerics31Pilot.lean'
    assert args.jobs > 0 and 0 < args.lanes <= 4
    generate(args)


if __name__ == '__main__':
    main()
