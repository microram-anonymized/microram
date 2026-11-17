#!/usr/bin/env python3
"""Generate one checked range bound per exact family separated shape.

All existing exact-mass chains are reused. New chains are emitted once in
independent modules; final population/root/tail checks remain shape-specific.
Python arithmetic is untrusted input to the existing NCA1/NCA5 kernel checks.
"""
import argparse
import hashlib
import importlib.util
import json
import multiprocessing as mp
import re
import sys
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'RebuildBound.Proofs.NumericsFamilyRange'
NS = 'RebuildBound.NumericsFamilyRange'
spec = importlib.util.spec_from_file_location('family_ordinary', HERE.parent/'Numerics31OrdRange/gen.py')
ordinary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ordinary)
pilot = ordinary.helper(ROOT)


def chain_key(job):
    return (job['t'], job['r'], Fraction(job['qc'], 2 ** job['nb']))


@lru_cache(None)
def known_key(key):
    return ordinary.loaded_chain(str(ROOT), key, include_all=True)


@lru_cache(None)
def computed_chain(key):
    """Reuse untrusted chain integers from our own checked-output format.

    Unlike an imported proof adapter, this returns only data; the newly emitted
    modules check the chain again, so output renaming cannot create import cycles.
    The parsed signature fixes the checker scale, capacity and cutoff explicitly.
    """
    depth, radix, mass = key
    for directory in [HERE, HERE.parent/'NumericsFamilyDirectRange', HERE.parent/'NumericsFamilyPrep']:
        for path in sorted(directory.glob('C*.lean')):
            source=path.read_text()
            match=re.search(r'checkThin (\d+) (\d+) \(2 \^ (\d+)\) 64 256 NCA1.Tab.t(\d+) (\S+) = true',source)
            if not match:continue
            width,qc,nb,t=map(int,match.groups()[:4]);thin_name=match[5]
            if t!=depth or Fraction(qc,2**nb)!=mass:continue
            convs=re.findall(r'checkConv (\d+) \(2 \^ 320\) 256 (\S+) (\S+) (\S+) = true',source)
            previous=thin_name;steps=[]
            for w,left,right,out in convs:
                if left!=previous or right!=thin_name:break
                local=out.rsplit('.',1)[1]
                steps.append((int(w),pilot.read_named_table(directory/('Tab'+local+'.lean'),local)))
                previous=out
            if len(steps)!=radix-1:continue
            local=thin_name.rsplit('.',1)[1]
            return dict(reuse='computed-chain',qc=qc,nb=nb,width=width,
                        thin=pilot.read_named_table(directory/('Tab'+local+'.lean'),local),steps=steps)
    return None


def known(source_root, job):
    if job['kind']=='direct':return None
    key=chain_key(job)
    return known_key(key) or computed_chain(key)


pilot.known_chain = known


def compute(job):
    cache = ROOT/'.lake/family-range-cache'
    path = cache/(job['label']+'.json')
    # Upgrade an old cosmetic label only after comparing every semantic field.
    # Colliding old labels cannot supply the other geometry's final check.
    oldtag = f'L{job["level"]}D{job["digit"]}'
    oldlabel = oldtag + job['label'][len(job['tag']):]
    oldpath = cache/(oldlabel+'.json')
    oldjob = dict(job,tag=oldtag,label=oldlabel)
    if not path.exists() and oldpath.exists():
        data = json.loads(oldpath.read_text(),object_hook=pilot.fraction_hook)
        if data['job'] == oldjob and data['signature'] == pilot.source_fingerprint(ROOT,job['t']):
            data['job'] = job
            path.write_text(json.dumps(data,default=pilot.fraction_json)+'\n')
    return pilot.compute_job((str(ROOT),str(cache),job))


def dyadic(value):
    assert value > 0
    e = value.denominator.bit_length() - value.numerator.bit_length()
    if value > Fraction(1, 2 ** e):
        e -= 1
    return e


def rows_of(manifest):
    rows = []
    for key_id, entry in manifest['jobs'].items():
        k = entry['key']
        if k['role'] != 'separated_ordinary' and not (k['role'] == 'dense_level_one' and k['carry_bits'] == 2 and k['digit'] >= 3):
            continue
        g = dict(C=64, K=k['carry_bits'], e=k['block_bits']-k['carry_bits'],
                 r=k['radix'], I=k['index_bits'], range_bits=k['range_bits'],
                 a_tier_pages=k['older_tier_buckets'], stash_pages=k['stash_buckets'],
                 b_tier_pages=k['carry_tier_buckets'], tier_pages=k['tier_buckets'])
        row = pilot.row_job((g['K'], k['digit'], 1, 1), g)
        vals = [g[n] for n in ['C','K','e','r','range_bits','I','stash_pages',
                               'a_tier_pages','b_tier_pages','tier_pages']]
        row['geom'] = '(⟨' + ', '.join(map(str, vals)) + '⟩ : SepGeom)'
        row['key_id'] = key_id
        row['tag'] = (f'K{g["K"]}D{k["digit"]}I{g["I"]}R{g["range_bits"]}'
                      f'S{g["stash_pages"]}A{g["a_tier_pages"]}B{g["b_tier_pages"]}T{g["tier_pages"]}')
        rows.append(row)
    rows.sort(key=lambda r: (r['level'],r['digit'],r['geom']))
    assert len({r['tag'] for r in rows}) == len(rows)
    assert len({r['geom'] for r in rows}) == len(rows)
    return rows


def emit_chain(emitter, number, data):
    """Independent chain module, shared without lane-to-lane dependencies."""
    label = f'C{number}'
    j = data['job']; ns = emitter.ns; namespace = f'{ns}.{label}'
    imports = ['RebuildBound.Proofs.NCA5.Checker',f'RebuildBound.Proofs.NCA1.Tab{j["t"]}']
    tm, tab = emitter.table(label+'th', data['thin']);imports.append(tm)
    fulltab = ns + '.' + tab
    proofs = [f'theorem thin : NCA5.checkThin {data["width"]} {data["qc"]} (2 ^ {data["nb"]}) 64 256 NCA1.Tab.t{j["t"]} {fulltab} = true := by\n  decide +kernel\n']
    previous = fulltab; tables=[]; convs=[]
    for n, (width, matrix) in enumerate(data['steps'], 2):
        tm, table = emitter.table(label+f's{n}', matrix);imports.append(tm)
        table = ns + '.' + table
        proofs.append(f'theorem conv{n} : NCA5.checkConv {width} (2 ^ 320) 256 {previous} {fulltab} {table} = true := by\n  decide +kernel\n')
        tables.append(table);convs.append(namespace+f'.conv{n}');previous=table
    emitter.write(label, ''.join(f'import {i}\n' for i in imports)+
        f'\nset_option Elab.async false\nnamespace {namespace}\n\n'+
        '\n'.join(proofs)+f'\nend {namespace}\n')
    return dict(reuse='integrated', qc=data['qc'],nb=data['nb'],width=data['width'],
                thin=data['thin'],steps=data['steps'],thin_table=fulltab,
                thin_proof=namespace+'.thin',step_tables=tables,conv_proofs=convs,
                imports=[emitter.prefix+'.'+label])


def reused_rows(rows):
    registry = HERE/'registry.json'
    if not registry.exists():
        return {}
    targets = {r['geometry']:r['exponent'] for r in json.loads(registry.read_text())['shapes']}
    inv = json.loads((ROOT.parent/'analysis/bound_certification/code/lean_configuration_2p31.json').read_text())
    old = ordinary.all_rows(inv,(ROOT/'RebuildBound/Spec/Numerics31Pilot.lean').read_text(),
                            (ROOT/'RebuildBound/Spec/Numerics31Ordinary.lean').read_text(),pilot)
    result = {}
    for row in old:
        g = next(g for g in inv['shapes']['sep'] if (g['level'],g['digit']) == (row['level'],row['digit']))
        vals = [g[n] for n in ['C','K','e','r','range_bits','I','stash_pages','a_tier_pages','b_tier_pages','tier_pages']]
        geom = '(⟨' + ', '.join(map(str,vals)) + '⟩ : SepGeom)'
        e = targets.get(geom)
        if e is not None and Fraction(row['bn'],row['bd']) <= Fraction(1,2**e):
            result[geom] = dict(exponent=e,proof='RebuildBound.Numerics31OrdRange.row_'+row['tag'],
                               old_geom=row['geom'])
    return result


def generate(args):
    manifest = json.loads((ROOT.parent/'analysis/bound_certification/code/configuration_family.json').read_text())
    direct_only = getattr(args, 'direct_only', False)
    role = 'dense_level_one' if direct_only else 'separated_ordinary'
    manifest['jobs'] = {k: v for k, v in manifest['jobs'].items() if v['key']['role'] == role}
    directory = HERE.parent/'NumericsFamilyDirectRange' if direct_only else HERE
    prefix = 'RebuildBound.Proofs.NumericsFamilyDirectRange' if direct_only else PREFIX
    namespace = 'RebuildBound.NumericsFamilyDirectRange' if direct_only else NS
    rows=rows_of(manifest)
    reused = {} if direct_only else reused_rows(rows)
    jobs=[j for r in rows if r['geom'] not in reused for j in pilot.class_jobs(r)]
    print(f'{len(rows)} exact shapes; {len(jobs)} final-law checks',flush=True)
    with mp.Pool(args.jobs) as pool:
        results=list(pool.imap(compute,jobs))
    data={d['job']['label']:d for d in results}
    emitter=ordinary.emitter_class(pilot)(directory,prefix,args.lanes)
    fresh={};chain_count=0
    for d in results:
        if d['job']['kind']=='direct':continue
        key=chain_key(d['job']);reuse=known_key(key)
        if reuse is None:
            if key not in fresh:
                fresh[key]=emit_chain(emitter,chain_count,d);chain_count+=1
            reuse=fresh[key]
        d.update(reuse)
    proofs=[];counter=0
    for row in rows:
        if row['geom'] in reused:
            reuse = reused[row['geom']];row['exponent'] = e = reuse['exponent']
            proofs.append(f'theorem row_{row["tag"]} : selRange {row["geom"]} ≤ ENNReal.ofReal ((1 / {2**e} : ℚ) : ℝ) := by\n'
                f'  have hg : {row["geom"]} = {reuse["old_geom"]} := by decide +kernel\n'
                f'  rw [hg]\n  exact {reuse["proof"]}.trans (ENNReal.ofReal_le_ofReal (by norm_num))\n')
            continue
        labels=[j['label'] for j in pilot.class_jobs(row)]
        tn,td=pilot.target(max(data[l]['final']['total'] for l in labels))
        if row['kind']=='direct':
            tn,td=data[labels[0]]['final']['tn'],data[labels[0]]['final']['td']
        certificates=[]
        for label in labels:
            d=data[label];body=emitter.class_certificate(d,tn,td,counter%args.lanes);counter+=1
            if row['kind']=='direct':
                proofs.append(f'theorem range_{label} : stopLoss (rangeLaw 64 32 {row["p"]} (halfPow {row["t"]}) (2 ^ {row["i"]}) {row["t"]}) 64 ≤ ({tn} : ℝ≥0∞) / ({td} : ℕ) :=\n  {body}\n')
                certificates.append('range_'+label)
            else:
                proofs.append(f'theorem class_{label} (q : unitInterval) (hq : (q : ℝ) = (({d["job"]["qc"]} : ℕ) : ℝ) / ((2 ^ {row["nb"]} : ℕ) : ℝ)) :\n'
                    f'    stopLoss (rangeLawR 64 32 {row["p"]} (2 ^ {row["i"]}) {row["t"]} {row["r"]} q) 64 ≤\n'
                    f'      ({tn} : ℝ≥0∞) / ({td} : ℕ) + (2 ^ {row["i"]} : ℝ≥0∞) / 10 ^ 46 :=\n  {body}\n')
                certificates.append('class_'+label)
        twom=2**row['m'];delta=row['num']-twom
        assert 0<=delta and row['n']*delta<twom
        if row['kind']=='direct':
            value=Fraction(twom,twom-row['n']*delta)*2**row['t']*Fraction(tn,td)
            name,params,premises=('SelRange1.selRange_le',f'(t := {row["t"]}) (i := {row["i"]}) (P := {row["p"]})',' '.join(['rfl']*8))
        else:
            value=Fraction(twom,twom-row['n']*delta)*2**row['t']*row['r']*(Fraction(tn,td)+Fraction(2**row['i'],10**46))
            name,params,premises=('SelRange3.selRange_le',f'(r := {row["r"]}) (t := {row["t"]}) (i := {row["i"]}) (P := {row["p"]}) (nb := {row["nb"]}) (qcA := {2**row["nb"]//row["r"]+1}) (qcB := {2**row["nb"]//row["r"]})',' '.join(['rfl']*11))
        row['exponent']=e=dyadic(value);bd=2**e
        proofs.append(f'theorem row_{row["tag"]} : selRange {row["geom"]} ≤ ENNReal.ofReal ((1 / {bd} : ℚ) : ℝ) :=\n'
            f'  {name} {row["geom"]}\n    {params}\n'
            f'    (n := {row["n"]}) (m := {row["m"]}) (num := {row["num"]}) (tn := {tn}) (td := {td}) (bn := 1) (bd := {bd})\n'
            f'    {premises} {" ".join(certificates)} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n')
        print(row['tag'],e,flush=True)
    emitter.emit_lanes()
    spec_text='''import RebuildBound.Spec.Selected

/-! Shared range budgets, indexed by full separated shape. Generated by
`Proofs/NumericsFamilyRange/gen.py`; each row is checked by the existing
NCA1/NCA5 arithmetic soundness theorems. -/

namespace RebuildBound.Spec.ConfigurationFamily
open Model

def rangeBudgets : List (SepGeom × Nat) := [
'''+',\n'.join(f'  ({r["geom"]}, {r["exponent"]})' for r in rows)+''']

end RebuildBound.Spec.ConfigurationFamily

namespace RebuildBound.Spec
open Model ConfigurationFamily

def ConfigurationFamilyRangeNumerics_statement : Prop :=
  ∀ x ∈ rangeBudgets, selRange x.1 ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ x.2)

end RebuildBound.Spec
'''
    emitter.files[ROOT/'RebuildBound/Spec/ConfigurationFamilyRange.lean']=spec_text
    imports=['RebuildBound.Spec.ConfigurationFamilyRange','RebuildBound.Proofs.SelRange3.Glue']+[f'{prefix}.Lane{i}' for i in range(args.lanes)]
    if reused:imports.append('RebuildBound.Proofs.Numerics31OrdRange')
    body=''.join(f'import {i}\n' for i in imports)+'\nopen RebuildBound.Spec RebuildBound.Model\nopen scoped ENNReal\n\n'
    body+='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 500\n\n'
    body+=f'namespace {namespace}\n\n'+'\n'.join(proofs)+f'\nend {namespace}\n\n'
    body+='set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ntheorem RebuildBound.ConfigurationFamilyRangeNumerics : RebuildBound.Spec.ConfigurationFamilyRangeNumerics_statement := by\n  intro x hx\n  simp only [Spec.ConfigurationFamily.rangeBudgets, List.mem_cons, List.not_mem_nil, or_false] at hx\n  rcases hx with '+' | '.join(['rfl']*len(rows))+'\n'
    body+='\n'.join(f'  · have h := {namespace}.row_{r["tag"]}\n    norm_num at h ⊢\n    exact h' for r in rows)+'\n'
    emitter.files[directory.with_suffix('.lean')]=body
    if direct_only:
        old_spec = ROOT/'RebuildBound/Spec/ConfigurationFamilyRange.lean'
        new_spec = ROOT/'RebuildBound/Spec/ConfigurationFamilyDirectRange.lean'
        emitter.files[new_spec] = emitter.files.pop(old_spec)
        emitter.files = {path: text.replace('ConfigurationFamilyRange', 'ConfigurationFamilyDirectRange').replace('rangeBudgets', 'directRangeBudgets') for path, text in emitter.files.items()}
    for path,text in emitter.files.items():
        text = '/- Generated by NumericsFamilyRange/gen.py; do not edit. -/\n' + text
        path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists() and path.is_symlink():raise ValueError('Refusing output symlink')
        if not path.exists() or path.read_text()!=text:path.write_text(text)
    report=dict(format='family-range-registry/1',checker=dict(version=1,scale=320,cutoff=256,capacity=64,load=32,tail_exponent=46),
                shapes=[dict(key_id=r['key_id'],geometry=r['geom'],exponent=r['exponent']) for r in rows],
                generated_files=[str(p.relative_to(ROOT)) for p in sorted(emitter.files)],
                generated_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(emitter.files)},
                reused_whole_rows=len(reused),new_chains=chain_count,reused_chains=len(set(chain_key(d['job']) for d in results if d['job']['kind']!='direct'))-chain_count)
    (directory/'registry.json').write_text(json.dumps(report,indent=2)+'\n')
    print('new chains',chain_count,'checks',sum(len(c) for _,c in emitter.lanes),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--jobs',type=int,default=8);p.add_argument('--lanes',type=int,default=8);p.add_argument('--direct-only',action='store_true')
    generate(p.parse_args())
