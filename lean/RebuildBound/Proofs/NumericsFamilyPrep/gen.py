#!/usr/bin/env python3
"""Shared preparation/initialization ranges and exact complete-shape budgets."""
import argparse
import hashlib
import importlib.util
import json
import multiprocessing as mp
import sys
from fractions import Fraction
from pathlib import Path

sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
PREFIX='RebuildBound.Proofs.NumericsFamilyPrep';NS='RebuildBound.NumericsFamilyPrep'
spec=importlib.util.spec_from_file_location('family_ranges',HERE.parent/'NumericsFamilyRange/gen.py')
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
pilot=f.pilot


def compute(job):
    return pilot.compute_job((str(ROOT),str(ROOT/'.lake/family-prep-cache'),job))


def generate(args):
    manifest=json.loads((ROOT.parent/'analysis/bound_certification/code/configuration_family.json').read_text())
    table={e['key_id']:e for e in json.loads((ROOT.parent/'analysis/bound_certification/code/bound_table.json').read_text())['entries']}
    jobs={};geoms={}
    for kid,entry in manifest['jobs'].items():
        k=entry['key'];role=k['role']
        if role not in ('top_prepare','initialization'):continue
        K,I=k['block_bits'],k['index_bits'];stash=k['stash_buckets'];tier=k['tier_buckets']
        drain=stash if role=='top_prepare' else tier
        geom=(64,K,stash,tier,drain,k['range_bits'],I,'true')
        c=table[kid]['case'];rest=sum(Fraction(c[n]['probability_upper_decimal']) for n in ('stages','packing'))
        re=f.dyadic(rest)
        # The existing 2^31 cutoff-576 fixed-point certificate is weaker than
        # the Python ledger at this shape. Reuse its checked remainder target.
        if geom == (64,26,4,3,4,10,16,'true'):
            re=min(re,107)
        if geom in geoms:re=min(re,geoms[geom]['rest'])
        geoms[geom]=dict(rest=re,label='TP'+str(K))
        jobs.setdefault(K,dict(tag='TP'+str(K),label='TP'+str(K),kind='half',t=K-1-I,r=1,nb=1,qc=1,i=I+1,p=64*(tier+I*stash)))
    jobs=[jobs[K] for K in sorted(jobs) if K != 26]
    # The largest range term already has exactly the required 2^-101 bound.
    reused_ranges = {'TP26': 101}
    print(len(geoms),'complete TP shapes,',len(jobs),'range laws',flush=True)
    with mp.Pool(args.jobs) as pool:results=list(pool.imap(compute,jobs))
    emitter=f.ordinary.emitter_class(pilot)(HERE,PREFIX,args.lanes);fresh={}
    for d in results:
        key=f.chain_key(d['job']);reuse=f.known_key(key)
        if reuse is None:
            if key not in fresh:fresh[key]=f.emit_chain(emitter,len(fresh),d)
            reuse=fresh[key]
        d.update(reuse)
    proofs=[];exponents=dict(reused_ranges)
    for index,d in enumerate(results):
        j=d['job'];tn,td=pilot.target(d['final']['total']);rho=j['t']+1
        e=f.dyadic(2**rho*(Fraction(tn,td)+Fraction(2**j['i'],10**46)));exponents[j['label']]=e
        body=emitter.class_certificate(d,tn,td,index%args.lanes)
        proofs.append(f'theorem class_{j["label"]} (q : unitInterval) (hq : (q : ℝ) = ((1 : ℕ) : ℝ) / ((2 ^ 1 : ℕ) : ℝ)) :\n'
            f'    stopLoss (rangeLawR 64 32 {j["p"]} (2 ^ {j["i"]}) {j["t"]} 1 q) 64 ≤\n'
            f'      ({tn} : ℝ≥0∞) / ({td} : ℕ) + (2 ^ {j["i"]} : ℝ≥0∞) / 10 ^ 46 :=\n  {body}\n')
        proofs.append(f'theorem range_{j["label"]} : (2 : ℝ≥0∞) ^ {rho} * stopLoss (rangeLawR 64 32 {j["p"]} (2 ^ {j["i"]}) {j["t"]} 1 half) 64 ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ {e}) := by\n'
            f'  have h := class_{j["label"]} half (by norm_num [half])\n'
            f'  calc _ ≤ (2 : ℝ≥0∞) ^ {rho} * (({tn} : ℝ≥0∞) / ({td} : ℕ) + (2 ^ {j["i"]} : ℝ≥0∞) / 10 ^ 46) := by gcongr\n'
            '       _ ≤ _ := by\n'
            f'         have h1 : ({tn} : ℝ≥0∞) / ({td} : ℕ) = ENNReal.ofReal (({tn} : ℝ) / {td}) := by\n'
            '           rw [ENNReal.ofReal_div_of_pos (by positivity)]; norm_num\n'
            f'         have h2 : (2 ^ {j["i"]} : ℝ≥0∞) / 10 ^ 46 = ENNReal.ofReal ((2 ^ {j["i"]} : ℝ) / 10 ^ 46) := by\n'
            '           rw [ENNReal.ofReal_div_of_pos (by positivity)]; norm_num\n'
            f'         have hpow : (2 : ℝ≥0∞) ^ {rho} = ENNReal.ofReal ((2 : ℝ) ^ {rho}) := by norm_num\n'
            '         rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity), hpow,\n'
            '           ← ENNReal.ofReal_mul (by positivity)]\n'
            '         exact ENNReal.ofReal_le_ofReal (by norm_num)\n')
    emitter.emit_lanes();items=sorted(geoms.items(),key=lambda p:(p[0][1],p[0][4]));rows=[]
    for geom,g in items:
        rows.append('  (⟨'+', '.join(map(str,geom))+'⟩, '+str(exponents[g['label']])+', '+str(g['rest'])+')')
    emitter.files[ROOT/'RebuildBound/Spec/ConfigurationFamilyPrep.lean']='''import RebuildBound.Spec.TopPrepG

/-! Full preparation/initialization shapes with shared range and remainder
budgets. Distinct drain capacities remain distinct certificate rows. -/

namespace RebuildBound.Spec.ConfigurationFamily
open Model

def prepBudgets : List (TPGeom × Nat × Nat) := [
'''+',\n'.join(rows)+''']

end RebuildBound.Spec.ConfigurationFamily

namespace RebuildBound.Spec
open Model ConfigurationFamily

def ConfigurationFamilyPrepRange_statement : Prop :=
  ∀ x ∈ prepBudgets, tpRangeTerm x.1 32 ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ x.2.1)

def ConfigurationFamilyPrepNumerics_statement : Prop :=
  ∀ x ∈ prepBudgets, tpBound x.1 32 1 576 576 ≤
    ENNReal.ofReal (1 / (2 : ℝ) ^ x.2.1 + 1 / (2 : ℝ) ^ x.2.2)

end RebuildBound.Spec
'''
    imports=['RebuildBound.Spec.ConfigurationFamilyPrep','RebuildBound.Proofs.SelRange3.Glue','RebuildBound.Proofs.Numerics31Range']+[f'{PREFIX}.Lane{i}' for i in range(args.lanes)]
    body=''.join(f'import {i}\n' for i in imports)+'\nopen RebuildBound.Spec RebuildBound.Model\nopen scoped ENNReal\n\n'
    body+=f'namespace {NS}\n\n'+'\n'.join(proofs)+f'\nend {NS}\n\n'
    body+='theorem RebuildBound.ConfigurationFamilyPrepRange : RebuildBound.Spec.ConfigurationFamilyPrepRange_statement := by\n  intro x hx\n  simp only [Spec.ConfigurationFamily.prepBudgets, List.mem_cons, List.not_mem_nil, or_false] at hx\n  rcases hx with '+' | '.join(['rfl']*len(items))+'\n'
    body+='\n'.join('  · exact RebuildBound.TPRange31' if g['label'] in reused_ranges else f'  · exact {NS}.range_{g["label"]}' for _,g in items)+'\n'
    emitter.files[HERE.with_suffix('.lean')]=body
    for path,text in emitter.files.items():
        text = '/- Generated by NumericsFamilyPrep/gen.py; do not edit. -/\n' + text
        path.parent.mkdir(parents=True,exist_ok=True)
        if not path.exists() or path.read_text()!=text:path.write_text(text)
    (HERE/'registry.json').write_text(json.dumps(dict(format='family-prep-registry/1',
        checker=dict(version=1,scale=320,cutoff=256,capacity=64,load=32,tail_exponent=46),
        generated_files=[str(p.relative_to(ROOT)) for p in sorted(emitter.files)],
        generated_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(emitter.files)},
        shapes=[dict(geometry=list(geom),range_exponent=exponents[g['label']],rest_exponent=g['rest']) for geom,g in items],
        reused_whole_ranges=reused_ranges,new_half_chains=len(fresh)),indent=2)+'\n')
    print('new shared half chains',len(fresh),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--jobs',type=int,default=8);p.add_argument('--lanes',type=int,default=4)
    generate(p.parse_args())
