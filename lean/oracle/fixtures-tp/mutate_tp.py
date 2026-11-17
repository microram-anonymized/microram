#!/usr/bin/env python3
"""Mutation check of the model: switch off / alter one rule at a time and count
how many fixtures of DIR the mutated model disagrees on with the engine."""
import glob, os, sys, importlib
from multiprocessing import Pool
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.abspath(os.environ.get(
    'ORACLE_TP_WORK', os.path.join(HERE, '..', '..', '.lake', 'oracle', 'fixtures-tp')))
sys.path.insert(0, HERE)
import model_tp as m

MUTS = ['shed_rev', 'seq_levels', 'low_odd', 'blocks_swap', 'tier_first', 'sheds_rev',
        'no_gather_drop', 'dfs65', 'offer_rev', 'drain_cap_m1', 'stash_first',
        'no_copy_drop', 'cap_m1']

def run(args):
    mut, path = args
    m.MUT.clear()
    if mut:
        m.MUT.add(mut)
    f = m.load(path)
    try:
        ok, _, _ = m.compare(f)
    except Exception:
        ok = False
    return ok

def main():
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.join(WORK, 'fx')
    files = sorted(glob.glob(os.path.join(d, 'p*.json')) + glob.glob(os.path.join(d, 'i*.json')))
    if not files:
        sys.exit('fixture directory is missing or empty: ' + d)
    lines = []
    passed = True
    with Pool(48) as pool:
        for mut in [''] + MUTS:
            res = pool.map(run, [(mut, p) for p in files], chunksize=8)
            bad = len(files) - sum(res)
            passed = passed and (bad > 0 if mut else bad == 0)
            pb = sum(1 for p, r in zip(files, res) if not r and os.path.basename(p).startswith('p'))
            ib = bad - pb
            lines.append('%-16s fixtures failing: %4d  (prep %4d, init %4d)' % (mut or 'none (baseline)', bad, pb, ib))
            print(lines[-1], flush=True)
    os.makedirs(WORK, exist_ok=True)
    with open(os.path.join(WORK, 'MUTATIONS.txt'), 'w') as fh:
        fh.write('\n'.join(lines) + '\n')
    sys.exit(0 if passed else 1)

if __name__ == '__main__':
    main()
