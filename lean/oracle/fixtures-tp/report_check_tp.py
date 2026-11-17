#!/usr/bin/env python3
"""Cross-check of REPORT.tex (sec:binary-top-preparation, sec:top-final-ranges,
sec:top-dfs-decision) against the ENGINE's outputs on every successful fixture.

The report's logical reference (computed here from the INPUTS only):
  X_v   = surviving input records whose new home is v  (flagged tombstones dropped)
  E     = sum_v (X_v - 64)+
  E_b   = sum_v (X_{b,v} - 64)+,  V_b(x) = 2^b floor(O_x/2^b) + (H_x mod 2^b)
          (b one-based; O_x = the old bucket of x in A's main / the scattered bucket)
Claims checked on the engine's output:
  (1) the output multiset is the input minus flagged tombstones      (conservation)
  (2) main holds min(X_v, 64) records at every home v
  (3) R (prep) / the published tier (init) holds exactly E records
  (4) every R / tier record names a FULL home
  (5) stage stash b holds at most E_b records (stage_counts of the model run)
  (6) initialization: the first stage (bit 0) never sheds
  (7) r_pages == S for a preparation; init tier capacity == 64 * tier pages
"""
import glob, os, sys
from collections import Counter
from multiprocessing import Pool
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.abspath(os.environ.get(
    'ORACLE_TP_WORK', os.path.join(HERE, '..', '..', '.lake', 'oracle', 'fixtures-tp')))
sys.path.insert(0, HERE)
import model_tp as m


def check(path):
    m.LAST.clear()
    f = m.load(path)
    g = f['geometry']
    T, bb = g['T'], g['block_bits']
    words = {w['key']: int(w['word'], 16) for w in f['words']}
    out = f['outputs']
    prep = f['format'] == 'top-prep-fixture/0'
    res = {'file': os.path.basename(path), 'ok': True, 'notes': [], 'prep': prep,
           'verdict': out['verdict']}
    if prep:
        main_in = [(d['bucket'], d) for d in f['inputs']['A_main']]
        tier_in = [d for d in f['inputs']['A_tier']]
        recs = [d for _, d in main_in] + tier_in
        old = {d['key']: b for b, d in main_in}
    else:
        recs = f['input']
        old = {d['key']: j // 32 for j, d in enumerate(recs)}
        recs = [dict(d, tombstone=False, unshadowed=False) for d in recs]
    surv = [d for d in recs if not (d['tombstone'] and d['unshadowed'])]
    res['n_in'] = len(recs)
    res['flag_dropped'] = len(recs) - len(surv)
    res['tomb_in'] = sum(1 for d in surv if d['tombstone'])
    X = Counter(words[d['key']] & (T - 1) for d in surv)
    E = sum(max(0, x - 64) for x in X.values())
    Ebs = []
    for b in range(1, bb + 1):
        Xb = Counter()
        for d in surv:
            if d['key'] not in old:
                continue
            Xb[((old[d['key']] >> b) << b) + (words[d['key']] & ((1 << b) - 1))] += 1
        Ebs.append(sum(max(0, x - 64) for x in Xb.values()))
    if out['verdict'] != 'success':
        S = g['stage_stash_buckets']
        cap = (g['r_pages'] if prep else g['out_tier_pages']) * 64
        kind = out['kind']
        if kind == 'butterfly':
            res['fail_claim'] = max(Ebs[:bb - 1]) > 64 * S
        elif kind == 'butterfly-offers':
            res['fail_claim'] = Ebs[bb - 1] > 64 * S
        elif kind == 'residual-drain':
            res['fail_claim'] = E > cap
        else:
            res['fail_claim'] = None     # a range event, not an E event
        res['kind'] = kind
        return res
    X = Counter(words[d['key']] & (T - 1) for d in surv)
    E = sum(max(0, x - 64) for x in X.values())
    tier = out['R'] if prep else out['tier']
    keys_out = Counter(d['key'] for d in out['main']) + Counter(d['key'] for d in tier)
    keys_in = Counter(d['key'] for d in surv)
    c1 = keys_out == keys_in
    mainc = Counter(d['bucket'] for d in out['main'])
    c2 = all(mainc.get(v, 0) == min(X.get(v, 0), 64) for v in range(T))
    c3 = len(tier) == E
    c4 = all(mainc[words[d['key']] & (T - 1)] == 64 for d in tier)
    # (5) stage bounds
    ok, det = m.compare(f)[0], None
    sc = m.LAST.get('stage_counts')
    c5 = True
    if sc is not None:
        for b in range(1, bb + 1):
            Xb = Counter()
            for d in surv:
                if d['key'] not in old:
                    continue    # A's old tier records are not routed
                O = old[d['key']]
                H = words[d['key']]
                Xb[((O >> b) << b) + (H & ((1 << b) - 1))] += 1
            Eb = sum(max(0, x - 64) for x in Xb.values())
            if sc[b - 1] > Eb:
                c5 = False
                res['notes'].append('stage %d: stash %d > E_b %d' % (b, sc[b - 1], Eb))
        if not prep and sc[0] != 0:
            res['notes'].append('init stage 1 shed %d' % sc[0])
            c5 = False
    c7 = (g['r_pages'] == g['stage_stash_buckets']) if prep else (g['out_tier_capacity'] == 64 * g['out_tier_pages'])
    res.update(c1=c1, c2=c2, c3=c3, c4=c4, c5=c5, c7=c7, E=E, nR=len(tier),
               tomb_out=sum(1 for d in out['main'] if d['tombstone']) + sum(1 for d in tier if d['tombstone']))
    res['ok'] = c1 and c2 and c3 and c4 and c5 and c7
    return res


def main():
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.join(WORK, 'fx')
    files = sorted(glob.glob(os.path.join(d, 'p*.json')) + glob.glob(os.path.join(d, 'i*.json')))
    if not files:
        sys.exit('fixture directory is missing or empty: ' + d)
    with Pool(48) as pool:
        rows = pool.map(check, files, chunksize=4)
    lines = []
    for title, sel in (('PREPARATION', True), ('INITIALIZATION', False)):
        rs = [r for r in rows if r['prep'] == sel and r['verdict'] == 'success']
        lines.append('%s: %d successful fixtures; report reference holds on %d' % (
            title, len(rs), sum(r['ok'] for r in rs)))
        for k, name in (('c1', 'conservation (output = input minus flagged tombstones)'),
                        ('c2', 'main holds min(X_v,64) at every home'),
                        ('c3', '|R or published tier| == E exactly'),
                        ('c4', 'every leftover names a full home'),
                        ('c5', 'stage stash b <= E_b (and init stage 1 never sheds)'),
                        ('c7', 'r_pages == S (prep) / tier capacity == 64*pages (init)')):
            lines.append('   %-62s %d/%d' % (name, sum(r[k] for r in rs), len(rs)))
        lines.append('   fixtures with plain tombstones surviving into the output: %d' % sum(1 for r in rs if r['tomb_out'] > 0))
        lines.append('   fixtures with flagged tombstones dropped before routing: %d' % sum(1 for r in rs if r['flag_dropped'] > 0))
        lines.append('   fixtures with R/tier > 0 records: %d' % sum(1 for r in rs if r['nR'] > 0))
    for title, sel in (('PREPARATION', True), ('INITIALIZATION', False)):
        for kind, claim in (('butterfly', 'some E_b (b < k) exceeds 64 S'),
                            ('butterfly-offers', 'E_k exceeds 64 S'),
                            ('residual-drain', 'E exceeds the drain capacity'),
                            ('residual-dfs-partition', None)):
            rs = [r for r in rows if r['prep'] == sel and r['verdict'] == 'failure' and r.get('kind') == kind]
            if claim:
                lines.append('%s failures %-22s %4d   %s on %d' % (title, kind, len(rs), claim,
                                                                    sum(1 for r in rs if r['fail_claim'])))
            else:
                lines.append('%s failures %-22s %4d   (a range event: not an E event)' % (title, kind, len(rs)))
    bad = [r for r in rows if not r['ok'] or (r['verdict'] == 'failure' and r.get('fail_claim') is False)]
    for r in bad[:20]:
        lines.append('DISAGREES %s %s' % (r['file'], r['notes']))
    print('\n'.join(lines))
    os.makedirs(WORK, exist_ok=True)
    with open(os.path.join(WORK, 'REPORT_CHECK.txt'), 'w') as fh:
        fh.write('\n'.join(lines) + '\n')
    sys.exit(0 if not bad else 1)


if __name__ == '__main__':
    main()
