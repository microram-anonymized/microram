#!/usr/bin/env python3
"""Lane-exact reference model of the d=2 separated-sources ordinary merge,
written from RebuildBound/Spec/Model/ENGINE_D2.md, compared against a fixture's engine output."""
import json, sys

C = 64

class Fail(Exception):
    pass

def load(path):
    f = json.load(open(path))
    words = {w['key']: int(w['word'], 16) for w in f['words']}
    return f, words

def buckets_of(recs, n):
    bs = [dict() for _ in range(n)]
    for r in recs:
        bs[r['bucket']][r['lane']] = r
    return bs

def lanes_sorted(b):
    return [b[l] for l in sorted(b)]

def lowest_free(b, k, extra_occupied=()):
    occ = set(b) | set(extra_occupied)
    out = []
    l = 0
    while len(out) < k:
        if l not in occ:
            out.append(l)
        l += 1
    return out

def stash_append(stash, recs, cap_buckets=1):
    # stash: list of dicts (buckets); append recs in order into lowest free lanes
    if sum(len(b) for b in stash) + len(recs) > cap_buckets * C:
        raise Fail('stash')
    it = iter(recs)
    pending = list(recs)
    for b in stash:
        free = [l for l in range(C) if l not in b]
        take = min(len(free), len(pending))
        for l, r in zip(free[:take], pending[:take]):
            b[l] = r
        pending = pending[take:]
    assert not pending

def merge_split(first, second, bit, words, stash, blank_first=False):
    """PlanMergePair semantics. Returns new (first, second); sheds into stash."""
    if blank_first:
        first = {}
    f0 = {l: r for l, r in first.items() if not (words[r['key']] >> bit) & 1}
    f1 = {l: r for l, r in first.items() if (words[r['key']] >> bit) & 1}
    s0 = [second[l] for l in sorted(second) if not (words[second[l]['key']] >> bit) & 1]
    s1 = [second[l] for l in sorted(second) if (words[second[l]['key']] >> bit) & 1]
    a0 = min(len(s0), C - len(f0))
    a1 = min(len(s1), C - len(f1))
    out0 = dict(f0)
    for l, r in zip(lowest_free(f0, a0), s0[:a0]):
        out0[l] = r
    out1 = dict(f1)
    for l, r in zip(lowest_free(f1, a1), s1[:a1]):
        out1[l] = r
    kept = set(id(r) for r in s0[:a0]) | set(id(r) for r in s1[:a1])
    shed = [second[l] for l in sorted(second) if id(second[l]) not in kept]
    if shed:
        if blank_first:
            raise AssertionError('blank-first cannot shed')
        try:
            stash_append(stash, shed)
        except Fail:
            raise Fail('butterfly')
        pass
    return out0, out1

def run(path):
    f, words = load(path)
    g = f['geometry']
    U, out_n = g['U'], g['out_buckets']
    home = lambda r: words[r['key']] & (out_n - 1)
    A = buckets_of(f['inputs']['A_main'], g['older_buckets'])
    A_tier = buckets_of(f['inputs']['A_tier'], 1)[0]
    B = buckets_of(f['inputs']['B_main'], U)
    B_tier = buckets_of(f['inputs']['B_tier'], 1)[0]
    out = [dict() for _ in range(out_n)]
    for j in range(g['older_buckets']):
        out[U + j] = dict(A[j])
    stage = [[{}] for _ in range(g['block_bits'])]  # one bucket each
    # A route: bits 0..K-1 over [U, 2U): per level, pairs in ascending first index
    K = g['K']
    try:
        for bit in range(K):
            half = 1 << bit
            for i in range(U, 2 * U):
                if (i - U) & half:
                    continue
                out[i], out[i + half] = merge_split(out[i], out[i + half], bit, words, stage[bit])
        # continuation bit K, blank first
        for i in range(U):
            out[i], out[i + U] = merge_split({}, out[i + U], K, words, None, blank_first=True)
        # ---- finish ----
        ins = [{}]  # insertion stash
        btier_keys = set(r['key'] for r in B_tier.values())
        pool = [stage[b][0] for b in range(g['block_bits'])] + [A_tier]
        pool = [{l: r for l, r in s.items() if r['key'] not in btier_keys} for s in pool]
        leaves = [[] for _ in range(out_n)]
        for s in pool:
            for l in sorted(s):
                leaves[home(s[l])].append(s[l])
        for v in range(out_n):
            if len(leaves[v]) > C:
                raise Fail('residual-dfs-partition')
        leaves = [{i: r for i, r in enumerate(lv)} for lv in leaves]
        direct = dict(B_tier)
        for i in range(U):
            bkeys = set(r['key'] for r in B[i].values())
            for q in range(2):
                ci = i + q * U
                out[ci] = {l: r for l, r in out[ci].items() if r['key'] not in bkeys}
            sheds = []
            for q in range(2):
                ci = i + q * U
                src = [B[i][l] for l in sorted(B[i]) if ((words[B[i][l]['key']] >> K) & 1) == q]
                alloc = min(len(src), C - len(out[ci]))
                for l, r in zip(lowest_free(out[ci], alloc), src[:alloc]):
                    out[ci][l] = r
                sheds.append(src[alloc:])
                if q == 1:
                    if sum(len(b) for b in ins) + len(sheds[0]) + len(sheds[1]) > C:
                        raise Fail('fixed-merge-offers')
                    stash_append(ins, sheds[0] + sheds[1])
                # A leaf offer, kTableWins
                mkeys = set(r['key'] for r in out[ci].values())
                leaf = leaves[ci]
                cand = [l for l in sorted(leaf)]
                drop = [l for l in cand if leaf[l]['key'] in mkeys]
                stale = [l for l in cand if leaf[l]['key'] not in mkeys]
                u = min(len(stale), C - len(out[ci]))
                for ml, ll in zip(lowest_free(out[ci], u), stale[:u]):
                    out[ci][ml] = leaf[ll]
                for ll in drop + stale[:u]:
                    del leaf[ll]
                # B tier offer, kResidualWins, full-home match
                cand = [l for l in sorted(direct) if home(direct[l]) == ci]
                ckeys = set(direct[l]['key'] for l in cand)
                out[ci] = {l: r for l, r in out[ci].items() if r['key'] not in ckeys}
                v = min(len(cand), C - len(out[ci]))
                for ml, dl in zip(lowest_free(out[ci], v), cand[:v]):
                    out[ci][ml] = direct[dl]
                for dl in cand[:v]:
                    del direct[dl]
        tier = [{}]
        for v in range(out_n):
            try:
                stash_append(tier, lanes_sorted(leaves[v]))
            except Fail:
                raise Fail('residual-drain')
        try:
            stash_append(tier, lanes_sorted(direct))
        except Fail:
            raise Fail('residual-drain')
        ins_keys = set(r['key'] for r in ins[0].values())
        a_ids = set()
        for lv in leaves:
            a_ids |= set(id(r) for r in lv.values())
        tier_b_keys = set(r['key'] for r in tier[0].values() if id(r) not in a_ids)
        tier[0] = {l: r for l, r in tier[0].items()
                   if not (id(r) in a_ids and r['key'] in ins_keys)}
        ins[0] = {l: r for l, r in ins[0].items() if r['key'] not in tier_b_keys}
        try:
            stash_append(tier, lanes_sorted(ins[0]))
        except Fail:
            raise Fail('residual-drain')
    except Fail as e:
        return 'failure', str(e), None, None
    return 'success', '', out, tier[0]

def compare(path):
    f, _ = load(path)
    verdict, msg, out, tier = run(path)
    eng = f['outputs']
    print('model:', verdict, msg, '| engine:', eng['verdict'], eng.get('message', ''))
    if verdict != eng['verdict']:
        return False
    if verdict == 'failure':
        return msg in eng['message']
    def norm(recs):
        return sorted((r['bucket'], r['lane'], r['key'], r['value'], r['tombstone']) for r in recs)
    m = [dict(r, bucket=b, lane=l) for b, bk in enumerate(out) for l, r in bk.items()]
    t = [dict(r, bucket=0, lane=l) for l, r in tier.items()]
    # engine values have meta class bit stripped; inputs never carry it
    ok_m = norm(m) == norm(eng['main'])
    ok_t = norm(t) == norm(eng['tier'])
    print('main lane-exact:', ok_m, ' tier lane-exact:', ok_t, ' |main|', len(m), '|tier|', len(t))
    if not (ok_m and ok_t):
        a, b = set(norm(m)), set(norm(eng['main']))
        print('main model-only', sorted(a - b)[:5]); print('main engine-only', sorted(b - a)[:5])
        a, b = set(norm(t)), set(norm(eng['tier']))
        print('tier model-only', sorted(a - b)[:5]); print('tier engine-only', sorted(b - a)[:5])
    return ok_m and ok_t

if __name__ == '__main__':
    allok = True
    for p in sys.argv[1:]:
        allok &= compare(p)
    sys.exit(0 if allok else 1)
