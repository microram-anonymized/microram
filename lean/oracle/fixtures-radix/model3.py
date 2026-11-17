#!/usr/bin/env python3
"""Lane-exact reference model of the separated-sources ordinary merge at a
general digit d = r * 2^e, written from RebuildBound/Spec/Model/ENGINE_RADIX.md and compared
against a fixture's engine output (fd3 fixtures).  Section numbers (P*, F*)
refer to that document."""
import json, sys
from collections import Counter

C = 64


class Fail(Exception):
    def __init__(self, phase, kind):
        super().__init__(f"{phase}/{kind}")
        self.phase, self.kind = phase, kind


class Stash:
    """A multi-bucket stash / tier: list of lane->rec dicts."""
    def __init__(self, buckets):
        self.b = [dict() for _ in range(buckets)]

    def count(self):
        return sum(len(x) for x in self.b)

    def cap(self):
        return C * len(self.b)

    def append(self, recs, phase, kind, cov=None):   # capacity test, then fill
        if self.count() + len(recs) > self.cap():
            raise Fail(phase, kind)
        it = list(recs)
        if cov is not None and recs and self.count() + len(recs) > C:
            cov['stash_bucket1:' + kind] += 1
        for bk in self.b:
            if not it:
                break
            free = [l for l in range(C) if l not in bk]
            for l, rec in zip(free, it):
                bk[l] = rec
            it = it[len(free):]
        assert not it

    def records(self):
        return [rec for bk in self.b for l, rec in sorted(bk.items())]


def lowest_free(b, n):
    out, l = [], 0
    while len(out) < n:
        if l not in b:
            out.append(l)
        l += 1
    return out


def lane_list(b):
    return [b[l] for l in sorted(b)]


def run(f, cov=None, order='engine'):
    cov = Counter() if cov is None else cov
    g = f['geometry']
    U, K, d = g['U'], g['K'], g['digit']
    r, e, k = g['odd_part'], g['power'], g['block_bits']
    N = g['out_buckets']
    assert N == d * U and k == K + e and d == r << e
    SA = g['stage_stash_buckets']
    words = {w['key']: int(w['word'], 16) for w in f['words']}
    t = lambda rec: words[rec['key']]
    bit = lambda rec, j: (t(rec) >> j) & 1
    digit = lambda rec: (t(rec) >> k) % r
    home = lambda rec: (t(rec) & ((1 << k) - 1)) + (1 << k) * digit(rec)
    way = lambda rec: ((t(rec) >> K) & ((1 << e) - 1)) | (digit(rec) << e)

    def buckets_of(recs, n):
        bs = [dict() for _ in range(n)]
        for x in recs:
            rec = dict(x)
            bs[x['bucket']][x['lane']] = rec
        return bs

    inp = f['inputs']
    A = buckets_of(inp['A_main'], g['older_buckets'])
    A_tier = buckets_of(inp['A_tier'], g['older_tier_buckets'])
    B = buckets_of(inp['B_main'], U)
    B_tier = buckets_of(inp['B_tier'], g['carry_tier_buckets'])
    for bk in B_tier:
        for rec in bk.values():
            rec['cls'] = 'B'

    out = [dict() for _ in range(N)]
    for j in range(g['older_buckets']):          # P1: copy A to [U, dU)
        out[U + j] = dict(A[j])
    stage = [Stash(SA) for _ in range(k)]         # stash[j], one per bit
    writers = [set() for _ in range(k)]
    cur = ['']
    radix = Stash(SA)

    def pair(i, j, b, stash, phase, kind):       # MergeSplit (sec. 2)
        F, S = out[i], out[j]
        f0 = {l: x for l, x in F.items() if not bit(x, b)}
        f1 = {l: x for l, x in F.items() if bit(x, b)}
        s0 = [S[l] for l in sorted(S) if not bit(S[l], b)]
        s1 = [S[l] for l in sorted(S) if bit(S[l], b)]
        a0, a1 = min(len(s0), C - len(f0)), min(len(s1), C - len(f1))
        for l, x in zip(lowest_free(f0, a0), s0[:a0]):
            f0[l] = x
        for l, x in zip(lowest_free(f1, a1), s1[:a1]):
            f1[l] = x
        kept = {id(x) for x in s0[:a0] + s1[:a1]}
        shed = [S[l] for l in sorted(S) if id(S[l]) not in kept]
        if shed:
            cov[f'shed:{kind}:bit{b}'] += len(shed)
            if kind == 'route-level' and stash.count():
                cov['cont_into_nonempty_stash'] += 1
            if kind == 'route-level' and writers[b] - {'cont'}:
                cov['cont_shares_stash_with_span'] += 1
            if stash is not radix:
                writers[b].add(cur[0])
        stash.append(shed, phase, kind, cov)
        out[i], out[j] = f0, f1

    def route(base, s, levels):                   # RouteSubnetworkRecursive
        if levels <= 4:
            count = 1 << levels
            lev = 0
            while lev + 1 < levels:
                half, b = 1 << lev, s + lev
                for mid in range(count):
                    if mid & (half | (half << 1)):
                        continue
                    i, h = base + (mid << s), 1 << b
                    # quad = pairs (0,1),(2,3) on b, then (0,2),(1,3) on b+1
                    # (both levels' capacity tested first; same verdict)
                    pair(i, i + h, b, stage[b], 'prepare-older', 'butterfly')
                    pair(i + 2 * h, i + 3 * h, b, stage[b], 'prepare-older', 'butterfly')
                    pair(i, i + 2 * h, b + 1, stage[b + 1], 'prepare-older', 'butterfly')
                    pair(i + h, i + 3 * h, b + 1, stage[b + 1], 'prepare-older', 'butterfly')
                lev += 2
            while lev < levels:
                half, b = 1 << lev, s + lev
                for mid in range(count):
                    if mid & half:
                        continue
                    pair(base + (mid << s), base + ((mid | half) << s), b,
                         stage[b], 'prepare-older', 'butterfly')
                lev += 1
            return
        low = (levels >> 1) & ~1
        high = levels - low
        for h in range(1 << high):
            route(base + (h << (s + low)), s, low)
        for l in range(1 << low):
            route(base + (l << s), s + low, high)

    try:
        # P2: pure blocks q = 1..r-1, then block 0's spans largest first
        if order == 'canonical':
            # Job.lean's d = 2 schedule, generalized: stage by stage over the
            # whole blank-region output, pairs in ascending first index
            for b in range(k):
                for i in range(N):
                    if not (i >> b) & 1:
                        pair(i, i + (1 << b), b, stage[b], 'prepare-older', 'butterfly')
        for q in (range(1, r) if order != 'canonical' else ()):
            cur[0] = f'block{q}'
            route(q << k, 0, k)
        if order == 'blank-full' and e > 0:
            # the "simple form": block 0's full k-level network
            # with [0, U) blank (same MergeSplit set, other order)
            cur[0] = 'block0'
            route(0, 0, k)
        for u in range(e - 1, -1, -1):
            if order != 'engine':
                break
            cur[0] = f'span{u}'
            route(1 << (K + u), 0, K + u)
        cur[0] = 'cont'

        # P3: continuation bits K..k-1 over block 0
        for b in (range(K, k) if order == 'engine' else ()):
            half = 1 << b
            for i in range(half):
                if b == K:                        # blank first: compact
                    L = lane_list(out[i + half])
                    out[i] = {n: x for n, x in enumerate(y for y in L if not bit(y, b))}
                    out[i + half] = {n: x for n, x in enumerate(y for y in L if bit(y, b))}
                else:
                    pair(i, i + half, b, stage[b], 'prepare-older', 'route-level')
        # P4: terminal radix pass
        if r > 1:
            blk = 1 << k
            for p in range(blk):
                ins = [out[q * blk + p] for q in range(r)]
                routes = [[[l for l in sorted(ins[i]) if digit(ins[i][l]) == q]
                           for q in range(r)] for i in range(r)]
                new, shed = [], [set() for _ in range(r)]
                for q in range(r):
                    o = {l: ins[q][l] for l in routes[q][q]}
                    for i in range(r):
                        if i == q:
                            continue
                        src = routes[i][q]
                        a = min(len(src), C - len(o))
                        for l, sl in zip(lowest_free(o, a), src[:a]):
                            o[l] = ins[i][sl]
                        shed[i] |= set(src[a:])
                    new.append(o)
                rs = [ins[i][l] for i in range(r) for l in sorted(shed[i])]
                if rs:
                    cov['shed:radix'] += len(rs)
                    cov['shed:radix-multi-input'] += sum(1 for i in range(r) if shed[i]) > 1
                radix.append(rs, 'prepare-older', 'radix-route', cov)
                for q in range(r):
                    out[q * blk + p] = new[q]

        cov['stage_stash_multi_writer'] += sum(1 for w in writers if len(w) > 1)
        # ---- finish ----
        ins = Stash(SA)
        btier_keys = {x['key'] for bk in B_tier for x in bk.values()}
        pool = [s.b for s in stage] + ([radix.b] if r > 1 else []) + [A_tier]
        # F1 pool dedup: B tier (rank 0) clears A-class slots (rank 2)
        cov['pool_dedup'] += sum(1 for slot in pool for bk in slot for x in bk.values()
                                 if x['key'] in btier_keys)
        pool = [[{l: x for l, x in bk.items() if x['key'] not in btier_keys}
                 for bk in slot] for slot in pool]
        I, Dc = g['range_index_bits'], g['range_bits']
        leaves = [[] for _ in range(1 << Dc)]
        for slot in pool:                          # F3 gather order
            for bk in slot:
                for l in sorted(bk):
                    leaves[home(bk[l]) >> I].append(bk[l])
        if any(len(lv) > C for lv in leaves):     # F4 DFS (pages = 1)
            per_home = Counter(home(x) for lv in leaves for x in lv)
            if max(per_home.values()) <= C:
                cov['dfs_fail_leaf_sum_only'] += 1
            raise Fail('finish', 'residual-dfs-partition')
        leaves = [dict(enumerate(lv)) for lv in leaves]
        direct = [dict(bk) for bk in B_tier]      # F2 direct copy
        for i in range(U):                         # F5
            bkeys = {x['key'] for x in B[i].values()}
            for q in range(d):
                ci = i + q * U
                cov['bmain_dedup'] += sum(1 for x in out[ci].values() if x['key'] in bkeys)
                out[ci] = {l: x for l, x in out[ci].items() if x['key'] not in bkeys}
            sheds = []
            for q in range(d):
                ci = i + q * U
                src = [B[i][l] for l in sorted(B[i]) if way(B[i][l]) == q]
                a = min(len(src), C - len(out[ci]))
                for l, x in zip(lowest_free(out[ci], a), src[:a]):
                    out[ci][l] = x
                sheds.append(src[a:])
                if src[a:]:
                    cov['ins_shed'] += len(src[a:])
                    cov[f'ins_shed_way{q}'] += 1
                if q == d - 1:
                    ins.append([x for s in sheds for x in s], 'finish', 'fixed-merge-offers', cov)
                # A leaf offer (kTableWins)
                leaf = leaves[ci >> I]
                mk = {x['key'] for x in out[ci].values()}
                cand = [l for l in sorted(leaf) if home(leaf[l]) == ci]
                drop = [l for l in cand if leaf[l]['key'] in mk]
                stale = [l for l in cand if leaf[l]['key'] not in mk]
                u = min(len(stale), C - len(out[ci]))
                for ml, ll in zip(lowest_free(out[ci], u), stale[:u]):
                    out[ci][ml] = leaf[ll]
                cov['leaf_drop'] += len(drop)
                cov['leaf_absorb'] += u
                if I > 0 and u and any(home(x) != ci for x in leaf.values()):
                    cov['leaf_absorb_shared_leaf'] += 1
                if u < len(stale):
                    cov['leaf_leftover_at_offer'] += 1
                for ll in drop + stale[:u]:
                    del leaf[ll]
                # B tier offer (kResidualWins), one plan per tier bucket
                for grp in direct:
                    fc = [l for l in sorted(grp) if home(grp[l]) == ci]
                    ck = {grp[l]['key'] for l in fc}
                    ncl = sum(1 for x in out[ci].values() if x['key'] in ck)
                    cov['btier_clear'] += ncl
                    out[ci] = {l: x for l, x in out[ci].items() if x['key'] not in ck}
                    v = min(len(fc), C - len(out[ci]))
                    cov['btier_absorb'] += v
                    if grp is not direct[0] and v:
                        cov['btier_absorb_group1'] += v
                    if v < len(fc):
                        cov['btier_leftover'] += len(fc) - v
                    for ml, dl in zip(lowest_free(out[ci], v), fc[:v]):
                        out[ci][ml] = grp[dl]
                    for dl in fc[:v]:
                        del grp[dl]
        tier = Stash(g['out_tier_buckets'])       # F6 first drain
        for rb in leaves + direct:
            cov['leftover'] += len(rb)
            tier.append(lane_list(rb), 'finish', 'residual-drain', cov)
        ins_keys = {x['key'] for x in ins.records()}   # F7 leftover dedup
        tier_b_keys = {x['key'] for x in tier.records() if x.get('cls') == 'B'}
        cov['leftover_dedup_A'] += sum(1 for bk in tier.b for x in bk.values()
                                       if x.get('cls') != 'B' and x['key'] in ins_keys)
        tier.b = [{l: x for l, x in bk.items()
                   if not (x.get('cls') != 'B' and x['key'] in ins_keys)} for bk in tier.b]
        ins.b = [{l: x for l, x in bk.items() if x['key'] not in tier_b_keys} for bk in ins.b]
        for bk in ins.b:                           # F8 second drain
            cov['ins_drained'] += len(bk)
            tier.append(lane_list(bk), 'finish', 'residual-drain', cov)
    except Fail as fl:
        return 'failure', fl, None, None
    return 'success', None, out, tier


def norm(recs):
    return sorted((x['bucket'], x['lane'], x['key'], x['value'], x['tombstone']) for x in recs)


def compare(path, verbose=False, cov=None):
    f = json.load(open(path))
    verdict, fl, out, tier = run(f, cov)
    eng = f['outputs']
    res = {'path': path, 'model': verdict, 'engine': eng['verdict'],
           'kind': None if fl is None else fl.kind, 'ok': False}
    if verdict != eng['verdict']:
        res['why'] = 'verdict'
        return res
    if verdict == 'failure':
        want = f"the {fl.phase} phase ran out of room at {fl.kind};"
        res['ok'] = want in eng['message']
        if not res['ok']:
            res['why'] = 'message: ' + eng['message']
        return res
    m = [dict(x, bucket=b, lane=l) for b, bk in enumerate(out) for l, x in bk.items()]
    t = [dict(x, bucket=b, lane=l) for b, bk in enumerate(tier.b) for l, x in bk.items()]
    ok_m, ok_t = norm(m) == norm(eng['main']), norm(t) == norm(eng['tier'])
    res['ok'] = ok_m and ok_t
    res['main'], res['tier'] = len(m), len(t)
    if not res['ok']:
        res['why'] = f'lanes main={ok_m} tier={ok_t}'
        if verbose:
            a, b = set(norm(m)), set(norm(eng['main']))
            print(' main model-only', sorted(a - b)[:6])
            print(' main engine-only', sorted(b - a)[:6])
            a, b = set(norm(t)), set(norm(eng['tier']))
            print(' tier model-only', sorted(a - b)[:6])
            print(' tier engine-only', sorted(b - a)[:6])
    return res


if __name__ == '__main__':
    allok = True
    for p in sys.argv[1:]:
        r = compare(p, verbose=True)
        print(p, r)
        allok &= r['ok']
    sys.exit(0 if allok else 1)


def order_agreement(f, order):
    """(same verdict, same failure kind, record-exact, lane-exact) of a
    schedule variant against the engine's output in fixture f."""
    v, fl, out, tier = run(f, order=order)
    eng = f['outputs']
    if v != eng['verdict']:
        return (False, False, False, False)
    if v == 'failure':
        return (True, f"at {fl.kind};" in eng['message'], True, True)
    m = sorted((b, l, x['key']) for b, bk in enumerate(out) for l, x in bk.items())
    t = sorted((b, l, x['key']) for b, bk in enumerate(tier.b) for l, x in bk.items())
    em = sorted((x['bucket'], x['lane'], x['key']) for x in eng['main'])
    et = sorted((x['bucket'], x['lane'], x['key']) for x in eng['tier'])
    rec = lambda mm, tt: (sorted((b, k) for b, l, k in mm), sorted(k for b, l, k in tt))
    return (True, True, rec(m, t) == rec(em, et), m == em and t == et)
