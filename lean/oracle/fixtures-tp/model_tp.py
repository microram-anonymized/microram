#!/usr/bin/env python3
"""Lane-exact reference model of the TOP PREPARATION and of the DIRECT
INITIALIZATION's route, written from ENGINE_TOPPREP.md (sections 3-8).

`model_prep(fixture)` and `model_init(fixture)` are pure functions of the
fixture's geometry, its input records (A main + A tier, or the input list) and
the word of every key; they never look at the engine's outputs.  `counters`
records which paths a run exercised (coverage only; no effect on the result).
"""
import json
from collections import Counter

CAP = 64
LAST = {}     # per-run diagnostics read by report_check_tp.py (not used by the model)
MUT = set()   # mutation switches (used only by mutate_tp.py to test the fixtures)


class Fail(Exception):
    def __init__(self, kind):
        super().__init__(kind)
        self.kind = kind


class Result:
    def __init__(self, verdict, kind, main, tier, counters, scattered=None):
        self.verdict = verdict
        self.kind = kind
        self.main = main      # list of (bucket, lane, key, value, tombstone, unshadowed)
        self.tier = tier      # list of (page, lane, key, value, tombstone, unshadowed)
        self.counters = counters
        self.scattered = scattered


def lowest_free(occupied, n):
    out, lane = [], 0
    while len(out) < n:
        if lane not in occupied:
            out.append(lane)
        lane += 1
    return out


def lanes(bucket):
    return [bucket[l] for l in sorted(bucket)]


class Stash:
    """`pages` buckets of 64 lanes (a stage stash, or the drain target)."""

    def __init__(self, pages):
        self.pages = [dict() for _ in range(pages)]
        self.capacity = pages * CAP

    def count(self):
        return sum(len(p) for p in self.pages)

    def append(self, recs):
        pending = list(recs)
        for page in self.pages:
            free = lowest_free(set(page), min(len(pending), CAP - len(page)))
            for lane, rec in zip(free, pending):
                page[lane] = rec
            pending = pending[len(free):]
        assert not pending


def rec_of(d):
    return (d['key'], d['value'], d['tombstone'], d['unshadowed'])


def is_flagged(r):          # tombstone with kMetaUnshadowed
    return r[2] and r[3]


def route_and_pack(g, words, C, tier_pages, drain_pages, cnt):
    """Sections 4-8.  C: list of T dicts lane -> rec (A copied, or scattered).
    tier_pages: list of dicts (A's old tier pages; [] has the width of the tier
    but no records).  Returns (C, drain Stash) or raises Fail."""
    T, bb, S = g['T'], g['block_bits'], g['stage_stash_buckets']
    half = T >> 1

    def word(r):
        return words[r[0]]

    def home(r):
        return word(r) & (T - 1)

    def bit(r, b):
        return (word(r) >> b) & 1

    sh = [Stash(S) for _ in range(bb)]

    # ---- 4.2 the pair merge-split --------------------------------------
    def split(i, j, b, kind):
        F, Sx = C[i], C[j]
        F0 = {l: r for l, r in F.items() if bit(r, b) == 0}
        F1 = {l: r for l, r in F.items() if bit(r, b) == 1}
        S0 = [(l, r) for l, r in sorted(Sx.items()) if bit(r, b) == 0]
        S1 = [(l, r) for l, r in sorted(Sx.items()) if bit(r, b) == 1]
        a0 = min(len(S0), CAP - len(F0))
        a1 = min(len(S1), CAP - len(F1))
        for lane, (_, r) in zip(lowest_free(set(F0), a0), S0[:a0]):
            F0[lane] = r
        for lane, (_, r) in zip(lowest_free(set(F1), a1), S1[:a1]):
            F1[lane] = r
        shed = sorted(S0[a0:] + S1[a1:], key=lambda x: x[0])
        shed = [r for _, r in shed]
        if 'shed_rev' in MUT:
            shed = shed[::-1]
        if sh[b].count() + len(shed) > sh[b].capacity - (1 if 'cap_m1' in MUT else 0):
            raise Fail(kind)
        sh[b].append(shed)
        if shed:
            cnt['shed_bit%d' % min(b, bb - 1)] += 1
            cnt['sheds'] += len(shed)
        C[i], C[j] = F0, F1

    # ---- 4.3 the recursive butterfly -----------------------------------
    def route(base, stride, levels):
        if levels <= 4:                              # leaf: quads, then a pair level
            count = 1 << levels
            lev = 0
            while lev + 1 < levels and 'seq_levels' not in MUT:
                h = 1 << lev
                b = stride + lev
                for mid in range(count):
                    if mid & (h | (h << 1)):
                        continue
                    q0 = base + (mid << stride)
                    q1 = base + ((mid + h) << stride)
                    q2 = base + ((mid + 2 * h) << stride)
                    q3 = base + ((mid + 3 * h) << stride)
                    split(q0, q1, b, 'butterfly')
                    split(q2, q3, b, 'butterfly')
                    split(q0, q2, b + 1, 'butterfly')
                    split(q1, q3, b + 1, 'butterfly')
                lev += 2
            while lev < levels:
                h = 1 << lev
                b = stride + lev
                for mid in range(count):
                    if mid & h:
                        continue
                    split(base + (mid << stride), base + ((mid | h) << stride), b,
                          'butterfly')
                lev += 1
            return
        low = (levels >> 1) & ~1
        if 'low_odd' in MUT:
            low = levels >> 1
        high = levels - low
        for hh in range(1 << high):
            route(base + (hh << (stride + low)), stride, low)
        for ll in range(1 << low):
            route(base + (ll << stride), stride + low, high)

    for blk in ((1, 0) if 'blocks_swap' in MUT else (0, 1)):
        route(blk * half, 0, bb - 1)

    for b in range(bb - 1):
        if len(sh[b].pages) > 1 and sh[b].pages[1]:
            cnt['stage_page1'] += 1
    # ---- 5 the pool, its range table -----------------------------------
    pool_pages = [sh[b].pages[p] for b in range(bb - 1) for p in range(S)]
    pool_pages += tier_pages
    if 'tier_first' in MUT:
        pool_pages = tier_pages + pool_pages[:len(pool_pages) - len(tier_pages)]
    if 'sheds_rev' in MUT:
        pool_pages = [sh[b].pages[p] for b in reversed(range(bb - 1)) for p in range(S)] + tier_pages
    swept = len(pool_pages)
    assert swept == g['pool_swept_buckets']
    ml = bb
    ranges = []                      # the range buckets: dict lane -> rec
    if ml <= 3:
        index_bits = ml
        for pg in pool_pages:
            ranges.append({l: r for l, r in pg.items() if not is_flagged(r)})
        cnt['direct_plan'] += 1

        def candidates(b):
            return [ranges[k] for k in range(len(ranges))]
    else:
        rho = 0
        while (1 << rho) < 8 * swept:
            rho += 1
        rho = min(rho, ml)
        index_bits = ml - rho
        if index_bits > 18:
            rho += index_bits - 18
            index_bits = 18
        pool = []
        for pg in pool_pages:
            for l in sorted(pg):
                if 'no_gather_drop' in MUT or not is_flagged(pg[l]):
                    pool.append(pg[l])
                else:
                    cnt['gather_flag_drop'] += 1
        leaves = [[] for _ in range(1 << rho)]
        for r in pool:
            leaves[home(r) >> index_bits].append(r)
        if max(len(x) for x in leaves) > (CAP + 1 if 'dfs65' in MUT else CAP):
            raise Fail('residual-dfs-partition')
        cnt['dfs_gathered'] += len(pool)
        if any(len({home(r) for r in x}) > 1 for x in leaves):
            cnt['leaf_multi_home'] += 1
        if max(len(x) for x in leaves) >= CAP - 2:
            cnt['leaf_near_64'] += 1
        for x in leaves:
            ranges.append({l: r for l, r in enumerate(x)})

        def candidates(b):
            return [ranges[b >> index_bits]]

    # ---- 6 the offer ----------------------------------------------------
    def offer(b):
        for rb in candidates(b):
            cand = [(l, r) for l, r in sorted(rb.items()) if home(r) == b]
            if 'offer_rev' in MUT:
                cand = cand[::-1]
            n = min(len(cand), CAP - len(C[b]))
            if len(cand) > n:
                cnt['offer_blocked'] += 1
            if len(cand) > 1 and n >= 1 and len(C[b]) > 0:
                cnt['offer_into_nonempty'] += 1
            for lane, (l, r) in zip(lowest_free(set(C[b]), n), cand[:n]):
                C[b][lane] = r
                del rb[l]
            cnt['offer_absorbed'] += n

    # ---- 4.4 the last level, fused with the offers ----------------------
    for i in range(half):
        split(i, i + half, bb - 1, 'butterfly-offers')
        offer(i)
        offer(i + half)
    if len(sh[bb - 1].pages) > 1 and sh[bb - 1].pages[1]:
        cnt['last_page1'] += 1

    # ---- 7 the drain ----------------------------------------------------
    drain = Stash(drain_pages)
    if 'drain_cap_m1' in MUT:
        drain.capacity -= 1
    if 'stash_first' in MUT:
        for pg in sh[bb - 1].pages:
            L = lanes(pg)
            if drain.count() + len(L) > drain.capacity:
                raise Fail('residual-drain')
            drain.append(L)
        for pg in sh[bb - 1].pages:
            pg.clear()
    for rb in ranges:
        L = lanes(rb)
        if drain.count() + len(L) > drain.capacity:
            raise Fail('residual-drain')
        drain.append(L)
        cnt['range_leftover'] += len(L)
    if drain.count() > 0 and drain.count() > CAP:
        cnt['drain_over_64_before_last'] += 1
    for pg in sh[bb - 1].pages:
        L = lanes(pg)
        if drain.count() + len(L) > drain.capacity:
            raise Fail('residual-drain')
        drain.append(L)
        cnt['last_level_drain'] += len(L)
    LAST['stage_counts'] = [sh[b].count() for b in range(bb)]
    if len(drain.pages) > 1 and drain.pages[1]:
        cnt['drain_page1'] += 1
    return C, drain


def dfs_geometry(g):
    """Section 2: the plan fields derived from (T, S, tier pages), checked
    against what the dumper read out of the engine.  Returns a list of
    disagreements (empty = agreement)."""
    T, S = g['T'], g['stage_stash_buckets']
    bb = T.bit_length() - 1
    bad = []
    if T != g['D'] * g['U'] or g['U'] != 1 << g['K'] or g['block_bits'] != bb or g['e'] != g['D'].bit_length() - 1:
        bad.append('T/U/D/K/e/block_bits')
    if g['r_pages'] != S and g.get('r_pages') != 0:
        bad.append('r_pages != S')
    if g['n_sheds'] != bb - 1:
        bad.append('n_sheds')
    swept = (bb - 1) * S + g['a_tier_pages']
    if g['pool_swept_buckets'] != swept or g['pool_slots'] != 64 * swept or g['main_levels'] != bb:
        bad.append('pool shape')
    if bb <= 3:
        want = dict(dfs=0, range_bits=0, range_index_bits=bb, range_groups=swept,
                    range_buckets=swept, range_scatter_per_bucket=64)
    else:
        rho = 0
        while (1 << rho) < 8 * swept:
            rho += 1
        rho = min(rho, bb)
        I = bb - rho
        if I > 18:
            rho += I - 18
            I = 18
        want = dict(dfs=1, range_bits=rho, range_index_bits=I, range_groups=1,
                    range_buckets=1 << rho, range_scatter_per_bucket=64)
        P, s0 = 64 * swept, 64
        hd = 0
        while hd < rho and (s0 << (hd + 1)) < P:
            hd += 1
        caps = [P if (h > 16 or (s0 << h) >= P) else (s0 << h) for h in range(rho + 1)]
        if 'dfs_units' in g and (g.get('dfs_direct_height') != hd or g.get('dfs_capacities') != caps or g.get('dfs_units') != 1 << rho):
            bad.append('dfs workspace hd=%s caps=%s units=%s vs %s %s %s' % (
                g.get('dfs_direct_height'), g.get('dfs_capacities'), g.get('dfs_units'),
                hd, caps, 1 << rho))
    for k, v in want.items():
        if g[k] != v:
            bad.append('%s: engine %s model %s' % (k, g[k], v))
    return bad


def out_list(buckets, key):
    out = []
    for b, d in enumerate(buckets):
        for l in sorted(d):
            r = d[l]
            out.append((b, l, r[0], r[1], r[2], r[3]))
    return out


def model_prep(f):
    g = f['geometry']
    T = g['T']
    words = {w['key']: int(w['word'], 16) for w in f['words']}
    cnt = Counter()
    # ---- 3.1 the copy-and-retag of A's main ------------------------------
    C = [dict() for _ in range(T)]
    for d in f['inputs']['A_main']:
        r = rec_of(d)
        if is_flagged(r) and 'no_copy_drop' not in MUT:
            cnt['copy_flag_drop'] += 1
            continue
        C[d['bucket']][d['lane']] = r
        if r[2]:
            cnt['a_tomb'] += 1
    tier = [dict() for _ in range(g['a_tier_pages'])]
    for d in f['inputs']['A_tier']:
        tier[d['page']][d['lane']] = rec_of(d)
        cnt['a_tier'] += 1
    try:
        C, drain = route_and_pack(g, words, C, tier, g['r_pages'], cnt)
    except Fail as e:
        return Result('failure', e.kind, [], [], cnt)
    return Result('success', '', out_list(C, 0), out_list(drain.pages, 1), cnt)


def scatter_rule(count, T, per_bucket=32):
    """Section 9: input record j -> (bucket j // 32, lane j % 32)."""
    return [(j // per_bucket, j % per_bucket) for j in range(count)]


def model_init(f):
    g = f['geometry']
    T = g['T']
    words = {w['key']: int(w['word'], 16) for w in f['words']}
    cnt = Counter()
    inp = f['input']
    C = [dict() for _ in range(T)]
    scattered = []
    for j, (b, l) in enumerate(scatter_rule(len(inp), T)):
        r = (inp[j]['key'], inp[j]['value'] + '00', False, False)
        C[b][l] = r
        scattered.append((b, l, r[0], r[1], r[2], r[3]))
    tier = [dict() for _ in range(g['a_tier_pages'])]   # empty: no older tier
    try:
        C, drain = route_and_pack(g, words, C, tier, g['out_tier_pages'], cnt)
    except Fail as e:
        return Result('failure', e.kind, [], [], cnt, scattered)
    return Result('success', '', out_list(C, 0), out_list(drain.pages, 1), cnt,
                  scattered)


def key_of(d, where):
    return (d[where], d['lane'], d['key'], d['value'], d['tombstone'], d['unshadowed'])


def compare(f):
    """(ok, detail, result)."""
    fmt = f['format']
    if fmt == 'top-prep-fixture/0':
        res = model_prep(f)
        tier_name = 'R'
    else:
        res = model_init(f)
        tier_name = 'tier'
    out = f['outputs']
    bad = dfs_geometry(f['geometry'])
    if bad:
        return False, 'geometry: ' + '; '.join(bad), res
    if fmt == 'top-init-fixture/0' and 'scattered' in f:
        eng_scat = [key_of(d, 'bucket') for d in f['scattered']['main']]
        if eng_scat != res.scattered:
            return False, 'scatter mismatch', res
    if res.verdict != out['verdict']:
        return False, 'verdict model=%s(%s) engine=%s(%s)' % (
            res.verdict, res.kind, out['verdict'], out['kind']), res
    if res.verdict == 'failure':
        if res.kind != out['kind']:
            return False, 'kind model=%s engine=%s' % (res.kind, out['kind']), res
        return True, '', res
    eng_main = [key_of(d, 'bucket') for d in out['main']]
    eng_tier = [key_of(d, 'page') for d in out[tier_name]]
    if eng_main != res.main:
        a, b = set(eng_main), set(res.main)
        return False, 'main differs: engine-only %d model-only %d e.g. %s | %s' % (
            len(a - b), len(b - a), sorted(a - b)[:2], sorted(b - a)[:2]), res
    if eng_tier != res.tier:
        a, b = set(eng_tier), set(res.tier)
        return False, '%s differs: engine-only %d model-only %d e.g. %s | %s' % (
            tier_name, len(a - b), len(b - a), sorted(a - b)[:2], sorted(b - a)[:2]), res
    return True, '', res


def load(path):
    with open(path) as fh:
        return json.load(fh)


if __name__ == '__main__':
    import sys
    for p in sys.argv[1:]:
        ok, detail, res = compare(load(p))
        print(p, 'OK' if ok else 'MISMATCH ' + detail, res.verdict, res.kind)
