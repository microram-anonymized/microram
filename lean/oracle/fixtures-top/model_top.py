#!/usr/bin/env python3
"""Lane-exact reference model of the TOP FINISH, written from ENGINE_TOP.md
(RebuildBound/Spec/Model/ENGINE_TOP.md).

`model(fixture) -> Result` is a pure function of the fixture's geometry, its
four input record lists (C_main, R, B_main, B_tier) and the word of every key.
It never looks at the engine's outputs.  `counters` records which paths a run
exercised (used for the coverage report); it has no effect on the result.
"""
import json
from collections import Counter

CAP = 64


class Fail(Exception):
    def __init__(self, kind):
        super().__init__(kind)
        self.kind = kind


class Result:
    def __init__(self, verdict, kind, main, tier, counters):
        self.verdict = verdict
        self.kind = kind
        self.main = main      # list of (bucket, lane, key, value, tombstone)
        self.tier = tier      # list of (page, lane, key, value, tombstone)
        self.counters = counters


def lowest_free(occupied, n):
    """The n smallest lanes not in `occupied`, ascending."""
    out = []
    lane = 0
    while len(out) < n:
        if lane not in occupied:
            out.append(lane)
        lane += 1
    return out


def lanes(bucket):
    """The records of a bucket (dict lane -> rec) in ascending lane order."""
    return [bucket[l] for l in sorted(bucket)]


class Stash:
    """A pool slot / tier: `pages` buckets of 64 lanes."""

    def __init__(self, pages):
        self.pages = [dict() for _ in range(pages)]
        self.capacity = pages * CAP

    def count(self):
        return sum(len(p) for p in self.pages)

    def append(self, recs):
        """Records in list order into the lowest free lanes of page 0, then
        page 1, ...  The caller has tested the capacity."""
        pending = list(recs)
        for page in self.pages:
            free = lowest_free(set(page), min(len(pending), CAP - len(page)))
            for lane, rec in zip(free, pending):
                page[lane] = rec
            pending = pending[len(free):]
        assert not pending


def model(f):
    g = f['geometry']
    T, U, D, K = g['T'], g['U'], g['D'], g['K']
    words = {w['key']: int(w['word'], 16) for w in f['words']}
    cnt = Counter()

    def home(r):
        return words[r['key']] & (T - 1)

    def way(r):
        return (words[r['key']] >> K) & (D - 1)

    # ---- inputs -----------------------------------------------------------
    C = [dict() for _ in range(T)]
    for r in f['inputs']['C_main']:
        C[r['bucket']][r['lane']] = r
    Rin = [dict() for _ in range(g['r_pages'])]
    for r in f['inputs']['R']:
        Rin[r['page']][r['lane']] = r
    B = [dict() for _ in range(U)]
    for r in f['inputs']['B_main']:
        B[r['bucket']][r['lane']] = r
    Bt = [dict() for _ in range(g['b_tier_pages'])]
    for r in f['inputs']['B_tier']:
        Bt[r['page']][r['lane']] = r

    try:
        return _run(g, T, U, D, K, home, way, C, Rin, B, Bt, cnt)
    except Fail as e:
        return Result('failure', e.kind, None, None, cnt)


def _run(g, T, U, D, K, home, way, C, Rin, B, Bt, cnt):
    dfs = bool(g['dfs'])
    I = g['range_index_bits']

    # ---- F1: pool dedup: R minus the keys of B's tier (every page, every
    # real lane, tombstones and unshadowed ones included) ---------------------
    bt_keys = {r['key'] for page in Bt for r in page.values()}
    R = []
    for page in Rin:
        p = {}
        for lane, r in page.items():
            if r['key'] in bt_keys:
                cnt['pool_dedup'] += 1
            else:
                p[lane] = r
        R.append(p)

    # ---- F2: the early (unshadowed) drop at the two reads of the pass: the
    # gather of R and the direct copy of B's tier ------------------------------
    def drop_flagged(page, counter):
        out = {}
        for lane, r in page.items():
            if r['tombstone'] and r['unshadowed']:
                cnt[counter] += 1
            else:
                out[lane] = r
        return out

    R = [drop_flagged(p, 'early_drop_R') for p in R]
    Btc = [drop_flagged(p, 'early_drop_Btier') for p in Bt]   # the direct copy

    # ---- F3: the range table of A's class -------------------------------------
    if dfs:
        pool = [r for page in R for r in lanes(page)]       # gather order
        nleaves = 1 << g['range_bits']
        leaves = [[] for _ in range(nleaves)]
        for r in pool:
            leaves[home(r) >> I].append(r)
        if pool:
            cnt['dfs_gathered'] += 1
        for l in leaves:
            if len(l) > CAP * g['range_groups']:
                cnt['fail_dfs'] += 1
                raise Fail('residual-dfs-partition')
        leaf_pages = [[{i: r for i, r in enumerate(l)}] for l in leaves]
    else:
        leaf_pages = [[dict(page) for page in R]]            # one "leaf": S_R pages

    def leaf_for(ci):
        """The pages of A's range table the offer of destination ci visits,
        in group order."""
        return leaf_pages[ci >> I] if dfs else leaf_pages[0]

    ins = Stash(g['merge_stash_pages'])

    # ---- F4: the sweep -----------------------------------------------------------
    for i in range(U):
        bkeys = {r['key'] for r in B[i].values()}
        for q in range(D):
            ci = i + q * U
            n0 = len(C[ci])
            C[ci] = {l: r for l, r in C[ci].items() if r['key'] not in bkeys}
            cnt['bmain_clear'] += n0 - len(C[ci])
        sheds = []
        for q in range(D):
            ci = i + q * U
            direction = [B[i][l] for l in sorted(B[i]) if way(B[i][l]) == q]
            dkeys = {r['key'] for r in direction}
            # ---- resolution -------------------------------------------------
            # (d) C's own tombstones
            n0 = len(C[ci])
            C[ci] = {l: r for l, r in C[ci].items() if not r['tombstone']}
            cnt['res_d'] += n0 - len(C[ci])
            # (a) + (c) over A's candidates naming ci
            for page in leaf_for(ci):
                for lane in sorted(page):
                    r = page[lane]
                    if home(r) != ci:
                        continue
                    if r['key'] in dkeys:
                        cnt['res_a'] += 1
                        del page[lane]
                    elif r['tombstone']:
                        cnt['res_c_leaf'] += 1
                        del page[lane]
            # (b) + (c) over B's tier candidates naming ci
            for page in Btc:
                cand = [page[l] for l in sorted(page) if home(page[l]) == ci]
                ckeys = {r['key'] for r in cand}
                n0 = len(C[ci])
                C[ci] = {l: r for l, r in C[ci].items() if r['key'] not in ckeys}
                cnt['res_b'] += n0 - len(C[ci])
                for lane in sorted(page):
                    if home(page[lane]) == ci and page[lane]['tombstone']:
                        cnt['res_c_tier'] += 1
                        del page[lane]
            # ---- B's direction merged into C[ci]: live records only -------------
            for r in direction:
                if r['tombstone']:
                    cnt['bmain_tombstone_skipped'] += 1
                    if r['unshadowed']:
                        cnt['early_drop_Bmain'] += 1
            src = [r for r in direction if not r['tombstone']]
            alloc = min(len(src), CAP - len(C[ci]))
            for lane, r in zip(lowest_free(set(C[ci]), alloc), src):
                C[ci][lane] = r
            sheds.append(src[alloc:])
            if q == D - 1:
                total = sum(len(s) for s in sheds)
                if ins.count() + total > ins.capacity:
                    cnt['fail_merge_stash'] += 1
                    raise Fail('fixed-merge-offers')
                flat = [r for s in sheds for r in s]
                if flat:
                    cnt['merge_stash_appends'] += len(flat)
                ins.append(flat)
            # ---- offers: A's pages, then B's tier pages -------------------------
            for page in leaf_for(ci):
                cand = [l for l in sorted(page) if home(page[l]) == ci]
                take = min(len(cand), CAP - len(C[ci]))
                for lane, l in zip(lowest_free(set(C[ci]), take), cand[:take]):
                    C[ci][lane] = page[l]
                    del page[l]
                cnt['a_leaf_absorb'] += take
            for page in Btc:
                cand = [l for l in sorted(page) if home(page[l]) == ci]
                take = min(len(cand), CAP - len(C[ci]))
                for lane, l in zip(lowest_free(set(C[ci]), take), cand[:take]):
                    C[ci][lane] = page[l]
                    del page[l]
                cnt['b_tier_absorb'] += take

    if ins.count() > CAP:
        cnt['merge_stash_second_page'] += 1
    cnt['shed_records'] = ins.count()

    # ---- F5: the epilogue ----------------------------------------------------------
    tier = Stash(g['out_tier_pages'])
    drained = []          # (rec, class) in drain order; class 'A' or 'B'
    range_buckets = ([p for pages in leaf_pages for p in pages] if dfs
                     else leaf_pages[0])
    for cls, bucket_list in (('A', range_buckets), ('B', Btc)):
        for page in bucket_list:
            L = lanes(page)
            if tier.count() + len(L) > tier.capacity:
                cnt['fail_drain1'] += 1
                raise Fail('residual-drain')
            tier.append(L)
            drained.extend((r, cls) for r in L)
    cls_of = {id(r): c for r, c in drained}
    cnt['drain1_records'] = tier.count()
    if tier.count() > CAP:
        cnt['out_tier_second_page_after_drain1'] += 1
    # leftover dedup
    shed_keys = {r['key'] for page in ins.pages for r in page.values()}
    tierB_keys = {r['key'] for r, c in drained if c == 'B'}
    for page in tier.pages:
        for lane in sorted(page):
            r = page[lane]
            if cls_of[id(r)] == 'A' and r['key'] in shed_keys:
                cnt['leftover_dedup_carry'] += 1
                del page[lane]
    for page in ins.pages:
        for lane in sorted(page):
            if page[lane]['key'] in tierB_keys:
                cnt['leftover_dedup_shed'] += 1
                del page[lane]
    # second drain: the merge stash
    for page in ins.pages:
        L = lanes(page)
        if tier.count() + len(L) > tier.capacity:
            cnt['fail_drain2'] += 1
            raise Fail('residual-drain')
        tier.append(L)

    if tier.count() > CAP:
        cnt['out_tier_second_page'] += 1

    # ---- F6: trailing tombstone drops ------------------------------------------------
    for b in range(T):
        n0 = len(C[b])
        C[b] = {l: r for l, r in C[b].items() if not r['tombstone']}
        cnt['trailing_drop_main'] += n0 - len(C[b])
    for page in tier.pages:
        for lane in list(page):
            if page[lane]['tombstone']:
                cnt['trailing_drop_tier'] += 1
                del page[lane]

    main = [(b, l, r['key'], r['value'], r['tombstone'])
            for b in range(T) for l, r in C[b].items()]
    tier_out = [(p, l, r['key'], r['value'], r['tombstone'])
                for p, page in enumerate(tier.pages) for l, r in page.items()]
    return Result('success', '', main, tier_out, cnt)


def load(path):
    with open(path) as fh:
        return json.load(fh)


def compare(f):
    """Run the model on fixture `f` and compare with the engine's outputs.
    Returns (ok, detail, result)."""
    res = model(f)
    eng = f['outputs']
    if res.verdict != eng['verdict']:
        return False, 'verdict model=%s(%s) engine=%s(%s)' % (
            res.verdict, res.kind, eng['verdict'], eng['kind']), res
    if res.verdict == 'failure':
        if res.kind != eng['kind']:
            return False, 'failing kind model=%s engine=%s' % (res.kind, eng['kind']), res
        return True, '', res

    def norm(recs, where):
        return sorted((r[where], r['lane'], r['key'], r['value'], r['tombstone'])
                      for r in recs)
    ok_main = sorted(res.main) == norm(eng['main'], 'bucket')
    ok_tier = sorted(res.tier) == norm(eng['tier'], 'page')
    if ok_main and ok_tier:
        return True, '', res
    m, e = set(res.main), set(norm(eng['main'], 'bucket'))
    tm, te = set(res.tier), set(norm(eng['tier'], 'page'))
    detail = 'main %s tier %s | main model-only %s engine-only %s | tier model-only %s engine-only %s' % (
        ok_main, ok_tier, sorted(m - e)[:3], sorted(e - m)[:3],
        sorted(tm - te)[:3], sorted(te - tm)[:3])
    return False, detail, res


if __name__ == '__main__':
    import sys
    allok = True
    for p in sys.argv[1:]:
        ok, detail, res = compare(load(p))
        print(p, 'OK' if ok else 'MISMATCH', detail, dict(res.counters))
        allok &= ok
    sys.exit(0 if allok else 1)
