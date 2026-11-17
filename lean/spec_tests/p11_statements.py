#!/usr/bin/env python3
"""Exhaustive tests of the P11 statements (RebuildBound/Spec/P11.lean).

Mirrors the definitions of Spec/Prob/Network.lean on tiny instances: b stages,
n keys, bucket capacity C, every word assignment enumerated exactly (rational
arithmetic). A route is a lane-ordered bucket array; stage j + 1 moves each main
record to its bucket with bit j from its word and keeps, per destination, the
first C arrivals under a policy:

* "lane": arrival order (source bucket index, then lane): blind;
* "key": smallest keys first: blind;
* "peek": prefers records whose bit j + 1 is set: NOT blind (negative control).

Checks, for random pos, main sets, lo, R, P, L:
* P11a: condAvg_j(phi(final state)) == forestTest_j(state after j), for every j
  in [lo, b] and every h, with phi = termTest;
* P11b: wordAvg (rangeCount - L)+ <= wordAvg termTest(final state);
* P11ab: wordAvg (rangeCount - L)+ <= wordAvg firstArrivalTest(raw arrivals).
The negative control must violate P11a in some trials.

Usage: spec_tests/p11_statements.py [--trials N] [--seed S]
"""
from __future__ import annotations

import argparse
import itertools
import random
from fractions import Fraction
from functools import lru_cache
from math import comb

HALF = Fraction(1, 2)


def binom_pmf(n, p):
    return [comb(n, k) * p ** k * (1 - p) ** (n - k) for k in range(n + 1)]


class Instance:
    def __init__(self, rng, b, n, C, policy):
        self.b, self.n, self.C, self.policy = b, n, C, policy
        self.nodes = list(itertools.product((0, 1), repeat=b))
        self.pos = [tuple(rng.randint(0, 1) for _ in range(b)) for _ in range(n)]
        # main0: keys with lane order; tier: the rest (they start in the early list)
        keys = list(range(n))
        rng.shuffle(keys)
        k_main = rng.randint(max(0, n - 2), n)
        self.main0 = keys[:k_main]
        self.tier = sorted(keys[k_main:])
        self.lo = rng.randint(0, b - 1)
        self.R = tuple(rng.randint(0, 1) for _ in range(b))
        self.P = rng.randint(0, 3)
        self.L = rng.randint(0, 2)

    def dest(self, h, j, x):
        return tuple(h[x][i] if i < j else self.pos[x][i] for i in range(self.b))

    def route(self, h):
        """Main sets after each stage and the shed lists per stage (in order)."""
        buckets = {v: [] for v in self.nodes}
        for x in self.main0:
            buckets[self.pos[x]].append(x)
        mains = [set(self.main0)]
        sheds = [[]]
        for j in range(self.b):
            arrivals = {v: [] for v in self.nodes}
            for v in self.nodes:  # source bucket order, then lane
                for x in buckets[v]:
                    d = list(v)
                    d[j] = h[x][j]
                    arrivals[tuple(d)].append(x)
            new, shed = {}, []
            for v in self.nodes:
                arr = arrivals[v]
                if self.policy == 'key':
                    arr = sorted(arr)
                elif self.policy == 'peek':
                    nxt = j + 1 if j + 1 < self.b else j
                    arr = sorted(arr, key=lambda x: -h[x][nxt])
                new[v] = arr[:self.C]
                shed += arr[self.C:]
            buckets = new
            mains.append({x for v in self.nodes for x in buckets[v]})
            sheds.append(shed)
        return mains, sheds

    def early(self, h, mains, sheds):
        lst = list(self.tier)
        for j in range(1, self.lo + 1):
            lst += sheds[j]
        return lst[:self.P]

    def in_range(self, v):
        return all(v[i] == self.R[i] for i in range(self.lo, self.b))

    def net_state(self, h, mains, j):
        st = {}
        for v in self.nodes:
            st[(v, 0)] = sum(1 for x in mains[j] if self.dest(h, j, x) == v)
            st[(v, 1)] = sum(1 for x in mains[self.lo] - mains[j] if self.dest(h, j, x) == v)
        return st

    def range_count(self, h, mains, sheds):
        e = self.early(h, mains, sheds)
        late = mains[self.lo] - mains[self.b]
        return (sum(1 for x in e if self.in_range(h[x])) +
                sum(1 for x in late if self.in_range(h[x])))

    # --- backward tests ---------------------------------------------------
    def term_test(self, st):
        p = HALF ** (self.b - self.lo)
        s = sum(st[(v, 1)] for v in self.nodes if self.in_range(v))
        return sum(w * max(e + s - self.L, 0) for e, w in enumerate(binom_pmf(self.P, p)))

    def key(self, st):
        return tuple(st[(v, sl)] for v in self.nodes for sl in (0, 1))

    def forest_test(self, j, st):
        return self._forest(j, self.key(st))

    @lru_cache(maxsize=None)
    def _forest(self, j, k):
        st = dict(zip([(v, sl) for v in self.nodes for sl in (0, 1)], k))
        if j >= self.b:
            return self.term_test(st)
        # thin every coordinate by 1/2, add into bit j := R[j], cap every node
        coords = [q for q in st if st[q] > 0]
        total = Fraction(0)
        for ks in itertools.product(*[range(st[q] + 1) for q in coords]):
            w = Fraction(1)
            for q, kq in zip(coords, ks):
                w *= binom_pmf(st[q], HALF)[kq]
            thin = {q: 0 for q in st}
            for q, kq in zip(coords, ks):
                thin[q] = kq
            summed = {q: 0 for q in st}
            for (v, sl), c in thin.items():
                d = list(v)
                d[j] = self.R[j]
                summed[(tuple(d), sl)] += c
            capped = {}
            for v in self.nodes:
                m = summed[(v, 0)]
                capped[(v, 0)] = min(m, self.C)
                capped[(v, 1)] = summed[(v, 1)] + max(m - self.C, 0)
            total += w * self._forest(j + 1, self.key(capped))
        return total

    def first_arrival_test(self, N):
        st = {}
        for v in self.nodes:
            st[(v, 0)] = min(N[v], self.C)
            st[(v, 1)] = max(N[v] - self.C, 0)
        return self.forest_test(self.lo + 1, st)


def words(inst):
    per_key = list(itertools.product((0, 1), repeat=inst.b))
    return itertools.product(per_key, repeat=inst.n)


def agree_below(j, h, g):
    return all(h[x][i] == g[x][i] for x in range(len(h)) for i in range(j))


def trial(rng, policy):
    inst = Instance(rng, b=rng.randint(2, 3), n=rng.randint(2, 4), C=rng.randint(1, 2),
                    policy=policy)
    allh = list(words(inst))
    cache = {h: inst.route(h) for h in allh}
    # P11a at every j in [lo, b], for a few h
    a_ok = True
    for h in rng.sample(allh, min(4, len(allh))):
        mains, _ = cache[h]
        for j in range(inst.lo, inst.b + 1):
            comp = [g for g in allh if agree_below(j, h, g)]
            lhs = sum(inst.term_test(inst.net_state(g, cache[g][0], inst.b)) for g in comp) / len(comp)
            rhs = inst.forest_test(j, inst.net_state(h, mains, j))
            if lhs != rhs:
                a_ok = False
    # P11b and P11ab
    lhs = Fraction(0)
    mid = Fraction(0)
    rhs = Fraction(0)
    for h in allh:
        mains, sheds = cache[h]
        lhs += max(inst.range_count(h, mains, sheds) - inst.L, 0)
        mid += inst.term_test(inst.net_state(h, mains, inst.b))
        N = {v: sum(1 for x in range(inst.n) if inst.dest(h, inst.lo + 1, x) == v)
             for v in inst.nodes}
        rhs += inst.first_arrival_test(N)
    tot = len(allh)
    return a_ok, lhs / tot <= mid / tot, lhs / tot <= rhs / tot, (lhs / tot, mid / tot, rhs / tot)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--trials', type=int, default=40)
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    bad = 0
    for i in range(args.trials):
        policy = ('lane', 'key')[i % 2]
        a, b_, ab, vals = trial(rng, policy)
        if not (a and b_ and ab):
            bad += 1
            print(f'FAIL trial {i} ({policy}): P11a={a} P11b={b_} P11ab={ab} {[float(v) for v in vals]}')
    print(f'blind policies: {args.trials - bad}/{args.trials} pass')
    neg = 0
    for i in range(args.trials):
        a, _, _, _ = trial(rng, 'peek')
        neg += not a
    print(f'negative control (peeking policy): P11a violated in {neg}/{args.trials} (want > 0)')
    raise SystemExit(1 if bad or neg == 0 else 0)


if __name__ == '__main__':
    main()
