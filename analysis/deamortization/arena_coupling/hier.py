"""Hierarchy simulator for the deamortized B-ary schedule, with or without
explicit storage.

Time unit: one level-1 carry interval.  Level l (0-based, l < L1 non-top,
l == L1 the top) has interval B**l.  Every non-top level has its own worker
of speed s units per its own interval, so one unit of work at level l takes
B**l / s.

Per-level merge rule (the appendix model, deamortization_analysis.py):
  digit 1 (k = 0): adopt at zero cost, D_n = max(a_n, D_{n-1})
  digit j >= 2   : pre-route j-1 units from p_n = max(D_{n-1}, storage wait),
                   D_n = max(a_n, p_n + (j-1)u) + u
where a_n is the arrival of carry n (level 0: n; level l: publication of
level l-1's digit-B merge of cycle n).

Policies (how storage constrains p_n):
  'model'    : none; a stall is any D^l_n > a^l_{n+2} at any non-top level
               (one later carry may wait, a second stalls).
  'lease'    : the paper's / code's layout.  Two full regions rotate as the
               outgoing slot; the first digit of a cycle that needs the full
               working region is f (2 in the paper; 2, or 4 with the code's
               bank-first run at B = 8).  Cycle c's digit-f merge starts only
               after the next level retires the table that cycle c-W left in
               that region (W = 2 full regions; W = 3 adds a full region).
  'fungible' : cap units (of the level's own carry size) of perfectly
               divisible storage, the most optimistic use of the same amount:
               a merge of digit j starts only when cap - (partial) - j units
               are not held by outgoing tables the next level still needs.
For storage policies a stall is level 1 failing to retire carry n by n + q
(the online-stash ring), as in the model.

Retirement of outgoing table m by the next level (adoption semantics):
  digit >= 2 there         : when the merge that consumes it publishes;
  digit 1, 'pointer'       : the consumer adopts it in place (code, b > 2), so
                             it is retired when the consumer's digit-2 merge
                             publishes;
  digit 1, 'move'          : the table is moved into the consumer's storage at
                             zero cost when adopted (Figure fig:deamortized-
                             arena draws A_1 in the consumer's middle region);
  digit 1, 'install'       : as 'move' but the move costs install_cost units
                             after arrival (code, b = 2).
The top retires each carry on arrival (+ top_delay of its own intervals).
"""
from __future__ import annotations

import math
import sys
import threading

INF = float("inf")


class Sim:
    def __init__(self, B, L1, s, policy="model", top_cycles=4, adopt="pointer",
                 f=2, W=2, cap=None, install_cost=0.0, top_delay=0.0, q=2.0,
                 level0_adopt_free=True):
        self.B, self.L1, self.s = B, L1, s
        self.policy, self.adopt, self.f, self.W = policy, adopt, f, W
        self.cap = cap if cap is not None else 3 * B - 1
        self.install_cost, self.top_delay, self.q = install_cost, top_delay, q
        self.delta = [float(B ** l) for l in range(L1 + 1)]
        self.counts = [top_cycles * B ** (L1 - l) for l in range(L1)]
        self.D = [[None] * c for c in self.counts]
        self.Pst = [[None] * c for c in self.counts]  # merge start (output allocated)

    # arrival of carry n at level l (l may be the top, L1)
    def arr(self, l, n):
        if l == 0:
            return float(n)
        src = (n + 1) * self.B - 1
        if src >= self.counts[l - 1]:
            return INF
        return self.d(l - 1, src)

    # time the producer's region holding carry m of level l is free again
    def ret(self, l, m):
        if m < 0:
            return -INF
        if l == self.L1:
            return self.arr(l, m) + self.top_delay * self.delta[l]
        if m >= self.counts[l]:
            return INF
        j = m % self.B + 1
        if j == 1 and l > 0 and self.adopt == "pointer" and self.B > 1:
            return self.d(l, m + 1) if m + 1 < self.counts[l] else INF
        return self.d(l, m)

    def outgoing_retire(self, l, c, m):
        """Retirement of level l's outgoing table m, seen from level l's cycle c."""
        if m < 0:
            return -INF
        # A pointer-adopted table m with m + 1 == c is retired only after the
        # consumer's next merge, whose carry is cycle c's own output: after
        # every merge of cycle c starts.
        if (l + 1 < self.L1 + 1 and l + 1 != self.L1 and self.adopt == "pointer"
                and m % self.B == 0 and m + 1 >= c):
            return INF
        if m >= c:
            return INF
        return self.ret(l + 1, m)

    def fungible_wait(self, l, n, j, c):
        B = self.B
        if j == 1:
            held = 0  # previous partial already retired
            need = 1 if (l == 0 or self.adopt in ("move", "install")) else 0
            mlist = range(max(0, c - 5), c)
        else:
            if j == 2:
                held = 1 if (l == 0 or self.adopt in ("move", "install")) else 0
            else:
                held = j - 1
            need = j
            mlist = range(max(0, c - 5), c)
        room = self.cap - held - need
        if room < 0:
            return INF
        K = int(math.floor(room / B + 1e-12))
        R = sorted((self.outgoing_retire(l, c, m) for m in mlist), reverse=True)
        if len(R) <= K:
            return -INF
        return R[K]

    def d(self, l, n):
        v = self.D[l][n]
        if v is not None:
            return v
        B = self.B
        j = n % B + 1
        c = n // B
        u = self.delta[l] / self.s
        a = self.arr(l, n)
        prev = self.d(l, n - 1) if n > 0 else -INF
        if j == 1:
            w = -INF
            if self.policy == "fungible":
                w = self.fungible_wait(l, n, j, c)
            st = max(a, prev, w)
            if l > 0 and self.adopt == "install":
                val = st + self.install_cost * u
            else:
                val = st
        else:
            p = prev
            if self.policy == "lease":
                if j == self.f and c >= self.W:
                    p = max(p, self.ret(l + 1, c - self.W))
            elif self.policy == "fungible":
                p = max(p, self.fungible_wait(l, n, j, c))
            self.Pst[l][n] = p
            val = max(a, p + (j - 1) * u) + u
        self.D[l][n] = val
        return val

    def run(self):
        for n in range(self.counts[0]):
            self.d(0, n)
        for l in range(self.L1):
            for n in range(self.counts[l]):
                self.d(l, n)
        return self

    def worst(self):
        """Largest violation measure; <= 0 means no stall."""
        if self.policy == "model":
            w = -INF
            for l in range(self.L1):
                for n in range(self.counts[l] - 2):
                    a2 = self.arr(l, n + 2)
                    w = max(w, (self.D[l][n] - a2) / self.delta[l])
            return w
        return max(self.ret(0, n) - n - self.q for n in range(self.counts[0] - 1))

    def retention(self, l):
        """Max over carries of (retire - arrival) at level l, in level-l intervals."""
        out = -INF
        for n in range(self.counts[l] - 1):
            r = self.ret(l, n)
            a = self.arr(l, n)
            if r < INF and a < INF:
                out = max(out, (r - a) / self.delta[l])
        return out


def ok(B, L1, s, **kw):
    sim = Sim(B, L1, s, **kw).run()
    return sim.worst() <= 1e-9


def min_speed(B, L1, lo=0.5, hi=None, iters=40, **kw):
    hi = hi if hi is not None else 3.0 * B
    if not ok(B, L1, hi, **kw):
        return INF
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if ok(B, L1, mid, **kw):
            hi = mid
        else:
            lo = mid
    return hi


def big_stack(fn):
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(255 * 1024 * 1024)
    out = {}

    def target():
        out["v"] = fn()

    t = threading.Thread(target=target)
    t.start()
    t.join()
    return out.get("v")
