"""Minimum rebuild speeds and average tables per lookup under the storage
layout of Section 2.5, Deamortization (two regions of B units and one of B-1
per non-top level; the adopted first carry is moved into the middle region,
as Figure fig:deamortized-arena draws).

Extends hier.py with two knobs for a merge of digit j (j units of work):
  late  : share of the j units that can run only after the carry arrives
          (at least one unit, the carry's own); None is the appendix model
  prerouting=False : no work starts before the carry arrives
and with the model's count of queryable tables at one level: the published
partial table, from the adoption of a cycle's first carry until its last
merge publishes, plus every carry that has arrived but is not yet merged.

The minimum-speed search requires both no stalls and a repeating schedule:
publication times in the final two top-level cycles must differ by exactly
one cycle. A finite run without stalls alone can accept a speed below the
long-run requirement while a backlog is still growing.

Run with no arguments to print the table rows; `--check` reproduces the
unconstrained model (1, 2.25, 4.5 and 1.5, 11/6, 127/72 tables per level).
"""
import sys

from hier import Sim, big_stack, INF

LAYOUT = dict(policy="lease", f=2, W=2, adopt="move")
MODEL = dict(policy="model")
# (non-top levels, top cycles) per B: deep enough that the middle levels are
# in steady state; each configuration is checked against a deeper one.
DEPTH = {2: [(6, 10), (8, 20)], 4: [(4, 10), (5, 20)],
         8: [(3, 10), (4, 10), (5, 10)]}


class LayoutSim(Sim):
    def __init__(self, B, L1, s, late=None, prerouting=True, **kw):
        super().__init__(B, L1, s, **kw)
        self.late, self.prerouting = late, prerouting

    def d(self, l, n):
        if self.late is None and self.prerouting:
            return super().d(l, n)
        v = self.D[l][n]
        if v is not None:
            return v
        j = n % self.B + 1
        if j == 1:
            return super().d(l, n)
        c = n // self.B
        u = self.delta[l] / self.s
        a = self.arr(l, n)
        p = self.d(l, n - 1) if n > 0 else -INF
        if self.policy == "lease" and j == self.f and c >= self.W:
            p = max(p, self.ret(l + 1, c - self.W))
        late = j if not self.prerouting else max(self.late * j, 1.0)
        val = max(a, p + (j - late) * u) + late * u
        self.D[l][n] = val
        return val

    def tables_per_level(self, l, lo=0.3, hi=0.7):
        """Time-average queryable tables at level l over the middle window."""
        B, D = self.B, self.D[l]
        n_max = len(D)
        t0 = lo * n_max * self.delta[l]
        t1 = hi * n_max * self.delta[l]
        area = 0.0

        def add(a, b):
            nonlocal area
            a, b = max(a, t0), min(b, t1)
            if b > a:
                area += b - a

        for n in range(n_max):
            a = self.arr(l, n)
            if a < INF and D[n] is not None:
                add(a, D[n])                      # carry n waits until merged
        for c in range(n_max // B):
            first, last = D[c * B], D[c * B + B - 1]
            if first is not None and last is not None:
                add(first, last)                  # published partial table
        return area / (t1 - t0)


def periodicity_error(sim):
    """Largest normalized change in delay between the last two top cycles."""
    period = sim.B ** sim.L1
    error = 0.0
    for l, delays in enumerate(sim.D):
        stride = sim.B ** (sim.L1 - l)
        for n in range(len(delays) - stride, len(delays)):
            difference = delays[n] - delays[n - stride] - period
            error = max(error, abs(difference) / sim.delta[l])
    return error


def ok(B, L1, tc, s, **kw):
    sim = LayoutSim(B, L1, s, top_cycles=tc, **kw).run()
    return sim.worst() <= 1e-9 and periodicity_error(sim) <= 1e-7


def min_speed(B, L1, tc, **kw):
    lo, hi = (B + 1) / 2 - 1 / B - 1e-9, 3.0 * B
    if ok(B, L1, tc, lo, **kw):
        return lo
    for _ in range(40):
        mid = 0.5 * (lo + hi)
        if ok(B, L1, tc, mid, **kw):
            hi = mid
        else:
            lo = mid
    return hi


def tables(B, L1, tc, s, **kw):
    sim = LayoutSim(B, L1, s, top_cycles=tc, **kw).run()
    # The default horizons are multiples of five top cycles, so this window
    # spans complete cycles at every level and excludes startup/shutdown.
    return [sim.tables_per_level(l, lo=0.2, hi=0.8) for l in range(L1)]


def largest_late_share(B, L1, tc, s_target, **kw):
    lo, hi = 0.0, 1.0
    for _ in range(30):
        mid = 0.5 * (lo + hi)
        if ok(B, L1, tc, s_target, late=mid, **kw):
            lo = mid
        else:
            hi = mid
    return lo


def main():
    check = "--check" in sys.argv
    for B in (2, 4, 8):
        for L1, tc in DEPTH[B]:
            kw = MODEL if check else LAYOUT
            s = min_speed(B, L1, tc, **kw)
            q = tables(B, L1, tc, s * (1 + 1e-9), **kw)
            row = f"B={B} L1={L1} tc={tc}: s*={s:.4f} tables/level={[round(x, 3) for x in q]}"
            if not check:
                s0 = min_speed(B, L1, tc, prerouting=False, **kw)
                c = largest_late_share(B, L1, tc, s * (1 + 1e-6), **kw)
                row += f" no-prerouting s={s0:.4f} largest late share={c:.4f}"
            print(row, flush=True)


if __name__ == "__main__":
    big_stack(main)
