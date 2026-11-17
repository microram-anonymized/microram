"""Convergence in depth at B = 8 and the appendix's share variants under the
layout of Section 2.5 (see layout_speeds.py)."""
from hier import big_stack, INF
from layout_speeds import LayoutSim, LAYOUT, min_speed, tables, ok

class ShareSim(LayoutSim):
    """late share per digit j (list indexed by j - 2, for j = 2..B)."""
    def __init__(self, B, L1, s, shares, **kw):
        super().__init__(B, L1, s, late=0.0, **kw)
        self.shares = shares
    def d(self, l, n):
        j = n % self.B + 1
        if j >= 2:
            self.late = self.shares[j - 2]
        return super().d(l, n)

def min_speed_shares(B, L1, tc, shares):
    lo, hi = 4.0, 12.0
    for _ in range(36):
        mid = 0.5 * (lo + hi)
        sim = ShareSim(B, L1, mid, shares, top_cycles=tc, **LAYOUT).run()
        if sim.worst() <= 1e-9:
            hi = mid
        else:
            lo = mid
    return hi

def main():
    for L1, tc in ((5, 2),):
        s = min_speed(8, L1, tc, **LAYOUT)
        print(f"B=8 L1={L1} tc={tc}: s*={s:.4f} tables/level={[round(x,3) for x in tables(8, L1, tc, s*(1+1e-9), **LAYOUT)]}", flush=True)
    for name, sh in (("half", [0.5]*7),
                     ("level 4 touches", [.49,.36,.33,.28,.27,.25,.26]),
                     ("level 5 touches", [.37,.28,.25,.23,.22,.21,.22]),
                     ("level 6 touches", [.30,.23,.21,.19,.19,.18,.18])):
        print(f"B=8 shares {name}: s={min_speed_shares(8, 3, 20, sh):.4f}", flush=True)

if __name__ == "__main__":
    big_stack(main)
