"""Analytical checks for the level-arena rebuild (src/oram/levelarena/DESIGN.md).

Receiver-owned inboxes, fixed partial banks, and consumer-side fused retagging.
This is a storage/routing model, not a timing or queueing simulator. Work counters
have distinct units; do not add radix tuples, AES bucket batches, and intersects
as though they had equal cost.

A level keeps ONE bank, for its odd partials; the even partials are built in
the level above's inbox slot under the forwarding lease and no even bank is
allocated, so a non-top level costs (3B-1)U_l counting its two inbox slots
above (DESIGN.md, "Geometry and storage bound").

The optional bank-first run (Params::bank_first) builds digits 2..r of every
cycle in that bank while it is idle, alternating the bank's top and base, and
ends on an odd digit; it costs one tier per level and no main storage.  check_bank_first restates its placement independently of the
engine's.

  python analysis/level_arena_model.py quick
  python analysis/level_arena_model.py       # broader scalar invariant checks
"""
from dataclasses import dataclass
from fractions import Fraction
import sys


def odd_split(j):
    if j < 1:
        raise ValueError("digit must be positive")
    e = (j & -j).bit_length() - 1
    return j >> e, e


def log2_exact(n):
    if n < 1 or n & (n - 1):
        raise ValueError("bucket count must be a power of two")
    return n.bit_length() - 1


@dataclass(frozen=True)
class Geometry:
    B: int = 8
    L: int = 4                  # includes the top
    D: int = 4
    r0: int = 8
    stash_buckets: int = 1      # online stash holds 64 * stash_buckets entries
    q: int = 2                 # complete dense prefixes, including active/retired

    bank_first: str = 'off'     # 'off' or 'no-clone' (Params::bank_first)

    def __post_init__(self):
        log2_exact(self.B)
        log2_exact(self.r0)
        log2_exact(self.stash_buckets)
        if self.B not in (2, 4, 8) or self.L < 2:
            raise ValueError("require B in {2,4,8}, L >= 2")
        if not 1 <= self.D <= 8 or self.q < 1:
            raise ValueError("require 1 <= D <= 8 and q >= 1")
        if self.D > self.B:  # the top is no wider than B: it moves 2D/(B+1) of a level's work
            raise ValueError("require D <= B")
        if self.bank_first not in ('off', 'no-clone'):
            raise ValueError("bank_first is off or no-clone")

    @property
    def Z(self):
        return 2 * self.r0 * self.stash_buckets

    def U(self, level):
        if not 1 <= level <= self.L:
            raise ValueError("level outside hierarchy")
        return self.Z * self.B ** (level - 1)

    @property
    def T(self):
        return self.D * self.U(self.L)

    @property
    def capacity_entries(self):
        return 32 * self.T

    @property
    def partial_buckets(self):
        total = 0
        for l in range(1, self.L):
            total += (self.B - 1) * self.U(l)
        return total

    def bank_run_end(self, level):
        """The last digit of level's bank-first run; 1 means none.

        Two consecutive partials share the (B-1)U bank only while
        (2r - 1) <= B - 1, so r <= B/2.  The run must end on an ODD digit,
        whose successor is even and goes to the lease."""
        if not 1 <= level < self.L or self.bank_first == 'off':
            return 1
        half = self.B // 2
        return half if half % 2 else half - 1

    def lease_digit(self, level):
        """The first digit of a cycle that needs an inbox of the level above."""
        return self.bank_run_end(level) + 1

    def placement(self, level, j):
        """(where, offset in units of U) for digit j below the top.

        where is 'odd' or 'run' (the bank's two occupancies), 'inbox' (the
        forwarding lease) or 'adopt'."""
        B, r = self.B, self.bank_run_end(level)
        if j == B:
            return 'inbox', 0
        if j == 1 and level >= 2 and B > 2:
            return 'adopt', 0
        if j % 2 == 0 and j > r:
            return 'inbox', 0
        top = r >= 2 and j <= r and (r - j) % 2 == 0
        return ('run' if j % 2 == 0 else 'odd'), ((B - 1 - j) if top else 0)

    @property
    def run_tiers(self):
        """Extra tier slots: one per level with a non-empty run."""
        return sum(1 for l in range(1, self.L) if self.bank_run_end(l) >= 2)

    @property
    def per_level_coefficient(self):
        # A non-top level in units of U_l, counting its two inbox slots above:
        # odd bank (B-1) + inboxes 2B.  The even partials are built inside one
        # of those inbox slots and cost nothing of their own.
        return 3 * self.B - 1

    @property
    def inbox_buckets(self):
        return sum(2 * self.U(l) for l in range(2, self.L + 1))

    @property
    def main_buckets(self):
        return self.partial_buckets + self.inbox_buckets + 2 * self.T

    @property
    def dense_ring_buckets(self):
        # q complete prefixes plus one being assembled (includes online stash).
        return (self.q + 1) * self.Z // 2

    @property
    def ratio(self):
        return Fraction(self.main_buckets, self.T)

    @property
    def ratio_closed_form(self):
        tail = 1 - Fraction(1, self.B ** (self.L - 1))
        return 2 + Fraction(self.per_level_coefficient,
                            (self.B - 1) * self.D) * tail

    @property
    def ratio_limit(self):
        return 2 + Fraction(self.per_level_coefficient, (self.B - 1) * self.D)


def ladder_main_buckets(fanouts, D, z):
    """Main buckets of an exact resolved ladder, in 64-slot buckets.

    `fanouts` are b_1..b_(L-1), one per non-top level (the half-fanout ladder
    is not uniform); `D` is the top digit and `z` is U_1.  U_(l+1) = b_l U_l.
    A non-top level keeps one odd bank, (b_l - 1) U_l, and the two inbox slots
    of the level above, each U_(l+1) wide; the top has two banks of D U_L.  The
    bank-first run adds a TIER per level, never a main bucket.  Returns the
    per-level U list, the partial/inbox/top split and the total M.
    """
    fanouts = list(fanouts)
    if not fanouts or any(log2_exact(b) < 1 for b in fanouts):
        raise ValueError("fanouts must be powers of two, at least 2")
    if not 1 <= D <= max(fanouts):
        raise ValueError("require 1 <= D <= the widest fanout")
    u = [z]
    for b in fanouts:
        u.append(u[-1] * b)
    partial = sum((b - 1) * u[i] for i, b in enumerate(fanouts))
    inbox = sum(2 * u[i + 1] for i in range(len(fanouts)))
    top = 2 * D * u[-1]
    return dict(U=u, partial=partial, inbox=inbox, top=top,
                M=partial + inbox + top)


def ladder_from_capacity(fanouts, D, capacity):
    """z = U_1 from the actual capacity: C = 32 T, T = D U_L."""
    span = 1
    for b in fanouts:
        span *= b
    t, rem = divmod(capacity, 32)
    u_top, rem2 = divmod(t, D)
    z, rem3 = divmod(u_top, span)
    if rem or rem2 or rem3:
        raise ValueError("capacity is not 32 * D * z * prod(fanouts)")
    return z


def bank_run_end_for(b, bank_first):
    """Geometry.bank_run_end for one level's own fanout b (1 means no run)."""
    if bank_first == 'off':
        return 1
    half = b // 2
    return half if half % 2 else half - 1


def ladder_slots(fanouts, D, z, tiers, bank_first='no-clone'):
    """Physical slot enumeration of the exact resolved ladder (allocation_reconcile.py).

    Returns per-level lists of (kind, main_buckets, tier_buckets).  `tiers` is
    the tier width per level (index 0 is level 1).  Below the top a level has
    its odd bank, a run-bank slot over the SAME buckets when its run is
    non-empty (bank-first: tier only, no main), and two inbox slots when
    l >= 2; the top has two banks of D U_L and two inboxes.  The sum of main
    buckets equals ladder_main_buckets(...)['M'].
    """
    fanouts = list(fanouts)
    levels = len(fanouts) + 1
    u = ladder_main_buckets(fanouts, D, z)['U']
    out = []
    for l in range(1, levels + 1):
        t = tiers[l - 1]
        slots = []
        if l < levels:
            b = fanouts[l - 1]
            slots.append(('odd', (b - 1) * u[l - 1], t))
            if bank_run_end_for(b, bank_first) >= 2:
                slots.append(('run', 0, t))
        else:
            slots += [('bank', D * u[l - 1], t), ('bank', D * u[l - 1], t)]
        if l >= 2:
            slots += [('inbox', u[l - 1], t), ('inbox', u[l - 1], t)]
        out.append(slots)
    return out


def synchronous_regions(fanouts, D, z, tiers):
    """The synchronous mode's per-level (region buckets, tier width): one
    table per level, U_(l+1) below the top and T at it; a tier is widened by
    the level below's width where the level adopts (2 <= l < L)."""
    fanouts = list(fanouts)
    u = ladder_main_buckets(fanouts, D, z)['U']
    levels = len(fanouts) + 1
    out = []
    for l in range(1, levels + 1):
        region = u[l] if l < levels else D * u[levels - 1]
        width = tiers[l - 1]
        if 2 <= l < levels:
            width = max(width, tiers[l - 2])
        out.append((region, width))
    return out


def family_destination(B, L, level, sequence):
    """Canonical terminal publication of a shared-nonce family.

    Sequences count accepted incoming carries, one-based; digit B forwards a
    full table to parent sequence sequence/B. Adoption at digit 1 is terminal.
    """
    if not (1 <= level <= L and sequence >= 1):
        raise ValueError("invalid family coordinate")
    while level < L and sequence % B == 0:
        sequence //= B
        level += 1
    return level, sequence


def family_id(level, sequence):
    if not 1 <= level < (1 << 15) or not 1 <= sequence < (1 << 48):
        raise ValueError("nonce coordinate exhausted")
    return (sequence << 15) | level


def absorb_counts(j, U, install_first=False):
    """Sparse non-top merge counters. j=1 adopts unless install_first is set.

    Copies/retags count bucket spans (fused in the implementation), butterfly
    and cross counters count bucket participations, radix counts tuples.
    Residual work, publication, and reader retirement are not priced here.
    """
    K = log2_exact(U)
    r, e = odd_split(j)
    if j == 1:
        # The binary install is a plain copy: digit 2 re-tags P_1 anyway.
        moved = U if install_first else 0
        return dict(copy=moved, retag=0, older_route=0, cross=0, radix_tuples=0)
    older_route = U * ((j - (1 << e)) * (K + e)
                       + sum((1 << u) * (K + u) for u in range(e)))
    return dict(copy=j * U, retag=j * U, older_route=older_route,
                cross=2 * U * ((1 << e) - 1),
                radix_tuples=(1 << e) * U if r > 1 else 0)


def check_bank_first():
    """The bank-first run's placement, restated independently of the engine."""
    expected = {(2, 'off'): (1, 2), (2, 'no-clone'): (1, 2),
                (4, 'off'): (1, 2), (4, 'no-clone'): (1, 2),
                (8, 'off'): (1, 2), (8, 'no-clone'): (3, 4)}
    for (B, mode), (end, lease) in expected.items():
        for L in range(2, 7):
            g = Geometry(B=B, L=L, D=min(B, 4), bank_first=mode)
            for l in range(1, L):
                assert g.bank_run_end(l) == end and g.lease_digit(l) == lease
                first = None
                for j in range(1, B + 1):
                    where, off = g.placement(l, j)
                    if first is None and where == 'inbox':
                        first = j
                    if where in ('odd', 'run'):
                        assert off + j <= B - 1                  # fits the bank
                        assert (where == 'odd') == (j % 2 == 1)  # parity picks
                    if j == 1:
                        continue
                    pw, poff = g.placement(l, j - 1)
                    if where in ('odd', 'run') and pw in ('odd', 'run'):
                        # P_(j-1) is live while P_j is written
                        assert pw != where
                        assert poff + (j - 1) <= off or off + j <= poff
                assert first == lease
            # One tier per run, no main bucket.
            assert g.run_tiers == (L - 1 if end >= 2 else 0)
            assert g.main_buckets == Geometry(B=B, L=L, D=min(B, 4)).main_buckets
    # A worked layout, in units of U.
    g8 = Geometry(B=8, L=3, D=2, bank_first='no-clone')
    assert [g8.placement(1, j) for j in (1, 2, 3)] == [('odd', 6), ('run', 0), ('odd', 4)]
    print("PASS bank-first run: parity-chosen ends, pair rule, lease digits")


def dense_counts(g):
    s = g.stash_buckets
    return dict(log_copy=g.Z // 2,
                dedup_pairs=s * s * g.r0 * (g.r0 - 1) // 2,
                scatter_source=g.Z // 2, scatter_destination=g.Z,
                retag=g.Z, route=g.Z * log2_exact(g.Z))


def top_shape(D):
    """The top's (r, e): binary when D is a power of two (one binary butterfly
    over the whole top, so no radix-eight kernel), whole digit otherwise."""
    if D & (D - 1) == 0:
        return 1, D.bit_length() - 1
    return D, 0


def top_counts(g):
    U = g.U(g.L)
    r, e = top_shape(g.D)
    return dict(prepare_copy=g.T, prepare_retag=g.T,
                prepare_route=g.T * (log2_exact(U) + e),
                prepare_radix_tuples=U if r > 1 else 0,
                incoming_retag=U, merge_tuples=U)


def top_digits_up_to(B):
    """Representative top digits with D <= B: trivial, binary, whole-digit."""
    return {2: (1, 2), 4: (1, 3, 4)}.get(B, (1, 4, 7))


def check_geometry_and_shapes():
    assert absorb_counts(1, 16, install_first=True) == dict(
        copy=16, retag=0, older_route=0, cross=0, radix_tuples=0)
    for B in (2, 4, 8):
        for L in range(2, 9):
            for D in top_digits_up_to(B):
                g = Geometry(B=B, L=L, D=D)
                assert g.ratio == g.ratio_closed_form
                assert g.ratio < g.ratio_limit
                for l in range(1, L):
                    U = g.U(l)
                    for j in range(1, B + 1):
                        r, e = odd_split(j)
                        assert j * U == r * (U << e)
                        if j == B:
                            assert j * U == g.U(l + 1)
                            continue
                        if j % 2 == 0:
                            # An even partial lands in the inbox above, which
                            # is one full table wide.
                            assert j * U <= g.U(l + 1)
                            continue
                        # An odd partial is the only thing a bank holds, so
                        # the bank is sized for the largest of them.
                        assert j * U <= (B - 1) * U
    print("PASS fixed-bank bounds, full-carry inbox sizes, finite-L memory sums")


def check_routing_counts():
    for U in (2, 16, 256, 4096):
        for j in range(2, 9):
            K = log2_exact(U)
            r, e = odd_split(j)
            # Enumerate the existing absorb's phase-1 blocks and phase-2 crosses.
            blocks = [(U << e, K + e)] * (r - 1)
            blocks += [(U << u, K + u) for u in reversed(range(e))]
            counts = absorb_counts(j, U)
            assert sum(n for n, _ in blocks) == (j - 1) * U
            assert counts['older_route'] == sum(n * k for n, k in blocks)
            assert counts['cross'] == sum(2 * U * (1 << u) for u in range(e))
    print("PASS absorb preparation/finish routing counts")


def check_families(prefixes):
    for B, L in ((2, 5), (4, 4), (8, 4)):
        roots = {}
        for l in range(1, L + 1):
            period = B ** (l - 1)
            for v in range(1, prefixes // period + 1):
                root = family_destination(B, L, l, v)
                fid = family_id(*root)
                assert fid not in roots or roots[fid] == root
                roots[fid] = root
                # All members end at exactly the same public prefix boundary.
                assert v * period == root[1] * B ** (root[0] - 1)
                if l < L and v % B == 0:
                    assert root == family_destination(B, L, l + 1, v // B)
        # Direct initialization at D full-top carry periods; no counter-unit mix.
        for D in top_digits_up_to(B):
            H = D * B ** (L - 1)
            for l in range(1, L):
                n = H // B ** (l - 1)
                assert n % B == 0
                assert family_destination(B, L, l, n) == (L, D)
                future = family_destination(B, L, l, n + 1)
                assert future[1] * B ** (future[0] - 1) > H
    print("PASS canonical families, shared window ends, initialization sequences")


def check_carry_addressing():
    # Consumer retagging changes stored tags but preserves the low K bits that
    # place a routed power-of-two carry. Test even/odd top radices as well.
    for K in range(1, 13):
        for e in range(4):
            for r in (1, 2, 3, 4, 5, 6, 7):
                low = K + e
                shift = 24
                for t in (0, 1, (1 << K) - 1, 0x123456789abcdef,
                          0xffffffffffffffff):
                    mapped = ((t & ((1 << low) - 1))
                              | (((t >> low) % r) << shift))
                    assert (mapped & ((1 << K) - 1)) == (t & ((1 << K) - 1))
    print("PASS consumer retagging preserves carry bucket placement")


def check_dense_dedup():
    # Scalar fixture for the chronological unit-pair algorithm. Each unit is
    # internally unique, but the same key may occur in any number of units.
    for r0 in (2, 4, 8):
        for s in (1, 16):
            units = [[((i * 37 + j) % (64 * s + 17), (i, j))
                      for j in range(64 * s)] for i in range(r0)]
            active = [[True] * len(unit) for unit in units]
            expected = {key: value for unit in units for key, value in unit}
            for fresh in range(1, r0):
                fresh_keys = {key for key, _ in units[fresh]}
                for old in range(fresh):
                    for j, (key, _) in enumerate(units[old]):
                        if key in fresh_keys:
                            active[old][j] = False
            survivors = [(key, value) for i, unit in enumerate(units)
                         for j, (key, value) in enumerate(unit) if active[i][j]]
            assert len(survivors) == len(expected)
            assert dict(survivors) == expected
    print("PASS dense unit-pair dedup retains exactly the newest values")


def print_tables():
    print("\nMain-table arena / capacity (excludes dense ring, tiers, masks, scratch)")
    print(" B  D   L=4 exact   large-L limit")
    for B in (2, 4, 8):
        for D in (d for d in (2, 3, 4, 7, 8) if B // 2 < d <= B):
            g = Geometry(B=B, D=D)
            print(f"{B:2} {D:2} {float(g.ratio):11.6f} {float(g.ratio_limit):15.6f}")
    print("\nDense carry per prefix, r0=8 (separate work units)")
    for s in (1, 16):
        g = Geometry(stash_buckets=s)
        print(f"stash_entries={64*s}, Z={g.Z}: {dense_counts(g)}")
    print("\nSparse absorb at U=16 (j=1 adoption; excludes residuals)")
    for j in range(1, 9):
        print(f"j={j}: {absorb_counts(j, 16)}")
    print("B=2 default j=1 install:", absorb_counts(1, 16, install_first=True))
    print("\nTop at B=8, L=4, D=4, Z=16:", top_counts(Geometry()))
    print("Top at B=8, L=4, D=7, Z=16:", top_counts(Geometry(D=7)))
    print("Top at B=8, L=4, D=8, Z=16:", top_counts(Geometry(D=8)))
    print("\nNo throughput, probe-average, or latency prediction is made.")


def main():
    if len(sys.argv) > 2 or (len(sys.argv) == 2 and sys.argv[1] != 'quick'):
        raise SystemExit("usage: level_arena_model.py [quick]")
    check_geometry_and_shapes()
    check_routing_counts()
    check_families(4096 if len(sys.argv) == 2 else 65536)
    check_carry_addressing()
    check_dense_dedup()
    check_bank_first()
    print_tables()


if __name__ == '__main__':
    main()
