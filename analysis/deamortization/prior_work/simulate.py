#!/usr/bin/env python3
"""Discrete-event model for GO96-style deamortized rebuild scheduling.

The model compares two persistent-buffer organizations.

TwoBuf
------
Each regular level has two full-size buffers:
  1. a full table/carry that may still be pinned while the next level absorbs it;
  2. one under-construction full-size buffer for the next local generation.

The first incoming carry remains queryable at the lower level while early rebuild
work is performed.  The second carry is allowed to arrive *before* the early work
finishes: it is attached to the same construction, and the remaining early work
and second-carry-dependent work are completed afterwards.  Thus there is no
artificial deadline requiring phase 1 to finish before carry 2.

2.5Buf / ThreeBuf
-----------------
A regular level reserves:
  1. one full outgoing carry (1.0 buffer),
  2. the first incoming carry as an immediately published half-full table
     (0.5 buffer; ThreeBuf may reserve a full slot for this role), and
  3. one full rebuild/output buffer (1.0 buffer).

The first carry is transferred/published immediately using the shallow-copy
ownership convention, so its lower-level source can be released immediately.
Early rebuild work then reads that published table and writes the rebuild buffer.
The second carry can arrive before early work finishes; its source stays pinned
until the final combined table is published.

Normalization
-------------
At level l, one incoming carry has size U_l = 2^l and two carries form one full
local table.  Total work per local generation is W_l = 2 U_l.  Rebuild speed
s=1 therefore means exactly one unit of rebuild work per logical-access time,
i.e. the long-run throughput of the amortized baseline.

alpha is the fraction of W_l that becomes available after carry 1.  The rest can
only be completed after carry 2 arrives.  Early work may spill past carry 2.
Memory movement itself is treated as free, as in the accompanying note.

The simulator reproduces the analytic no-stall thresholds

    TwoBuf:  s >= max(3/2, 6(1-alpha))
    2.5Buf:  s >= max(1,   2(1-alpha))

Probe accounting is logical rather than physical: every live carry is one
searchable table.  After carry 2 arrives and before the combined table is
published, carry 1 and carry 2 therefore count as TWO probes.  The lower-level
logical table can be retired by a shallow ownership change even when the carry's
backing storage remains physically pinned.  For a common (alpha, speed), both
buffer organizations have the same probe count whenever TwoBuf is feasible:

    f(alpha,s) = max(1, 2 alpha / s) + 2(1-alpha)/s
    qbar(alpha,s) = f(alpha,s) - 1/2.

The binary non-deamortized hierarchy has only half of its levels active on
average, so the total lookup overhead relative to that baseline is 2*qbar.

The same program also models a proposed power-of-two branching factor B.  A
regular B-ary level has states 0,...,B-1, a state-k table contains k carry
units, and the k -> k+1 merge has total work k+1 (zero at k=0).  The main
branching model is streamable: k units of current-table work may run before the
next carry arrives and one final unit depends on that carry.  One future carry
may wait in the predecessor's outgoing slot.  This makes B=2 coincide with the
2.5-buffer binary schedule at alpha=1/2.  The program reports space, rebuild
thresholds, and lookup ratios normalized to the binary non-deamortized L2/2
baseline.
"""

from dataclasses import dataclass, field
from typing import Optional, List, Dict
import argparse
import heapq
import itertools
import math
import sys
from pathlib import Path

DEAMORTIZATION_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(DEAMORTIZATION_DIR))
from deamortization_closed_form import average_at_minimum_exact, minimum_speed_exact


@dataclass
class Source:
    origin_level: Optional[int]
    buffer_id: Optional[int]


@dataclass
class Buffer:
    amount: float
    role: str


@dataclass
class Generation:
    first_src: Source
    second_src: Optional[Source]
    first_buf: int              # TwoBuf: build buffer; 2.5Buf: published half
    output_buf: Optional[int]   # 2.5Buf only
    early_remaining: float
    late_remaining: float
    second_arrived: bool = False
    early_done: bool = False
    token: int = 0


@dataclass
class Level:
    capacity: float
    incoming: List[Source] = field(default_factory=list)
    buffers: Dict[int, Buffer] = field(default_factory=dict)
    generation: Optional[Generation] = None
    last_work_update: float = 0.0


class Simulator:
    def __init__(self, speed: float, alpha: float, scheme: str,
                 levels: int = 10, accesses: int = 10_000):
        if scheme not in ("two", "2.5", "three"):
            raise ValueError("scheme must be 'two', '2.5', or 'three'")
        if speed <= 0:
            raise ValueError("speed must be positive")
        if not 0.0 <= alpha <= 1.0:
            raise ValueError("alpha must lie in [0,1]")

        self.speed = speed
        self.alpha = alpha
        self.scheme = scheme
        self.levels_n = levels
        self.accesses = accesses

        # ThreeBuf has the same schedule as 2.5Buf; it merely reserves a full
        # slot for the half-full published first-carry table.
        cap = {"two": 2.0, "2.5": 2.5, "three": 3.0}[scheme]
        self.levels = [Level(cap) for _ in range(levels)]

        self.events = []
        self.serial = itertools.count()
        self.buffer_ids = itertools.count()
        self.now = 0.0
        self.stall_time = None

        # Completions have priority 0 and fixed-rate external arrivals priority 2,
        # so a buffer released exactly at a deadline is usable at that deadline.
        for t in range(accesses):
            heapq.heappush(
                self.events,
                (float(t), 2, next(self.serial), "external", 0, None),
            )

    def used(self, level: int) -> float:
        return sum(b.amount for b in self.levels[level].buffers.values())

    def alloc(self, level: int, amount: float, role: str) -> Optional[int]:
        lv = self.levels[level]
        if self.used(level) + amount > lv.capacity + 1e-10:
            return None
        bid = next(self.buffer_ids)
        lv.buffers[bid] = Buffer(amount, role)
        return bid

    def schedule(self, when: float, kind: str, level: int, token: int):
        heapq.heappush(
            self.events,
            (when, 0, next(self.serial), kind, level, token),
        )

    def free_source(self, src: Optional[Source]):
        if src is None or src.origin_level is None:
            return
        lower = self.levels[src.origin_level]
        if src.buffer_id in lower.buffers:
            del lower.buffers[src.buffer_id]
            self.try_accept(src.origin_level)

    def offer(self, level: int, src: Source):
        if level >= self.levels_n:
            # Infinite sink above the simulated hierarchy.
            self.free_source(src)
            return
        self.levels[level].incoming.append(src)
        self.try_accept(level)

    def update_work(self, level: int):
        lv = self.levels[level]
        g = lv.generation
        if g is None:
            lv.last_work_update = self.now
            return

        dt = self.now - lv.last_work_update
        if dt <= 0:
            return
        budget = self.speed * dt

        # With one aggregate rebuild-throughput budget, the optimal policy is to
        # spend all pre-carry-2 time on early work.  After carry 2 arrives, early
        # and late work may be interleaved arbitrarily; the final completion time
        # depends only on their total remaining work.  We process early first for
        # bookkeeping simplicity.
        take = min(budget, g.early_remaining)
        g.early_remaining -= take
        budget -= take
        if g.early_remaining <= 1e-10:
            g.early_remaining = 0.0
            g.early_done = True

        if g.second_arrived and g.early_done and budget > 0:
            take = min(budget, g.late_remaining)
            g.late_remaining -= take

        lv.last_work_update = self.now

    def schedule_next_work_event(self, level: int):
        lv = self.levels[level]
        g = lv.generation
        if g is None:
            return

        g.token += 1
        token = g.token
        if g.early_remaining > 1e-10:
            self.schedule(
                self.now + g.early_remaining / self.speed,
                "early_done", level, token,
            )
        elif g.second_arrived:
            self.schedule(
                self.now + g.late_remaining / self.speed,
                "final_done", level, token,
            )

    def start_generation(self, level: int) -> bool:
        lv = self.levels[level]
        if lv.generation is not None or not lv.incoming:
            return False

        U = 2 ** level
        W = 2 * U

        if self.scheme == "two":
            build = self.alloc(level, 1.0, "under-construction")
            if build is None:
                return False
            first = lv.incoming.pop(0)
            g = Generation(
                first_src=first,
                second_src=None,
                first_buf=build,
                output_buf=None,
                early_remaining=self.alpha * W,
                late_remaining=(1.0 - self.alpha) * W,
            )
        else:
            # Publish/transfer carry 1 immediately.  2.5Buf uses only half a
            # full-buffer slot; ThreeBuf reserves a full slot for the same data.
            published_amount = 0.5 if self.scheme == "2.5" else 1.0
            published = self.alloc(level, published_amount, "published-first")
            if published is None:
                return False
            output = self.alloc(level, 1.0, "rebuild-output")
            if output is None:
                del lv.buffers[published]
                return False

            first = lv.incoming.pop(0)
            # Ownership/shallow-copy transfer: the lower-level source is no
            # longer separately resident once the first carry is published here.
            self.free_source(first)
            g = Generation(
                first_src=first,
                second_src=None,
                first_buf=published,
                output_buf=output,
                early_remaining=self.alpha * W,
                late_remaining=(1.0 - self.alpha) * W,
            )

        if g.early_remaining <= 1e-10:
            g.early_remaining = 0.0
            g.early_done = True

        lv.generation = g
        lv.last_work_update = self.now
        self.schedule_next_work_event(level)
        return True

    def attach_second_carry(self, level: int) -> bool:
        lv = self.levels[level]
        g = lv.generation
        if g is None or g.second_src is not None or not lv.incoming:
            return False

        # Key correction relative to the earlier model: carry 2 can be accepted
        # even if the alpha-fraction early work is unfinished.  No new full-size
        # local buffer is needed; TwoBuf uses the existing construction buffer,
        # while 2.5/ThreeBuf already reserved the full rebuild/output buffer.
        self.update_work(level)
        g.second_src = lv.incoming.pop(0)
        g.second_arrived = True
        self.schedule_next_work_event(level)
        return True

    def try_accept(self, level: int):
        changed = True
        while changed and self.stall_time is None:
            changed = False
            if self.start_generation(level):
                changed = True
            if self.attach_second_carry(level):
                changed = True

    def finish_generation(self, level: int, token: int):
        lv = self.levels[level]
        g = lv.generation
        if g is None or token != g.token:
            return

        self.update_work(level)
        if (not g.second_arrived or g.early_remaining > 1e-8
                or g.late_remaining > 1e-8):
            return  # stale completion event

        if self.scheme == "two":
            # Neither source is separately published at this level.
            self.free_source(g.first_src)
            self.free_source(g.second_src)
            out = g.first_buf
            lv.buffers[out].role = "full-output"
        else:
            # Carry 1 was transferred/published immediately; carry 2 remained a
            # source until the combined table became queryable.
            self.free_source(g.second_src)
            if g.first_buf in lv.buffers:
                del lv.buffers[g.first_buf]
            out = g.output_buf
            lv.buffers[out].role = "full-output"

        lv.generation = None
        lv.last_work_update = self.now
        self.offer(level + 1, Source(level, out))
        self.try_accept(level)

    def run(self) -> bool:
        while self.events and self.stall_time is None:
            time, _prio, _serial, kind, level, token = heapq.heappop(self.events)
            self.now = time

            if kind == "external":
                src = Source(None, None)
                self.offer(0, src)
                # A fixed-rate external carry has nowhere else to wait.  Internal
                # carries may wait by pinning the lower-level source buffer.
                if src in self.levels[0].incoming:
                    self.stall_time = self.now

            elif kind == "early_done":
                lv = self.levels[level]
                g = lv.generation
                if g is None or token != g.token:
                    continue
                self.update_work(level)
                self.schedule_next_work_event(level)

            elif kind == "final_done":
                self.finish_generation(level, token)

        return self.stall_time is None


def completion_factor(alpha: float, speed: float) -> float:
    """Publication time / carry interval U for one local generation."""
    return max(1.0, 2.0 * alpha / speed) + 2.0 * (1.0 - alpha) / speed


def avg_queryable_tables_per_level(alpha: float, speed: float) -> float:
    """Analytic average number of searchable carry tables at one level."""
    return completion_factor(alpha, speed) - 0.5


def explicit_probe_average(alpha: float, speed: float, epochs: int = 1000) -> float:
    """
    Integrate an explicit one-level lookup timeline.

    Time is normalized so one carry interval U=1 and one two-carry epoch has
    length 2.  In each epoch:

      * C1 is queryable from time 0 until publication;
      * C2 is queryable from time 1 until publication;
      * while both are live they count as TWO table probes;
      * publication subsumes both into the output, which is immediately handed
        to the next level and therefore is not double-counted at this level.

    The function deliberately counts logical searchable runs, independently of
    where their backing memory is physically owned.
    """
    f = completion_factor(alpha, speed)
    if f > 2.0 + 1e-12:
        # A generation overlaps the next C1 at this level; this simple timeline
        # is intended for the no-stall region only.
        return float("inf")

    total_area = 0.0
    for _ in range(epochs):
        # One table C1 lives over [0, f].
        total_area += f
        # A second, distinct table C2 lives over [1, f] when f > 1.
        total_area += max(0.0, f - 1.0)
    return total_area / (2.0 * epochs)


def analytic_threshold(alpha: float, scheme: str) -> float:
    if scheme == "two":
        return max(1.5, 6.0 * (1.0 - alpha))
    return max(1.0, 2.0 * (1.0 - alpha))


def min_probe_envelope(speed: float) -> float:
    """Best qbar if alpha may be retuned at a fixed aggregate speed."""
    if speed < 1.0:
        return float("inf")
    if speed < 2.0:
        return 2.0 / speed - 0.5
    return 0.5


def find_threshold(alpha: float, scheme: str, levels: int, accesses: int) -> float:
    lo, hi = 0.05, 8.0
    for _ in range(50):
        mid = (lo + hi) / 2.0
        if Simulator(mid, alpha, scheme, levels, accesses).run():
            hi = mid
        else:
            lo = mid
    return hi


def print_probe_curve(alpha: float = 0.75, max_speed: float = 5.0,
                      step: float = 0.25):
    """
    Print a SAME-(alpha,s) comparison of online lookup cost.

    The schemes have identical logical probe counts whenever both schedules are
    feasible.  Their difference is the feasible speed range.  By default we use
    alpha=3/4: 2.5Buf is feasible from s=1, while TwoBuf becomes feasible at
    s=3/2 and then lies exactly on top of the 2.5Buf curve.
    """
    print("speed,two_qbar,2.5_qbar,two_overhead_vs_binary_amortized,2.5_overhead_vs_binary_amortized,explicit_qbar,retuned_envelope")
    s = 1.0
    while s <= max_speed + 1e-12:
        analytic = avg_queryable_tables_per_level(alpha, s)
        explicit = explicit_probe_average(alpha, s)
        if math.isfinite(explicit) and abs(explicit - analytic) > 1e-9:
            raise AssertionError((s, explicit, analytic))
        q = explicit
        two = q if s + 1e-12 >= analytic_threshold(alpha, "two") else float("nan")
        half = q if s + 1e-12 >= analytic_threshold(alpha, "2.5") else float("nan")
        env = min_probe_envelope(s)
        two_ov = 2.0 * two if math.isfinite(two) else float("nan")
        half_ov = 2.0 * half if math.isfinite(half) else float("nan")
        print(
            f"{s:.6f},{two:.8f},{half:.8f},{two_ov:.8f},{half_ov:.8f},"
            f"{explicit:.8f},{env:.8f}"
        )
        s += step



# ---------------------------------------------------------------------------
# Larger-branching-factor model
# ---------------------------------------------------------------------------

def validate_branching_factor(B: int) -> None:
    if B < 2 or (B & (B - 1)) != 0:
        raise ValueError("B must be a power of two and at least 2")


def branching_average_work(B: int) -> float:
    """
    Average merge work per incoming-carry interval.

    A level cycles through states k=0,...,B-1.  State 0 accepts the first
    carry by a shallow ownership transfer at zero rebuild work.  For k>=1,
    merging a state-k table with one incoming carry has total work k+1.
    """
    validate_branching_factor(B)
    return (B + 1.0) / 2.0 - 1.0 / B


def branching_space_ratio(B: int, rho: float = 0.0,
                           levels: Optional[int] = None) -> float:
    r"""
    Persistent space divided by the top-level slot capacity N.

    The model requested in the report uses

        top level:       2 + rho/B slots,
        regular level:   3 - 1/B local slots.

    Successive lower-level slot capacities shrink geometrically by 1/B.
    If ``levels`` is omitted, use the deep-hierarchy geometric-series limit.
    If supplied, ``levels`` counts the top level as one level.
    """
    validate_branching_factor(B)
    if rho < 0:
        raise ValueError("rho must be nonnegative")

    if levels is None:
        lower_slot_sum = 1.0 / (B - 1.0)
    else:
        if levels < 1:
            raise ValueError("levels must be at least 1")
        if levels == 1:
            lower_slot_sum = 0.0
        else:
            lower_slot_sum = (1.0 - B ** (-(levels - 1))) / (B - 1.0)

    return 2.0 + rho / B + (3.0 - 1.0 / B) * lower_slot_sum


def branching_levels_factor(B: int) -> float:
    """Number of B-ary levels divided by the number of binary levels."""
    validate_branching_factor(B)
    return 1.0 / math.log2(B)


def branching_amortized_probes_per_level(B: int) -> float:
    """Non-deamortized public-occupancy average: state is nonzero (B-1)/B."""
    validate_branching_factor(B)
    return (B - 1.0) / B


def branching_amortized_probe_ratio_to_binary(B: int) -> float:
    """
    Total average probes divided by the binary non-deamortized baseline L2/2.
    """
    return (2.0 * branching_amortized_probes_per_level(B)
            / math.log2(B))


def branching_streamable_no_stall(B: int, speed: float,
                                   cycles: int = 4000,
                                   tol: float = 1e-9) -> bool:
    r"""
    Check the proposed B-ary schedule under a streamable merge model.

    Normalize the incoming-carry interval U to 1.  Let D_n be the publication
    time after processing carry n, and k=n mod B be the state immediately
    before that carry is incorporated.

    * k=0: the carry can be shallow-published at zero rebuild work once the
      preceding full generation has finished:

          D_n = max(n, D_{n-1}).

    * 1 <= k < B: k units of work on the already-published state-k table can
      be performed before the next carry arrives, while one final unit depends
      on the new carry:

          D_n = max(n, D_{n-1} + k/s) + 1/s.

    The predecessor contributes exactly one outgoing-carry slot, so one future
    carry may wait.  A second waiting carry would stall.  Hence carry n must be
    absorbed no later than arrival n+2, i.e. D_n <= n+2.

    This model is chosen because B=2 exactly recovers the earlier 2.5-buffer
    schedule with alpha=1/2.  It is an implementation assumption: a merge that
    cannot expose the k units of current-table work early should use the strict
    merge-on-arrival bound returned by branching_strict_threshold().
    """
    validate_branching_factor(B)
    if speed <= 0:
        return False
    if speed + tol < branching_average_work(B):
        # Long-run work-conservation lower bound.
        return False

    Dprev = None
    total = B * cycles
    for n in range(total):
        k = n % B
        if Dprev is None:
            D = 0.0  # first k=0 carry at time 0
        elif k == 0:
            D = max(float(n), Dprev)
        else:
            D = max(float(n), Dprev + k / speed) + 1.0 / speed

        if D > n + 2.0 + tol:
            return False
        Dprev = D
    return True


def branching_streamable_threshold(B: int, cycles: int = 4000) -> float:
    """Exact threshold; cycles is retained for caller compatibility."""
    return float(minimum_speed_exact(B))


def branching_strict_threshold(B: int) -> float:
    r"""
    Minimum speed in a stricter merge-on-arrival model.

    Here a state-k merge does not start until its carry arrives, so the service
    costs in one cycle are 0,2,3,...,B.  With one waiting-carry slot, every
    consecutive burst of m jobs gets m ordinary inter-arrival intervals plus
    one buffer-slack interval.  Because the costs rise within a cycle, the
    worst burst is the final m jobs, giving

        max_m [sum_{j=B-m+1}^B j] / (m+1).

    This is useful as a conservative comparison when pre-routing/pre-sorting of
    the current state cannot be done before the next carry is known.
    """
    validate_branching_factor(B)
    best = branching_average_work(B)
    for m in range(1, B):
        burst = m * (2.0 * B - m + 1.0) / 2.0
        best = max(best, burst / (m + 1.0))
    return best


def branching_probe_average(B: int, speed: float,
                             cycles: int = 8000,
                             warmup_cycles: int = 100) -> float:
    r"""
    Average number of logically queryable tables at one B-ary level.

    This explicitly simulates the streamable schedule used by
    branching_streamable_no_stall().  A published current state contributes one
    probe.  The carry that triggers the current merge contributes another probe
    until publication, and the single future carry allowed to wait in the
    predecessor's outgoing slot contributes a third probe while it waits.

    Thus the metric counts logical searchable runs, not physical arenas.  In
    the infinite-speed limit it converges to (B-1)/B, the non-deamortized public
    occupancy average.
    """
    validate_branching_factor(B)
    if not branching_streamable_no_stall(B, speed, max(500, warmup_cycles)):
        return float("inf")

    horizon = float(cycles * B)
    warm = float(min(warmup_cycles, max(0, cycles // 4)) * B)

    state = 0                 # published state k in {0,...,B-1}
    trigger = False           # carry currently attached to the next merge
    waiting = 0               # one later carry may wait
    phase = None              # None / "pre" / "late"
    remaining = 0.0

    t = 0.0
    next_arrival = 0.0
    area = 0.0
    last_area_t = 0.0

    def probes() -> int:
        return (1 if state > 0 else 0) + (1 if trigger else 0) + waiting

    def add_area(to_t: float) -> None:
        nonlocal area, last_area_t
        a = max(last_area_t, warm)
        b = min(to_t, horizon)
        if b > a:
            area += probes() * (b - a)
        last_area_t = to_t

    def start_prework() -> None:
        nonlocal phase, remaining
        if state > 0:
            phase = "pre"
            remaining = float(state)
        else:
            phase = None
            remaining = 0.0

    def attach_waiting_after_transition() -> None:
        nonlocal waiting, state, trigger, phase, remaining
        if waiting == 0:
            return
        waiting = 0
        if state == 0:
            # The first carry of a new cycle is a zero-work shallow publish.
            state = 1
            start_prework()
        else:
            trigger = True
            if phase is None:
                phase = "late"
                remaining = 1.0

    start_prework()
    tol = 1e-11

    while t < horizon - tol:
        completion = (t + remaining / speed
                      if phase is not None and remaining > tol
                      else float("inf"))
        arrival = next_arrival if next_arrival < horizon - tol else float("inf")

        # Completions win ties, so a slot released exactly at a deadline is
        # available to the carry arriving at that deadline.
        if completion <= arrival + tol:
            add_area(completion)
            t = completion
            if phase == "pre":
                remaining = 0.0
                if trigger:
                    phase = "late"
                    remaining = 1.0
                else:
                    phase = None
            elif phase == "late":
                remaining = 0.0
                trigger = False
                state += 1
                if state == B:
                    # The full table becomes the one outgoing carry to the next
                    # level, so it is no longer counted as this level's current
                    # state.  The next level counts it as an incoming carry.
                    state = 0
                start_prework()
                attach_waiting_after_transition()
            continue

        # Arrival happens before the next rebuild-phase completion.  Advance the
        # currently running work to the arrival time.
        dt = arrival - t
        if phase is not None:
            remaining = max(0.0, remaining - speed * dt)
        add_area(arrival)
        t = arrival
        next_arrival += 1.0

        if state == 0 and not trigger and phase is None:
            state = 1
            start_prework()
        elif not trigger:
            trigger = True
            if phase is None:
                phase = "late"
                remaining = 1.0
        else:
            if waiting:
                return float("inf")
            waiting = 1

    add_area(horizon)
    measured = horizon - warm
    return area / measured


def branching_probe_ratio_to_binary(B: int, speed: float,
                                     cycles: int = 8000) -> float:
    """Total average probes / (binary non-deamortized baseline L2/2)."""
    q = branching_probe_average(B, speed, cycles=cycles)
    if not math.isfinite(q):
        return float("inf")
    return 2.0 * q / math.log2(B)


def print_branching_table(max_B: int = 32, rho: float = 0.0,
                          cycles: int = 8000) -> None:
    validate_branching_factor(max_B)
    print(
        "B,levels_factor,space_ratio,avg_work_lb,streamable_min_speed,"
        "strict_min_speed,avg_probes_per_level_at_min,"
        "probe_ratio_vs_binary_baseline_at_min,fast_limit_probe_ratio"
    )
    B = 2
    while B <= max_B:
        smin = branching_streamable_threshold(B)
        q = float(average_at_minimum_exact(B))
        ratio = 2.0 * q / math.log2(B)
        print(
            f"{B},{branching_levels_factor(B):.8f},"
            f"{branching_space_ratio(B,rho):.8f},"
            f"{branching_average_work(B):.8f},{smin:.8f},"
            f"{branching_strict_threshold(B):.8f},{q:.8f},{ratio:.8f},"
            f"{branching_amortized_probe_ratio_to_binary(B):.8f}"
        )
        B *= 2


def print_branching_speed_curve(B: int, max_speed: Optional[float] = None,
                                 step: float = 0.25,
                                 cycles: int = 8000) -> None:
    validate_branching_factor(B)
    smin = branching_streamable_threshold(B)
    if max_speed is None or max_speed < smin:
        max_speed = max(2.0 * smin, smin + 2.0)
    if step <= 0:
        raise ValueError("step must be positive")
    print("speed,avg_probes_per_level,ratio_vs_binary_baseline")
    s = smin
    while s <= max_speed + 1e-12:
        q = branching_probe_average(B, s * (1.0 + 1e-6), cycles=cycles)
        print(f"{s:.8f},{q:.8f},{2.0*q/math.log2(B):.8f}")
        s += step

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--levels", type=int, default=9)
    p.add_argument("--accesses", type=int, default=5000)
    p.add_argument("--step", type=float, default=0.05,
                   help="alpha sweep step")
    p.add_argument("--probe-curve", action="store_true")
    p.add_argument("--probe-alpha", type=float, default=0.75,
                   help="common alpha used for the same-speed binary probe comparison")
    p.add_argument("--max-speed", type=float, default=5.0)
    p.add_argument("--speed-step", type=float, default=0.25)

    p.add_argument("--branching", action="store_true",
                   help="print the larger-branching-factor comparison table")
    p.add_argument("--max-B", type=int, default=32,
                   help="largest power-of-two branching factor in --branching mode")
    p.add_argument("--rho", type=float, default=0.0,
                   help="top-level scratch parameter in 2 + rho/B")
    p.add_argument("--branching-speed-curve", type=int, metavar="B",
                   help="print probe count versus speed for one branching factor")
    p.add_argument("--branch-cycles", type=int, default=8000)
    args = p.parse_args()

    if args.branching_speed_curve is not None:
        print_branching_speed_curve(
            args.branching_speed_curve,
            max_speed=args.max_speed,
            step=args.speed_step,
            cycles=args.branch_cycles,
        )
        return

    if args.branching:
        print_branching_table(args.max_B, args.rho, args.branch_cycles)
        return

    if args.probe_curve:
        print_probe_curve(args.probe_alpha, args.max_speed, args.speed_step)
        return

    print("alpha,two_sim,two_formula,2.5_sim,2.5_formula")
    a = 0.0
    while a <= 1.0 + 1e-12:
        two = find_threshold(a, "two", args.levels, args.accesses)
        half = find_threshold(a, "2.5", args.levels, args.accesses)
        print(
            f"{a:.6f},{two:.8f},{analytic_threshold(a,'two'):.8f},"
            f"{half:.8f},{analytic_threshold(a,'2.5'):.8f}"
        )
        a += args.step


if __name__ == "__main__":
    main()
