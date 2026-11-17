#!/usr/bin/env python3
"""
Storage-constrained deamortized hierarchical-ORAM model and figure.

Running this file with no arguments generates:

    deamortized_probe_tradeoff.pdf

in the current directory.

Model
-----
A B-ary level has public states 0,...,B-1.  One incoming carry is the unit of
size.  A state-k table contains k carry units.  The first carry (k=0) is
adopted into the level's storage at zero modeled rebuild cost.  For k>=1,
merging state k with the next carry has k+1 units of work.

The paper model uses the three-region layout of Section 2.5 (Deamortization):
two regions of B carry units and one of B-1 units. A rebuild waits for its
output region
to become free, including waits for the next level to absorb an outgoing
table. The figure and command-line summary use LayoutSim with LAYOUT from
arena_coupling/layout_speeds.py, the same model as the paper's comparison
table. Each curve starts at the simulated minimum speed for this layout.

The model is intentionally idealized:
  * the k units that depend only on the current state can be pre-routed before
    the next carry arrives;
  * one final unit depends on the new carry;
  * each non-top level has a constant rebuild speed;
  * the first carry is adopted into the middle region at zero cost.

A second waiting carry would stall the hierarchy.  The simulator counts every
separately published current table, triggering carry, and waiting carry as a
separate online table probe.

These are recipient-side categories for averaging lifetimes. They do not
give a tight global worst-case bound: charging each table to its physical
arena counts at most two published tables per arena, or 2*log_B(N), when
rebuild deadlines are met.

Probe overhead is normalized to the non-deamortized binary hierarchy.  A binary
level is active only half the time, so that baseline performs L_2/2 table
probes on average.

This is a logical scheduling model, not a simulation of the implementation's
thread scheduler. The older unconstrained helpers below remain only for the
independent checks in check_deamortization_closed_form.py; the paper figure
and summary do not use them.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import math
from pathlib import Path
import sys
from typing import Iterable, Optional

from deamortization_closed_form import minimum_speed_exact

sys.path.insert(0, str(Path(__file__).resolve().parent / "arena_coupling"))
from layout_speeds import (LAYOUT, LayoutSim, min_speed as layout_min_speed,
                          periodicity_error)
from hier import big_stack

# (non-top levels, top-level cycles), checked against the adjacent depths
# in layout_speeds.py and layout_extra.py. The time average spans six complete
# top cycles, excluding initialization and shutdown. Average all non-top
# levels; the fixed-size top itself is outside the paper's leading terms.
LAYOUT_RUNS = {2: (8, 10), 4: (5, 10), 8: (5, 10)}


# ---------------------------------------------------------------------------
# Archived unconstrained helpers, retained for closed-form verification
# ---------------------------------------------------------------------------

def validate_B(B: int) -> None:
    if B < 2 or (B & (B - 1)) != 0:
        raise ValueError("B must be a power of two and at least 2")


def average_rebuild_work(B: int) -> float:
    """Average rebuild work per incoming-carry interval."""
    validate_B(B)
    # Cycle costs are 0,2,3,...,B.
    return (B + 1.0) / 2.0 - 1.0 / B


def streamable_no_stall(
    B: int,
    speed: float,
    cycles: int = 4000,
    tol: float = 1e-10,
) -> bool:
    """
    Return whether the idealized streamable schedule avoids a stall.

    Normalize one incoming-carry interval to one unit of time.  Let D_n be the
    time at which carry n has been fully incorporated.

    For state k>0, k units of current-table work can run before the new carry is
    known and one unit must wait for the carry.  One future carry may wait, so
    carry n must finish by the arrival of carry n+2.
    """
    validate_B(B)
    if speed <= 0:
        return False
    if speed + tol < average_rebuild_work(B):
        return False

    D_prev: Optional[float] = None
    for n in range(B * cycles):
        k = n % B

        if D_prev is None:
            D = 0.0
        elif k == 0:
            # First carry of a fresh B-ary digit: shallow publish.
            D = max(float(n), D_prev)
        else:
            # Pre-route k units, then do the one carry-dependent unit.
            D = max(float(n), D_prev + k / speed) + 1.0 / speed

        if D > n + 2.0 + tol:
            return False
        D_prev = D

    return True


def min_streamable_speed(B: int, cycles: int = 4000) -> float:
    """Closed-form threshold; cycles is retained for caller compatibility."""
    return float(minimum_speed_exact(B))


def average_probes_per_level(
    B: int,
    speed: float,
    cycles: int = 6000,
    warmup_cycles: int = 100,
) -> float:
    """
    Average number of queryable tables at one B-ary level.

    A published state table contributes one probe.  A carry that has arrived
    but has not yet been subsumed contributes another.  One later carry may
    wait in the producer's outgoing slot and contributes a third probe.
    """
    validate_B(B)
    if not streamable_no_stall(B, speed, cycles=max(500, warmup_cycles)):
        return float("inf")

    horizon = float(cycles * B)
    warm = float(min(warmup_cycles, max(0, cycles // 4)) * B)

    state = 0
    trigger = False
    waiting = 0

    # phase is None, "pre", or "late".
    phase: Optional[str] = None
    remaining = 0.0

    t = 0.0
    next_arrival = 0.0
    area = 0.0
    last_area_t = 0.0
    tol = 1e-11

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

    def attach_waiting() -> None:
        nonlocal waiting, state, trigger, phase, remaining
        if waiting == 0:
            return
        waiting = 0
        if state == 0:
            state = 1
            start_prework()
        else:
            trigger = True
            if phase is None:
                phase = "late"
                remaining = 1.0

    start_prework()

    while t < horizon - tol:
        completion = (
            t + remaining / speed
            if phase is not None and remaining > tol
            else float("inf")
        )
        arrival = (
            next_arrival if next_arrival < horizon - tol else float("inf")
        )

        # A completion at exactly the carry deadline frees the slot in time.
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
                    # Full table becomes the outgoing carry to the next level.
                    state = 0

                start_prework()
                attach_waiting()
            continue

        # Carry arrives before the current phase completes.
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
    return area / (horizon - warm)


def probe_overhead(
    B: int,
    speed: float,
    cycles: int = 6000,
) -> float:
    """
    Average total probe count divided by the binary non-deamortized average L_2/2.
    """
    q = average_probes_per_level(B, speed, cycles=cycles)
    if not math.isfinite(q):
        return float("inf")

    # There are L_2 / log2(B) B-ary levels.
    return 2.0 * q / math.log2(B)


def fast_rebuild_probe_limit(B: int) -> float:
    """Probe overhead as rebuild speed tends to infinity."""
    validate_B(B)
    return 2.0 * (B - 1.0) / (B * math.log2(B))


@lru_cache(maxsize=None)
def modeled_min_speed(B: int) -> float:
    """Minimum no-stall speed with the paper's three-region layout."""
    if B not in LAYOUT_RUNS:
        raise ValueError("the storage-constrained figure supports B=2,4,8")
    levels, top_cycles = LAYOUT_RUNS[B]
    return max(average_rebuild_work(B),
               layout_min_speed(B, levels, top_cycles, **LAYOUT))


def layout_average_tables(B: int, speed: float) -> float:
    """Mean queryable tables over non-top levels in the coupled simulation."""
    levels, top_cycles = LAYOUT_RUNS[B]
    sim = LayoutSim(B, levels, speed, top_cycles=top_cycles, **LAYOUT).run()
    if sim.worst() > 1e-7:
        raise ValueError(f"B={B}, speed={speed}: simulated schedule stalls")
    if periodicity_error(sim) > 1e-7:
        raise ValueError(f"B={B}, speed={speed}: schedule is not yet periodic")
    return sum(sim.tables_per_level(l, lo=0.2, hi=0.8)
               for l in range(levels)) / levels


def space_ratio(B: int, rho: float = 0.0) -> float:
    """
    Deep-hierarchy main buckets divided by top buckets, with top factor B.

    Top level:     2 + rho/B slots.
    Other levels: 3 - 1/B local slots.
    Successive lower slot capacities shrink by 1/B.

    Our butterfly rebuild uses rho=0.
    """
    validate_B(B)
    if rho < 0:
        raise ValueError("rho must be nonnegative")

    lower_slots = 3.0 - 1.0 / B
    return 2.0 + rho / B + lower_slots / (B - 1.0)


# ---------------------------------------------------------------------------
# Plot and command line
# ---------------------------------------------------------------------------

def plot_tradeoff(
    output: str | Path = "deamortized_probe_tradeoff.pdf",
    Bs: Iterable[int] = (2, 4, 8),
    max_speed: float = 16.0,
    save_png: bool = False,
) -> Path:
    """
    Plot probe overhead against rebuild speed and save a PDF.

    Curves include the storage waits of the three-region layout. The supported
    non-top branching factors are 2, 4, and 8.
    """
    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    output = Path(output)
    if output.suffix.lower() != ".pdf":
        output = output.with_suffix(".pdf")

    Bs = tuple(Bs)
    for B in Bs:
        validate_B(B)

    # Single-column paper figure.
    fig, ax = plt.subplots(figsize=(3.35, 2.55))

    for B in Bs:
        s_min = modeled_min_speed(B)
        if s_min > max_speed:
            continue

        speeds = np.geomspace(
            s_min * (1.0 + 1e-6),
            max_speed,
            48,
        )
        ys = [2.0 * layout_average_tables(B, float(s)) / math.log2(B)
              for s in speeds]

        if B == 2:
            ax.plot(
                speeds,
                ys,
                linewidth=1.9,
                label=r"$B=2$",
                zorder=3,
            )
        else:
            ax.plot(
                speeds,
                ys,
                linewidth=1.8,
                label=fr"$B={B}$",
                zorder=2,
            )

    ax.axhline(1.0, linewidth=0.9, linestyle=":", color="0.45")

    ax.set_xscale("log", base=2)
    ax.set_xlim(0.8, max_speed)
    ax.set_ylim(0, 3.10)

    ticks = [1, 2, 3, 4, 8, 16]
    ticks = [x for x in ticks if x <= max_speed]
    ax.set_xticks(ticks)
    ax.set_xticklabels([f"{x:g}" for x in ticks])

    ax.set_xlabel("Rebuild speed", fontsize=10.5)
    ax.set_ylabel("Probe overhead", fontsize=10.5)
    ax.tick_params(axis="both", labelsize=8.8)
    ax.grid(True, which="both", linewidth=0.45, alpha=0.25)

    ax.legend(
        fontsize=7.4,
        frameon=False,
        ncol=2,
        columnspacing=0.8,
        handlelength=1.8,
        handletextpad=0.45,
        borderaxespad=0.3,
    )

    fig.tight_layout(pad=0.35)
    fig.savefig(output, bbox_inches="tight")

    if save_png:
        fig.savefig(output.with_suffix(".png"), dpi=300, bbox_inches="tight")

    plt.close(fig)
    return output


def print_summary(Bs: Iterable[int]) -> None:
    print("B,modeled_min_speed,storage_over_amortized_binary,"
          "avg_tables_at_min,probe_overhead_at_min,fast_probe_overhead")
    for B in Bs:
        validate_B(B)
        speed = modeled_min_speed(B)
        q = layout_average_tables(B, speed * (1.0 + 1e-6))
        print(
            f"{B},"
            f"{speed:.8f},"
            f"{space_ratio(B, rho=0.0)/2.0:.8f},"
            f"{q:.8f},"
            f"{2.0*q/math.log2(B):.8f},"
            f"{fast_rebuild_probe_limit(B):.8f}"
        )


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=(
            "Analyze the storage-constrained B-ary deamortized hierarchy. "
            "With no arguments, save deamortized_probe_tradeoff.pdf."
        )
    )
    p.add_argument(
        "-o",
        "--output",
        default="deamortized_probe_tradeoff.pdf",
        help="output PDF path (default: deamortized_probe_tradeoff.pdf)",
    )
    p.add_argument(
        "--max-speed",
        type=float,
        default=16.0,
        help="largest rebuild speed shown in the plot (default: 16)",
    )
    p.add_argument(
        "--B",
        type=int,
        nargs="+",
        default=[2, 4, 8],
        choices=[2, 4, 8],
        help="branching factors (default: 2 4 8)",
    )
    p.add_argument(
        "--png",
        action="store_true",
        help="also save a PNG next to the PDF",
    )
    p.add_argument(
        "--summary-only",
        action="store_true",
        help="print the numerical summary without generating a plot",
    )
    return p.parse_args()


def main() -> None:
    args = parse_args()

    if args.max_speed <= 1:
        raise ValueError("--max-speed must be greater than 1")

    for B in args.B:
        validate_B(B)

    print_summary(args.B)

    if args.summary_only:
        return

    output = plot_tradeoff(
        output=args.output,
        Bs=args.B,
        max_speed=args.max_speed,
        save_png=args.png,
    )
    print(f"Saved plot to {output}")


if __name__ == "__main__":
    # Simulated dependencies can recurse deeply across levels. Propagate an
    # exception from the large-stack worker so failed generation exits nonzero.
    def run_cli():
        try:
            main()
        except BaseException as exc:
            return exc

    failure = big_stack(run_cli)
    if failure is not None:
        raise failure
