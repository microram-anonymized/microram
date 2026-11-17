"""Check the closed forms against exact recurrences and event simulation."""

from fractions import Fraction
import math

from deamortization_closed_form import average_at_minimum_exact, minimum_speed_exact
from deamortization_analysis import average_probes_per_level, streamable_no_stall


def check(no_stall_checks, probe_simulators) -> None:
    """Check the closed forms exactly, then against the given event simulators.

    Each simulator takes the arguments of streamable_no_stall or
    average_probes_per_level, so that another implementation of the same model
    can be checked with the same thresholds and tolerances.
    """
    for exponent in range(1, 13):
        B = 2 ** exponent
        s = minimum_speed_exact(B)
        work = sum(range(2, B + 1))
        # Enumerate all suffix constraints independently of the rounded root.
        bounds = [Fraction(work, B)]
        suffix_work = 1
        bounds.append(Fraction(1, 2))
        for m in range(1, B - 1):
            suffix_work += B - m + 1
            bounds.append(Fraction(suffix_work, m + 2))
        assert s == max(bounds), (B, s, max(bounds))

        delay = Fraction(0)
        previous = None
        for cycle in range(6):
            delays = []
            for k in range(B):
                delay = (max(0, delay - 1) if k == 0 else
                         max(1 / s, delay + Fraction(k + 1) / s - 1))
                assert 0 <= delay <= 2, (B, cycle, k, delay)
                delays.append(delay)
            if cycle == 5:
                assert delays == previous, (B, "not periodic")
            previous = delays
        # Integrate the current table and each carry's lifetime separately.
        current_area = B - 1 + delays[-1] - delays[0]
        q = (current_area + sum(delays)) / B
        assert q == average_at_minimum_exact(B), (B, q)

        if B <= 64:
            speed = float(s) * (1 + 1e-8)
            for no_stall in no_stall_checks:
                assert no_stall(B, speed, cycles=600)
                assert not no_stall(B, float(s) * (1 - 1e-5), cycles=600)
            for simulate in probe_simulators:
                measured = simulate(B, speed, cycles=600, warmup_cycles=100)
                assert math.isclose(measured, float(q), abs_tol=2e-6), (
                    B, simulate.__name__, measured, q)
            print(f"B={B}: s={s}, q={q}, overhead={2*float(q)/math.log2(B):.9f}")
    print("Exact recurrence/suffix checks passed for B=2..4096 (powers of two).")


def main() -> None:
    check((streamable_no_stall,), (average_probes_per_level,))
    print("The event simulator agrees for B=2..64, including threshold checks.")


if __name__ == "__main__":
    main()
