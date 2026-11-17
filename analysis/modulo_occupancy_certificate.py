"""Check occupancy capacities with the 64-bit radix map's modulo bias.

For N=r*2^k buckets the largest destination probability is at most
1/N + 1/2^64. At half load, every marginal is convexly dominated by
Poisson(32*(1+N/2^64)). This is a component certificate, not a proof of
the main/range routing couplings or the lifetime failure bound.

It re-certifies, under that bias, the stash capacity table
(src/oram/rebuild/cpu_byteslice_stash_capacity_table.hpp) and the tier
depths selected by the generated residual tier coefficients
(src/oram/rebuild/cpu_byteslice_residual_tier_bound.hpp, from
gen_residual_tier_bound.py).
"""

from pathlib import Path
import re

from gen_residual_tier_bound import SCALE
from residual_occupancy_certificate import DOWN, interval
from stash_capacity_certificate import certify, entries

ROOT = Path(__file__).resolve().parents[1]


def modulo_mean_envelope(buckets, tag_bits=64):
    if buckets < 1 or tag_bits < 1 or buckets > 1 << tag_bits:
        raise ValueError("require 1 <= buckets <= the tag space")
    return interval(32) * (interval(1) + interval(buckets) / (1 << tag_bits))


def tier_boundaries(first=67, last=200):
    """Largest N accepted at each depth/exponent by the actual integer grid."""
    if first < 1 or last < first:
        raise ValueError("require a positive, ordered exponent range")
    source = (ROOT / "src/oram/rebuild/cpu_byteslice_residual_tier_bound.hpp").read_text()
    coefficients = [(int(a), int(b)) for a, b in
                    re.findall(r"\{(\d+)ull, (\d+)ull\}", source)]
    if len(coefficients) != 96:
        raise ValueError("unexpected residual coefficient grid")
    for depth in range(1, 9):
        for exponent in range(first, last+1):
            outputs, index = max(
                (((64*depth+1)*a - exponent*SCALE)//b, i)
                for i, (a, b) in enumerate(coefficients))
            if outputs > 0:
                yield 64*depth, exponent, outputs, interval(33+index)/32


def certify_modulo(outputs, slots, exponent, z=None):
    mean = modulo_mean_envelope(outputs)
    ok, bound = certify(outputs, slots, exponent, z=z, mean=mean)
    if not ok and z is not None:
        # The original grid witness can lose its tiny slack to the bias.
        # Another rational witness can still certify the same capacity.
        ok, bound = certify(outputs, slots, exponent, mean=mean)
    return ok, bound


def check(cells):
    count, worst, failures = 0, None, []
    for slots, exponent, outputs, z in cells:
        if outputs == 0:
            continue
        ok, bound = certify_modulo(outputs, slots, exponent, z)
        count += 1
        row = (DOWN.subtract(-exponent, bound), slots, exponent, outputs)
        worst = row if worst is None else min(worst, row)
        if not ok:
            failures.append(row)
    return count, worst, failures


def main():
    failed = False
    for name, cells in (
            ("Stage table", ((s, e, n, None) for s, e, n in entries())),
            ("Tier selector (exponents 67..200)", tier_boundaries())):
        count, worst, failures = check(cells)
        print(f"{name}: {count-len(failures)}/{count} certified")
        print(f"Minimum slack (bits), slots, exponent, width: {worst}")
        for row in failures:
            print("UNCERTIFIED", row)
        failed |= bool(failures)
    print("Occupancy inequalities only; routing couplings and lifetime ledger are separate.")
    raise SystemExit(failed)


if __name__ == "__main__":
    main()
