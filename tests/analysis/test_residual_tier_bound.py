"""Checks for analysis/gen_residual_tier_bound.py, which generates the integer Chernoff
coefficients used to size residual tiers automatically: numerical and
finite-distribution checks of its bounds."""

from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "analysis"))
import gen_residual_tier_bound as gen
import residual_occupancy_certificate as cert


class ResidualTierBoundTest(unittest.TestCase):
    def test_generated_header_is_current(self):
        self.assertEqual(gen.render(), (ROOT / "src/oram/rebuild/"
                         "cpu_byteslice_residual_tier_bound.hpp").read_text())

    def test_coefficients_enclose_independent_high_precision_oracle(self):
        # A separate 160-digit Poisson recurrence, including the positive
        # omitted tail. This checks coefficient direction and quantization.
        with localcontext() as ctx:
            ctx.prec = 160
            for numerator, (a, b) in zip(range(33, 129), gen.coefficients()):
                z = Decimal(numerator) / 32
                point = Decimal(-32).exp()
                mgf = Decimal(1)
                for k in range(1, 513):
                    point *= Decimal(32) / k
                    if k > 64:
                        mgf += point * (z ** (k - 64) - 1)
                ratio = z * 32 / 513
                mgf += point * z**448 * ratio / (1 - ratio)
                self.assertLessEqual(Decimal(a) / gen.SCALE, z.ln() / Decimal(2).ln())
                self.assertGreaterEqual(Decimal(b) / gen.SCALE,
                                        mgf.ln() / Decimal(2).ln())

    def test_poisson_envelope_covers_finite_binomial_mgf(self):
        for n, bins in ((64, 2), (96, 3), (128, 4)):
            for numerator in (33, 64, 96, 128):
                z = Fraction(numerator, 32)
                finite = sum(Fraction(comb(n, k) * (bins-1)**(n-k), bins**n)
                             * z**max(0, k-64) for k in range(n+1))
                upper = gen.poisson_mgf(cert.interval(numerator) / 32).high
                self.assertLessEqual(finite, Fraction(upper))

    def test_selected_depth_covers_finite_large_occupancy(self):
        coefficients = list(gen.coefficients())
        for buckets, exponent in ((128, 93), (131072, 79),
                                  (524288, 81), (4194304, 79)):
            selected = None
            for depth in range(1, 9):
                if any(buckets*b + exponent*gen.SCALE <= (64*depth+1)*a
                       for a, b in coefficients):
                    selected = depth
                    break
            self.assertIsNotNone(selected)
            self.assertLessEqual(cert.excess_upper(32*buckets, buckets, 64*selected),
                                 Decimal(2) ** -exponent)
        self.assertEqual(selected, 2)  # the initialization counterexample


if __name__ == "__main__":
    unittest.main()
