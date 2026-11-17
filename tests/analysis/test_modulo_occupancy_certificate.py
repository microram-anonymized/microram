"""Checks for analysis/modulo_occupancy_certificate.py (occupancy capacities under the
64-bit radix map's modulo bias): exact map probabilities and independent numerical
re-checks of the certificate."""

from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "analysis"))
import modulo_occupancy_certificate as modulo
from gen_residual_tier_bound import poisson_mgf
from residual_occupancy_certificate import interval
from stash_capacity_certificate import entries


class ModuloOccupancyCertificateTest(unittest.TestCase):
    def test_exact_reduced_tag_space_probabilities(self):
        bits = 8
        for low in range(5):
            for radix in range(1, 9):
                counts = Counter((tag & ((1 << low)-1)) +
                                 ((tag >> low) % radix)*(1 << low)
                                 for tag in range(1 << bits))
                buckets = radix << low
                q = 1 << (bits-low)
                exact_max = Fraction((q+radix-1)//radix, 1 << bits)
                self.assertEqual(Fraction(max(counts.values()), 1 << bits), exact_max)
                self.assertLessEqual(exact_max, Fraction(1, buckets) + Fraction(1, 1 << bits))
                self.assertLessEqual(32*buckets*exact_max,
                                     Fraction(modulo.modulo_mean_envelope(buckets, bits).high))

    def test_noninteger_mean_against_independent_high_precision_recurrence(self):
        with localcontext() as ctx:
            ctx.prec = 160
            for mean in (Decimal(32), Decimal(32) + Decimal(17)/2**40, Decimal(36)):
                for z in (Decimal(33)/32, Decimal(2), Decimal(4)):
                    point, mgf = (-mean).exp(), Decimal(1)
                    for k in range(1, 513):
                        point *= mean/k
                        if k > 64:
                            mgf += point*(z**(k-64)-1)
                    ratio = z*mean/513
                    oracle_upper = mgf + point*z**448*ratio/(1-ratio)
                    actual = poisson_mgf(interval(z), interval(mean)).high
                    self.assertGreaterEqual(actual, oracle_upper)
                    # The explicit geometric tail at 256 is conservative,
                    # especially at mean=36, z=4; it is not rounding noise.
                    self.assertLess(actual-oracle_upper, Decimal('1e-18')*oracle_upper)

    def test_all_stored_stage_thresholds_with_bias(self):
        count, worst, failures = modulo.check((s, e, n, None) for s, e, n in entries())
        self.assertEqual(count, 1012)
        self.assertEqual(failures, [])
        self.assertGreater(worst[0], 0)

    def test_all_tier_acceptance_boundaries_with_bias(self):
        count, worst, failures = modulo.check(modulo.tier_boundaries())
        self.assertEqual(count, 991)
        self.assertEqual(failures, [])
        self.assertGreater(worst[0], 0)

    def test_unsafe_claim_and_invalid_envelopes_reject(self):
        self.assertFalse(modulo.certify_modulo(1 << 29, 64, 100)[0])
        for buckets, bits in ((0, 64), (257, 8), (1, 0)):
            with self.assertRaises(ValueError):
                modulo.modulo_mean_envelope(buckets, bits)
        with self.assertRaises(ValueError):
            poisson_mgf(interval(4), 65)  # weighted-tail ratio exceeds one


if __name__ == "__main__":
    unittest.main()
