"""Exact small-state checks for the completed-A numerical enclosure."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import unittest

from certify_completed_a import convolve, thin, terminal, radix_classes, truncation
from test_completed_a_shadow import terminal_law


class CompletedANumericsTests(unittest.TestCase):
    def test_thinning_encloses_exact_binomials(self):
        from math import comb
        for scale in (16, 256):
            f = [[1, 2, 0, 0], [2, 0, 3, 0], [1, 0, 0, 0]]
            for p in (Q(1, 3), Q(3, 8)):
                actual = thin(f, p, scale)
                for u in range(3):
                    for v in range(4):
                        exact = sum((Q(f[m][r], scale)*comb(m,u)*comb(r,v)
                                     *p**(u+v)*(1-p)**(m+r-u-v)
                                     for m in range(u,3) for r in range(v,4)), Q(0))
                        self.assertGreaterEqual(Q(actual[u][v],scale), exact)
                        self.assertLess(Q(actual[u][v],scale)-exact, Q(8,scale))

    def test_packed_convolution_equals_direct_integer_convolution(self):
        import random
        rng = random.Random(20260929)
        for cutoff in (2, 5, 8):
            for _ in range(10):
                scale = 32
                f = [[rng.randrange(80) for _ in range(cutoff+1)] for _ in range(3)]
                h = [[rng.randrange(80) for _ in range(cutoff+1)] for _ in range(2)]
                actual = convolve(f,h,cutoff,scale)
                for m,row in enumerate(actual):
                    for r,value in enumerate(row):
                        exact = sum(f[u][v]*h[m-u][r-v]
                                    for u in range(len(f)) if 0 <= m-u < len(h)
                                    for v in range(r+1)) if m+r <= cutoff else 0
                        self.assertEqual(value, (exact+scale-1)//scale)
        self.assertEqual(convolve([[0]*3], [[0]*3], 2, 32), [[0]*3])

    def test_terminal_encloses_full_exact_mixture(self):
        # Main/shadow dependence matters; use a non-product input law.
        scale, cutoff, capacity = 1 << 40, 9, 1
        states = {(0,2): Q(1,4), (1,0): Q(3,4)}
        f = [[0]*(cutoff+1) for _ in range(2)]
        for (m,r), weight in states.items():
            f[m][r] = int(weight*scale)
        for radix in (2,3):
            for p in (Q(1,3),Q(3,8)):
                expected = defaultdict(Q)
                for children in product(states, repeat=radix):
                    weight = Q(1)
                    for state in children:
                        weight *= states[state]
                    for (_, r), mass in terminal_law(children,p,capacity).items():
                        expected[r] += weight*mass
                actual = terminal(f,radix,p,capacity,cutoff,scale)
                for r,value in enumerate(actual):
                    self.assertGreaterEqual(Q(value,scale), expected[r])
                    self.assertLess(Q(value,scale)-expected[r], Q(2000,scale))

    def test_partial_sum_truncation_retains_exact_good_states(self):
        # p=1 makes the removed terminal total explicit, without rounding.
        scale, cutoff = 64, 3
        f = [[scale//2,0,0,0], [0,0,scale//2,0]]
        actual = terminal(f,3,Q(1),1,cutoff,scale)
        # At most one nonzero child: total 3, shadow 2; two exceed cutoff.
        self.assertEqual(actual, [8,0,24,0])

    def test_finite_word_classes_partition_word_space(self):
        for width in (5,8,64):
            for radix in (1,3,5,7):
                classes = radix_classes(width,2,radix)
                self.assertEqual(sum(p*n for p,n in classes),1)
                self.assertEqual(sum(n for _,n in classes),radix)

    def test_terminal_truncation_is_charged(self):
        self.assertGreater(truncation(3,3,Q(1,3),2),truncation(3,1,Q(1),2))

if __name__ == '__main__':
    unittest.main()
