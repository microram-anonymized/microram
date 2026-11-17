#!/usr/bin/env python3
"""Published-tier sizing, separate from temporary sorted-range workspace.

Reuse the complete-home excess upper bound for ordinary one-bucket tiers.
For a full half-loaded top population, also compute a finite-multinomial
LOWER bound: exactly S+1 total excess among all overloaded homes. This does
not infer a lower bound from the Poisson upper comparison.
"""
from decimal import Context, Decimal, ROUND_FLOOR, localcontext
from fractions import Fraction
import hashlib
import json
from math import log2
from pathlib import Path

from certify_oram import (ONE, UP, ZERO, describe, exp_upper, upper_fraction,
                          weighted_poisson_pmf)
from certify_tier_router import positive_excess_bound
from source_scope import provenance, scoped

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DOWN = Context(prec=UP.prec, rounding=ROUND_FLOOR)


def lower_fraction(value):
    value = Fraction(value)
    return DOWN.divide(Decimal(value.numerator), Decimal(value.denominator))


def exact_excess_event_lower(homes, population, capacity, slots):
    """Lower bound P[sum_v (X_v-C)+ = S+1], X multinomial(N; 1/m).

    Let t=S+1. Sum over j overloaded homes (1<=j<=t), each with
    C+e records, positive e's summing to t. Relative to [z^t]exp(m W(z)),
    falling factorial and empty-outside probabilities have uniform explicit
    lower factors. A conditional union bound excludes other overloaded homes.
    All finite multinomial corrections are retained; no conditioning on a
    random Poisson total or heuristic Poisson lower approximation is used.
    """
    if (any(not isinstance(x, int) or x < 0 for x in (homes, population, capacity, slots))
            or homes < 1 or capacity < 1 or population < 1):
        raise ValueError('Positive integer geometry and nonnegative slots required')
    mean = Fraction(population, homes)
    t = slots+1
    if mean > Fraction(capacity, 2) or homes <= t+1:
        raise ValueError('This lower-bound domain requires mean <= C/2 and m> S+2')
    maximum_records = (capacity+1)*t
    # These products bound the exact finite-N / Poisson coefficient ratios.
    source_factor = 1-Fraction(maximum_records*(maximum_records-1), 2*population)
    home_factor = 1-Fraction(t*(t-1), 2*homes)
    outside_factor = 1-mean*t*t/Fraction(2*(homes-t))
    correction = source_factor*home_factor*outside_factor
    if min(source_factor, home_factor, outside_factor) <= 0:
        raise ValueError('Uniform finite-population lower factor is not positive')

    with localcontext(DOWN):
        # exp is correctly rounded; a downward ulp encloses from below.
        probability = DOWN.next_minus(DOWN.exp(lower_fraction(-mean)))
        pmf = [probability]
        rate = lower_fraction(mean)
        for n in range(1, capacity+t+1):
            pmf.append(pmf[-1]*rate/n)
        weights = [Decimal(0)]+pmf[capacity+1:]
        coefficients = [Decimal(1)]+[Decimal(0)]*t
        for n in range(1, t+1):
            coefficients[n] = homes*sum((j*weights[j]*coefficients[n-j]
                                         for j in range(1, n+1)), Decimal(0))/n
        coefficient_lower = Fraction(coefficients[t])

    # Conditional on the selected j homes' exact loads, the remaining balls
    # occupy m-j homes uniformly. Their Bin(n,1/(m-j)) tail is at most
    # exp(mean/(m-t-1))*P[Pois(mean)>C]; see report derivation.
    cutoff = max(2*capacity, capacity+32)
    pmf_upper = weighted_poisson_pmf(mean, Fraction(0), cutoff+1)
    with localcontext(UP):
        poisson_tail = sum(pmf_upper[capacity+1:cutoff+1], ZERO)
        poisson_tail += pmf_upper[cutoff+1]*upper_fraction(1/(1-mean/Fraction(cutoff+2)))
        other_heavy_upper = homes*exp_upper(mean/Fraction(homes-t-1))*poisson_tail
    no_other_factor = 1-Fraction(other_heavy_upper)
    if no_other_factor <= 0:
        raise ValueError('Conditional no-other-overload lower factor is not positive')
    lower = coefficient_lower*correction*no_other_factor
    return dict(homes=homes, population=population, main_capacity=capacity, tier_slots=slots,
        mean_exact=str(mean), witnessed_total_excess=t,
        positive_coefficient_lower_exact=str(coefficient_lower),
        finite_population_factor_exact=str(correction),
        other_overloaded_homes_expectation_upper=str(other_heavy_upper),
        no_other_overload_factor_lower_exact=str(no_other_factor),
        probability_lower_exact=str(lower), probability_lower_decimal=str(lower_fraction(lower)),
        approximate_log2_lower_for_display_only=log2(float(lower)),
        exceeds_2_minus_64=lower > Fraction(1, 1 << 64))


def main():
    lower=exact_excess_event_lower(1 << 22,32*(1 << 22),64,64)
    sources={str(Path(__file__).resolve().relative_to(ROOT)):hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    for name in ('test_tier_sizes.py','certify_oram.py'):
        sources[str((HERE/name).relative_to(ROOT))]=hashlib.sha256((HERE/name).read_bytes()).hexdigest()
    result=dict(scope='Finite multinomial top one-page lower witness only; no obsolete mixed-pool analysis.',top_one_bucket_lower=lower,source_sha256=provenance(sources))
    (HERE/'tier_size_analysis.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
