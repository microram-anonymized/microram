"""Freeze a common integer offered-load grid for matched latency campaigns."""

from decimal import Decimal, InvalidOperation, ROUND_CEILING, localcontext

from .codec import require
from .schema import RateGrid


def geometric_rate_grid(minimum, maximum, factor="2"):
    """Return a RateGrid shared verbatim by all arms, for fixed arrivals.

    Round each geometric point upward to integer ops/s; include maximum as
    the final (possibly shorter) interval. Bounds come from frozen saturation
    evidence, not from a different bound for each scheme.
    """
    require(type(minimum) is int and type(maximum) is int and 0 < minimum <= maximum,
            "rate bounds must be positive integers with minimum <= maximum")
    try:
        ratio = Decimal(str(factor))
    except InvalidOperation:
        require(False, "geometric factor must be finite and > 1")
    require(ratio.is_finite() and ratio > 1, "geometric factor must be finite and > 1")
    rates = []
    with localcontext() as context:
        context.prec = 50
        point = Decimal(minimum)
        while point < maximum:
            rate = int(point.to_integral_value(rounding=ROUND_CEILING))
            require(not rates or rate > rates[-1],
                    "factor too small to produce distinct integer rates")
            rates.append(rate)
            require(len(rates) < 256, "geometric grid exceeds 256 points; increase factor")
            point *= ratio
    if not rates or rates[-1] != maximum:
        rates.append(maximum)
    grid = RateGrid(absolute_ops_per_second=rates, minimum_ops_per_second=minimum)
    grid.validate()
    return grid
