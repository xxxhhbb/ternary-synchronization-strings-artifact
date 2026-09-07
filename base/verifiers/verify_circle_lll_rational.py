"""Exact-rational replay of the inequalities in Appendix D.

This does not evaluate logarithms numerically.  It checks the finite rational
series enclosures and every rational implication printed in the proof of the
all-length circle theorem.
"""

from fractions import Fraction as F
from math import factorial


def log_bounds(x: F, terms: int) -> tuple[F, F]:
    """Return the paper's lower/upper atanh-series bounds for log(x)."""
    assert x > 1
    z = (x - 1) / (x + 1)
    lower = 2 * sum((z ** (2 * j + 1) / (2 * j + 1) for j in range(terms + 1)), F())
    remainder = 2 * z ** (2 * terms + 3) / ((2 * terms + 3) * (1 - z * z))
    return lower, lower + remainder


def main() -> None:
    log2_lo, log2_hi = log_bounds(F(2), 12)
    log3_lo, log3_hi = log_bounds(F(3), 18)
    log325_lo, log325_hi = log_bounds(F(325, 256), 6)

    printed_log2_lower = F(6_931_471_805, 10_000_000_000)
    printed_alpha_upper = F(750_704, 100_000_000)
    assert log2_lo > printed_log2_lower

    # log(2600) = 11 log(2) + log(325/256).
    alpha_upper = (
        log2_hi + 2 * (F(1) + 11 * log2_hi + log325_hi) + log3_hi
    ) / 2600
    assert alpha_upper < printed_alpha_upper

    # Event-tail absorption at the first long scale ell=2601.
    margin_lower = (
        F(113, 2) * printed_log2_lower
        - 2601 * printed_alpha_upper
        - F(2601, 135)
    )
    printed_margin = F(4_444_055_899, 12_000_000_000)
    assert margin_lower == printed_margin
    assert printed_margin > F(3703, 10_000)
    assert printed_log2_lower / 18 - printed_alpha_upper - F(1, 135) > 0

    # Rational domination of the geometric neighbor tail.
    assert 25 * log2_hi < F(2601, 150)
    rational_neighbor_upper = F(3, 2**25) * (F(302) + F(151**2, 2601))
    printed_neighbor_upper = F(808_303, 29_091_692_544)
    assert rational_neighbor_upper == printed_neighbor_upper
    assert printed_neighbor_upper < F(1, 30_000)

    # Final LLL and synchronization margins.
    assert F(1, 135) > F(1, 150) + F(1, 15_000)
    assert F(1, 5202) < F(1, 5201)

    print("CIRCLE_RATIONAL_BOUNDS_PASS")
    print(f"log2_lower_slack={log2_lo - printed_log2_lower}")
    print(f"alpha_upper_slack={printed_alpha_upper - alpha_upper}")
    print(f"event_margin={printed_margin}")
    print(f"neighbor_upper={printed_neighbor_upper}")


if __name__ == "__main__":
    main()
