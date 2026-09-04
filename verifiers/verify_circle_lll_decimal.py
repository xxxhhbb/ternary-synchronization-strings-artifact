"""High-precision cross-check of the all-length circle LLL arithmetic."""

from __future__ import annotations

import json
from decimal import Decimal, getcontext


getcontext().prec = 80

L = 2600
ETA = Decimal(1) / L
FIXED_AND_BOUNDARY_LOSS = 88
EVENT_DENOMINATOR = 135
CHARGE_DENOMINATOR = 150
NEIGHBOR_PRODUCT_DENOMINATOR = 15000
NEIGHBOR_SUM_DENOMINATOR = 30000


def main() -> None:
    one = Decimal(1)
    two = Decimal(2)
    three = Decimal(3)
    e = one.exp()
    log_two = two.ln()
    alpha = ETA * (log_two + two * (e / ETA).ln() + three.ln())
    entropy_rate = log_two / Decimal(18) - alpha

    first_long_scale = Decimal(L + 1)
    event_margin = (
        entropy_rate - one / EVENT_DENOMINATOR
    ) * first_long_scale - Decimal(FIXED_AND_BOUNDARY_LOSS) * log_two

    charge_rate = one / CHARGE_DENOMINATOR
    z = (-charge_rate).exp()
    start = Decimal(L + 1)
    geometric_zero = z**int(start) / (one - z)
    geometric_one = z**int(start) * (
        start / (one - z) + z / (one - z) ** 2
    )
    neighbor_ratio = three * (geometric_zero + geometric_one / start)
    neighbor_margin = one / NEIGHBOR_SUM_DENOMINATOR - neighbor_ratio

    lll_rate = one / CHARGE_DENOMINATOR + one / NEIGHBOR_PRODUCT_DENOMINATOR
    lll_margin = one / EVENT_DENOMINATOR - lll_rate

    checks = {
        "volume_rate_alpha": str(alpha),
        "entropy_minus_volume_rate": str(entropy_rate),
        "event_absorption_margin": str(event_margin),
        "neighbor_ratio_at_first_scale": str(neighbor_ratio),
        "neighbor_ratio_margin_below_1_over_30000": str(neighbor_margin),
        "lll_exponent_margin": str(lll_margin),
        "equal_length_gap": "1/2600",
        "nonstrict_full_interval_gap": "1/5201",
        "advertised_strict_full_interval_gap": "1/5202",
    }
    if event_margin <= 0:
        raise SystemExit("event-tail margin failed")
    if neighbor_margin <= 0:
        raise SystemExit("neighbor-sum margin failed")
    if lll_margin <= 0:
        raise SystemExit("LLL exponent margin failed")
    print(json.dumps({"status": "PASS", **checks}, indent=2))


if __name__ == "__main__":
    main()
