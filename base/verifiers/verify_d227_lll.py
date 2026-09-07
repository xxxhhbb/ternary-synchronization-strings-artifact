"""Primary exact-rational replay of the denominator-227 LLL calculation.

The release entry point supplies the finite shells and charge parameters
fixed in the paper.  The verifier independently reconstructs all finite
event bounds and the rational infinite tail from the canonical codebook.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path


K = 952
M = 54
DEFAULT_D = 227
FINITE_END = 4000
ALPHA = Fraction(51, 100000)
BETA = Fraction(3, 10)
ROUND_SCALE = 10**30


def load_words(source: Path) -> list[str]:
    raw = source.read_bytes()
    words = raw.decode("ascii").splitlines()
    if len(words) != K or len(set(words)) != K:
        raise ValueError("malformed canonical 952-word export")
    if any(len(word) != M or set(word) - set("012") for word in words):
        raise ValueError("malformed codeword in canonical export")
    return words


def suffix_fibers(words: list[str]) -> dict[int, int]:
    return {s: max(Counter(word[-s:] for word in words).values()) for s in range(1, M)}


def point_mass(length: int, fibers: dict[int, int]) -> Fraction:
    candidates = [Fraction(1, K ** (length // M))]
    for offset in range(1, M):
        suffix = M - offset
        complete = (length - suffix) // M
        candidates.append(Fraction(fibers[suffix], K ** (complete + 1)))
    return max(candidates)


def event_volume(a: int, b: int, denominator: int, *, fill_left: bool = True) -> int:
    total = a + b
    difference = b - a
    value = 0
    upper = min(a, (total - 1 - denominator * difference) // (2 * denominator))
    if upper < 0:
        return 0
    for d_a in range(upper + 1):
        d_b = d_a + difference
        if d_b < 0 or d_b > b:
            continue
        if denominator * (d_a + d_b) >= total:
            continue
        if d_a == 0 and d_b == 0:
            continue
        value += math.comb(a, d_a) * math.comb(b, d_b) * 3**(d_a if fill_left else d_b)
    return value


def exp_upper(z: Fraction) -> Fraction:
    total = Fraction(1)
    term = Fraction(1)
    for degree in range(1, 81):
        term *= z / degree
        total += term
    term_81 = term * z / 81
    return total + term_81 / (1 - z / 82)


def ceil_scaled(value: Fraction) -> int:
    numerator = value.numerator * ROUND_SCALE
    return (numerator + value.denominator - 1) // value.denominator


def decimal(value: Fraction, digits: int = 24) -> str:
    sign = "-" if value < 0 else ""
    value = abs(value)
    scaled = value.numerator * 10**digits // value.denominator
    raw = str(scaled).rjust(digits + 1, "0")
    return sign + raw[:-digits] + "." + raw[-digits:]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--denominator", type=int, default=DEFAULT_D)
    parser.add_argument("--exclude-totals", default="")
    parser.add_argument("--alpha", default=str(ALPHA))
    parser.add_argument("--beta", default=str(BETA))
    parser.add_argument("--diagnostic", action="store_true", help="report failed inequalities instead of asserting")
    parser.add_argument("--bilateral", action="store_true")
    args = parser.parse_args()

    denominator = args.denominator
    alpha = Fraction(args.alpha)
    beta = Fraction(args.beta)
    if denominator < 156:
        raise ValueError("the current analytic tail is certified only for D>=156")
    excluded_totals = frozenset(
        int(item) for item in args.exclude_totals.split(",") if item
    )
    first_total = denominator + 1

    fibers = suffix_fibers(load_words(args.source))
    masses = {a: point_mass(a, fibers) for a in range((first_total - 1) // 2, FINITE_END)}
    exp_bounds = {
        total: exp_upper(alpha * total + beta)
        for total in range(first_total, FINITE_END + 1)
    }

    sum_scaled = 0
    weighted_scaled = 0
    maximum_scaled = 0
    maximum_witness = None
    event_type_count = 0
    for total in range(first_total, FINITE_END + 1):
        if total in excluded_totals:
            continue
        for a in range(1, total):
            b = total - a
            if denominator * abs(a - b) >= total:
                continue
            volume = event_volume(a, b, denominator)
            if volume == 0:
                continue
            event_type_count += 1
            upper = masses[a] * volume * exp_bounds[total]
            if args.bilateral:
                right_volume = event_volume(a, b, denominator, fill_left=False)
                upper = min(upper, masses[b] * right_volume * exp_bounds[total])
            scaled = ceil_scaled(upper)
            sum_scaled += scaled
            weighted_scaled += total * scaled
            if scaled > maximum_scaled:
                maximum_scaled = scaled
                maximum_witness = [a, b]

    finite_x_sum = Fraction(sum_scaled, ROUND_SCALE)
    finite_sx_sum = Fraction(weighted_scaled, ROUND_SCALE)
    loss_factor = Fraction(6000, 5999)
    finite_r0 = loss_factor * finite_x_sum
    finite_r1 = loss_factor * finite_sx_sum

    if denominator >= 358:
        q = Fraction(80, 83)
    elif denominator >= 200:
        # From log(952)>137/20, log(D)<6, log(2)<7/10, and
        # log(3)<11/10, the residual exponential rate is at least c.
        c = (
            Fraction(denominator - 1, 2 * denominator) * Fraction(137, 1080)
            - Fraction(44, 5 * denominator)
            - alpha
        )
        if c <= 0:
            raise ValueError("the coarse rational tail exponent is nonpositive")
        k = c.denominator // c.numerator + 1
        q = Fraction(k, k + 1)
    elif denominator == 156:
        q = Fraction(88, 89)
    else:
        raise ValueError("no paper-grade rational tail has been selected for this denominator")
    start = FINITE_END + 1
    one_minus_q = 1 - q
    first_moment = q**start * (
        Fraction(start, 1) / one_minus_q + q / one_minus_q**2
    )
    second_moment = q**start * (
        Fraction(start * start, 1) / one_minus_q
        + Fraction(2 * start, 1) * q / one_minus_q**2
        + q * (1 + q) / one_minus_q**3
    )
    tail_constant = Fraction(3 * 2 * K * K, denominator)
    tail_r0 = loss_factor * tail_constant * first_moment
    tail_r1 = loss_factor * tail_constant * second_moment

    r0 = finite_r0 + tail_r0
    r1 = finite_r1 + tail_r1
    slope_margin = alpha - r0
    constant_margin = beta - 109 * r0 - r1

    passed = (
        Fraction(maximum_scaled, ROUND_SCALE) < Fraction(1, 6000)
        and slope_margin > 0
        and constant_margin > 0
    )
    if not args.diagnostic and not passed:
        raise SystemExit("exact LLL inequalities failed")

    payload = {
        "status": f"D{denominator}_exact_finite_and_rational_tail_{'pass' if passed else 'fail'}",
        "denominator": denominator,
        "bilateral_conditioning": args.bilateral,
        "excluded_totals": sorted(excluded_totals),
        "finite_total_range": [first_total, FINITE_END],
        "event_type_count": event_type_count,
        "alpha": str(alpha),
        "beta": str(beta),
        "maximum_charge_upper_decimal": decimal(Fraction(maximum_scaled, ROUND_SCALE)),
        "maximum_charge_witness_lengths": maximum_witness,
        "R0_upper_decimal": decimal(r0),
        "R1_upper_decimal": decimal(r1),
        "finite_R0_upper_decimal": decimal(finite_r0),
        "finite_R1_upper_decimal": decimal(finite_r1),
        "combined_109R0_plus_R1_upper_decimal": decimal(109 * r0 + r1),
        "slope_margin_lower_decimal": decimal(slope_margin),
        "constant_margin_lower_decimal": decimal(constant_margin),
        "tail_R0_upper_decimal": decimal(tail_r0),
        "tail_R1_upper_decimal": decimal(tail_r1),
        "candidate_weak_normalized_edit_gap": f"1/{denominator}",
        "candidate_epsilon_open_threshold": f"{denominator-1}/{denominator}",
        "candidate_advertised_epsilon": f"{denominator}/{denominator+1}",
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
