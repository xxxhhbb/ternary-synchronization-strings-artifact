"""Independent exact replay of the direct unequal-interval bound.

This implementation uses 64-fold exponential range reduction rather than
the degree-80 direct Taylor enclosure used by the primary verifier.  The
release entry point supplies the shell exclusions and charge parameters
fixed in the paper.
"""

from __future__ import annotations

import argparse
import math
from collections import Counter
from fractions import Fraction as F
from pathlib import Path


K, M = 952, 54
END = 4200
GRID = 10**28
A, B = F(37, 100000), F(21, 100)


def words(path: Path) -> list[str]:
    data = path.read_bytes()
    result = data.decode("ascii").splitlines()
    if len(result) != K or len(set(result)) != K:
        raise SystemExit("canonical source must contain 952 distinct words")
    if not all(len(item) == M and not (set(item) - set("012")) for item in result):
        raise SystemExit("canonical source has an invalid codeword")
    return result


def fibers(items: list[str]) -> list[int]:
    return [0] + [max(Counter(item[-s:] for item in items).values()) for s in range(1, M)]


def mass(length: int, fib: list[int]) -> F:
    values = [F(1, K ** (length // M))]
    for offset in range(1, M):
        suffix = M - offset
        values.append(F(fib[suffix], K ** (1 + (length - suffix) // M)))
    return max(values)


def volume(left: int, right: int, denominator: int, *, fill_left: bool = True) -> int:
    total = left + right
    shift = right - left
    bound = min(left, (total - 1 - denominator * shift) // (2 * denominator))
    if bound < 0:
        return 0
    answer = 0
    for dl in range(bound + 1):
        dr = dl + shift
        if dr < 0 or dr > right or denominator * (dl + dr) >= total:
            continue
        if dl == dr == 0:
            continue
        answer += math.comb(left, dl) * math.comb(right, dr) * 3**(dl if fill_left else dr)
    return answer


def exp_upper(z: F) -> F:
    y = z / 64
    partial = F(1)
    term = F(1)
    for degree in range(1, 25):
        term *= y / degree
        partial += term
    term_25 = term * y / 25
    small = partial + term_25 / (1 - y / 26)
    return small**64


def ceiling(value: F) -> int:
    top = value.numerator * GRID
    return (top + value.denominator - 1) // value.denominator


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--denominator", type=int, default=216)
    parser.add_argument("--exclude-totals", default="")
    parser.add_argument("--alpha", default=str(A))
    parser.add_argument("--beta", default=str(B))
    parser.add_argument("--bilateral", action="store_true")
    args = parser.parse_args()
    denominator = args.denominator
    alpha, beta = F(args.alpha), F(args.beta)
    if denominator < 156:
        raise SystemExit("denominator must be at least 156")
    excluded = frozenset(int(x) for x in args.exclude_totals.split(",") if x)
    first = denominator + 1
    fib = fibers(words(args.source))
    masses = {length: mass(length, fib) for length in range((first - 1) // 2, END)}
    exponentials = {total: exp_upper(alpha * total + beta) for total in range(first, END + 1)}

    sx = 0
    ssx = 0
    largest = 0
    for total in range(first, END + 1):
        if total in excluded:
            continue
        for left in range(1, total):
            right = total - left
            if denominator * abs(left - right) >= total:
                continue
            count = volume(left, right, denominator)
            if not count:
                continue
            upper = masses[left] * count * exponentials[total]
            if args.bilateral:
                right_count = volume(left, right, denominator, fill_left=False)
                upper = min(upper, masses[right] * right_count * exponentials[total])
            value = ceiling(upper)
            sx += value
            ssx += total * value
            largest = max(largest, value)

    factor = F(6000, 5999)
    r0 = factor * F(sx, GRID)
    r1 = factor * F(ssx, GRID)

    if denominator >= 358:
        q = F(80, 83)
    elif denominator >= 200:
        c = F(denominator - 1, 2 * denominator) * F(137, 1080) - F(44, 5 * denominator) - alpha
        if c <= 0:
            raise ValueError("coarse rational tail exponent is nonpositive")
        k = c.denominator // c.numerator + 1
        q = F(k, k + 1)
    elif denominator == 156:
        q = F(88, 89)
    else:
        raise ValueError("no independent rational tail selected for this denominator")
    n = END + 1
    om = 1 - q
    first = q**n * (F(n, 1) / om + q / om**2)
    second = q**n * (F(n * n, 1) / om + F(2 * n, 1) * q / om**2 + q * (1 + q) / om**3)
    constant = F(6 * K * K, denominator)
    r0 += factor * constant * first
    r1 += factor * constant * second

    if F(largest, GRID) >= F(1, 6000):
        raise SystemExit("maximum charge bound failed")
    if r0 >= alpha:
        raise SystemExit("zeroth-moment LLL bound failed")
    if 109 * r0 + r1 >= beta:
        raise SystemExit("first-moment LLL bound failed")
    print(f"INDEPENDENT_D{denominator}_EXACT_REPLAY_PASS")
    print(f"excluded_totals={sorted(excluded)}")
    print(f"slope_margin={float(alpha-r0):.18g}")
    print(f"constant_margin={float(beta-109*r0-r1):.18g}")


if __name__ == "__main__":
    raise SystemExit("Internal arithmetic module; run python -B verify.py from the package root.")
