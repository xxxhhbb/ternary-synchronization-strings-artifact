"""Supported deletion volumes and exact rational LLL bounds for gap 1/216."""
from functools import lru_cache
from fractions import Fraction
import importlib.util
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'base_arithmetic', ROOT / 'base/verifiers/exact_arithmetic.py')
arithmetic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(arithmetic)

INF = 10**9  # Only finite totals <= 4000 use the capacity filter.
BOUNDS = (INF,41,41,41,41,47,45,83,36,39,42,49,56,50,44,47,44,
          INF,INF,61,72,39,66,75,82,INF,46,52,46,INF,82,75,66,39,72,61,
          INF,INF,44,47,44,50,56,49,42,39,36,83,45,47,41,41,41,41)
read_base_words = arithmetic.load_words


def read_words(source):
    words = read_base_words(source)
    assert all(w.startswith('012021') and w.endswith('120210') for w in words)
    return words


@lru_cache(None)
def capacity(a, u, v):
    lag = a + v - u
    assert lag > 0
    bound = BOUNDS[lag % 54] if lag % 54 else max(42, lag - 54)
    if bound == INF:
        return INF
    if u == v == 0:
        return bound
    previous = max(capacity(a, u-1, v) if u else -INF,
                   capacity(a, u, v-1) if v else -INF)
    return min(INF, previous + bound)


def volume(a, b, denominator, *, fill_left=True):
    difference, total = b-a, a+b
    assert total < INF
    upper = min(a, (total-1-denominator*difference)//(2*denominator))
    result = 0
    for u in range(max(0, -difference), upper+1):
        v = u+difference
        if v > b or u+v == 0:
            continue
        common = a-u
        assert common == b-v and common > 0
        if common <= capacity(a, u, v):
            result += math.comb(a, u)*math.comb(b, v)*2**(u if fill_left else v)
    return result


arithmetic.load_words = read_words
arithmetic.event_volume = volume
reported_values = []


def report_decimal(value, digits=40):
    """Outward decimal rounding; positions 6 and 7 are lower margins."""
    index = len(reported_values)
    reported_values.append(value)
    numerator = value.numerator * 10**digits
    scaled = numerator // value.denominator
    if index not in (6, 7) and numerator % value.denominator:
        scaled += 1
    sign = '-' if scaled < 0 else ''
    raw = str(abs(scaled)).rjust(digits+1, '0')
    return sign + raw[:-digits] + '.' + raw[-digits:]


arithmetic.decimal = report_decimal
if __name__ == '__main__':
    arithmetic.main()
    assert len(reported_values) == 10
    maximum, r0, r1, finite0, finite1, combined, slope, constant, tail0, tail1 = reported_values
    assert maximum < Fraction(158118, 10**9) < Fraction(1, 6000)
    assert finite0 < Fraction(364755781, 10**12)
    assert finite1 < Fraction(163709727665, 10**12)
    assert tail0 < Fraction(1, 10**27) and tail1 < Fraction(1, 10**24)
    assert r0 < Fraction(364756, 10**9)
    assert combined < Fraction(203468108, 10**9)
    assert slope > 0 and constant > 0
    print('PAPER_RATIONAL_BOUNDS_PASS')
