"""Iterative alignment capacities and independent rational LLL evaluation."""
from functools import lru_cache
import importlib.util
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'independent_arithmetic', ROOT / 'base/verifiers/independent_verify_d227_lll.py')
arithmetic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(arithmetic)
INF = 10**9
BOUNDS = (INF,41,41,41,41,47,45,83,36,39,42,49,56,50,44,47,44,
          INF,INF,61,72,39,66,75,82,INF,46,52,46,INF,82,75,66,39,72,61,
          INF,INF,44,47,44,50,56,49,42,39,36,83,45,47,41,41,41,41)
read_base_words = arithmetic.words


def read_words(source):
    words = read_base_words(source)
    for position, symbol in enumerate('012021'):
        assert all(w[position] == symbol for w in words)
    for position, symbol in enumerate('120210', 48):
        assert all(w[position] == symbol for w in words)
    return words


@lru_cache(None)
def capacity(a, u, v):
    table = [[0]*(v+1) for _ in range(u+1)]
    for i in range(u+1):
        for j in range(v+1):
            lag = a+j-i
            assert lag > 0
            bound = BOUNDS[lag % 54] if lag % 54 else (42 if lag == 54 else lag-54)
            previous = 0 if i == j == 0 else max(
                table[i-1][j] if i else -INF, table[i][j-1] if j else -INF)
            table[i][j] = min(INF, previous+bound)
    return table[u][v]


def volume(left, right, denominator, *, fill_left=True):
    total, result = left+right, 0
    assert total < INF
    for deficit in range(1, (total-1)//denominator+1):
        if (total-deficit) % 2:
            continue
        common = (total-deficit)//2
        if not 0 < common <= min(left, right):
            continue
        u, v = left-common, right-common
        if common <= capacity(left, u, v):
            result += math.comb(left, common)*math.comb(right, common)*2**(u if fill_left else v)
    return result


arithmetic.words = read_words
arithmetic.volume = volume
if __name__ == '__main__':
    arithmetic.main()
