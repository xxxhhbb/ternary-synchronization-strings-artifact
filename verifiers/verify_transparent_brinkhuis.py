"""Independent finite checks for the six-word Brinkhuis source."""

from itertools import product


B = {
    (0, 0): "210201202120102012",
    (0, 1): "210201021202102012",
    (1, 0): "021012010201210120",
    (1, 1): "021012102010210120",
    (2, 0): "102120121012021201",
    (2, 1): "102120210121021201",
}


def is_square_free(word):
    """Return False exactly when word has a nonempty contiguous square."""
    n = len(word)
    for start in range(n):
        for period in range(1, (n - start) // 2 + 1):
            if word[start : start + period] == word[
                start + period : start + 2 * period
            ]:
                return False
    return True


def outer_words(length):
    return (word for word in product(range(3), repeat=length) if is_square_free(word))


def main():
    words = list(B.values())
    assert all(len(word) == 18 for word in words)
    assert len(set(words)) == 6

    checked_outputs = 0
    checked_triples = 0
    for length in range(1, 6):
        for outer in outer_words(length):
            for choices in product(range(2), repeat=length):
                output = "".join(B[a, r] for a, r in zip(outer, choices))
                assert is_square_free(output), (outer, choices)
                checked_outputs += 1
                if length == 3:
                    checked_triples += 1
    assert checked_outputs == 1374
    assert checked_triples == 96

    checked_nonboundary_occurrences = 0
    for left_symbol in range(3):
        for right_symbol in range(3):
            if left_symbol == right_symbol:
                continue
            for left_choice, right_choice in product(range(2), repeat=2):
                pair = B[left_symbol, left_choice] + B[right_symbol, right_choice]
                for offset in range(1, 18):
                    for candidate in words:
                        assert pair[offset : offset + 18] != candidate
                        checked_nonboundary_occurrences += 1
    assert checked_nonboundary_occurrences == 2448

    assert len({word[:7] for word in words}) == 6
    assert len({word[-7:] for word in words}) == 6

    print("PASS: finite Brinkhuis source checks")
    print(f"  occurrence-wise outputs of outer lengths 1..5: {checked_outputs}")
    print(f"  corrected length-three cases: {checked_triples}")
    print(f"  non-boundary codeword comparisons: {checked_nonboundary_occurrences}")
    print("  distinct seven-symbol prefixes: 6")
    print("  distinct seven-symbol suffixes: 6")


if __name__ == "__main__":
    main()
