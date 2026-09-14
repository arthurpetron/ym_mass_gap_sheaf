"""Exact scalar pilot; the original four-pair count is proved in Lean.

This does not bound the joint power-42 channel or any higher-power term.
Lean independently checks the arithmetic and its use on original sums.
"""

from fractions import Fraction
import signal


def main():
    signal.alarm(30)
    nome = Fraction(1, 1024)
    odd_rate = 4 * nome ** 3
    per_pair = 8 * odd_rate ** 14
    pair_count_cap = 4
    detached_square_cap = 2
    summed = pair_count_cap * per_pair
    restored = detached_square_cap * summed
    assert per_pair / nome ** 36 == Fraction(1, 2 ** 29)
    assert summed / nome ** 36 == Fraction(1, 2 ** 27)
    assert restored / nome ** 36 == Fraction(1, 2 ** 26)
    reserve = Fraction(1, 4) - Fraction(1, 2 ** 19) - Fraction(1, 2 ** 26)
    assert reserve > 0
    print("At fixed nome 1/1024, all fourteen occupations fundamental:")
    print("Per-pair envelope / w^36 = 2^-29.")
    print("At most four original means pairs: summed envelope / w^36 = 2^-27.")
    print("Restoring each original detached partition square: relative cap 2^-26.")
    print(f"Remaining reference coefficient: {reserve} > 0.")
    print("OPEN: joint power 42, higher powers, positive full response, continuum/Clay.")


if __name__ == "__main__":
    main()
