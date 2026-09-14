"""Bounded scalar/local-coordinate pilot, not an original-sum certificate."""

from fractions import Fraction
from itertools import product
import signal


def main():
    signal.alarm(30)
    radius = 33
    face_capacity = 6 * (2 * radius + 1) ** 4
    assert face_capacity == 120906726
    for center in range(80):
        for value in range(120):
            if abs(center - value) <= radius:
                corner = max(0, center - radius)
                assert corner <= value
                assert 0 <= value - corner < 2 * radius + 1
    for coordinates in range(6):
        words = set()
        strata = {}
        for profile in product(range(4), repeat=coordinates):
            word = tuple(index for index, units_at_index in enumerate(profile)
                         for _ in range(units_at_index))
            assert len(word) == sum(profile)
            assert all(symbol < coordinates for symbol in word)
            assert word not in words
            words.add(word)
            strata[sum(profile)] = strata.get(sum(profile), 0) + 1
        assert all(count <= coordinates ** mass for mass, count in strata.items())
    nome = Fraction(1, 1024)
    higher = 9 * nome ** 8
    units = 2 * face_capacity
    assert units * higher < Fraction(1, 2)
    prospective_relative = 8 * 4 ** 12 * 2 * units * higher
    assert prospective_relative < Fraction(1, 2 ** 20)
    local_rate = units * higher
    exact_relative = 8 * 4 ** 12 * local_rate / (1 - local_rate)
    assert exact_relative <= prospective_relative < Fraction(1, 2 ** 20)
    print(f"Radius {radius}: <= {face_capacity} physical faces; <= {units} replica coordinates.")
    print("9600 boundary/interior coordinate cases passed without enumerating the 4D region.")
    print("1365 bounded profiles: unit-word injection, mass and mass-stratum counts passed.")
    print(f"Prospective geometric-union relative cap: {prospective_relative} < 2^-20.")
    print(f"Mass-counting geometric relative cap: {exact_relative} < 2^-20.")
    print("This scalar check does NOT sum the original labels or include detached partitions.")


if __name__ == "__main__":
    main()
