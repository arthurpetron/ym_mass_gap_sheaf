"""Exact, untrusted dimension/exponent and bounded radial-tail pilot.

The actual conditional-return inequality is proved in Lean. These checks
test its arithmetic constants, not a spectral gap or a continuum claim.
High-label source powers are avoided; only bounded radial samples are summed.
"""

from fractions import Fraction
from math import prod
from random import Random

from bf4_cube_balanced_descent import label


def check(spins: tuple[int, ...]) -> None:
    radius = max(spins)
    target = tuple(label(radius, s) for s in spins)
    source_energy = sum(s * (s + 2) for s in spins)
    target_energy = sum(s * (s + 2) for s in target)
    assert target_energy + radius * radius // 72 <= source_energy
    assert prod(s + 1 for s in spins) <= (radius + 1) ** 6
    assert prod(t + 1 for t in target) >= 1


def main() -> None:
    rng = Random(260913)
    count = 0
    for _ in range(3000):
        radius = rng.randrange(1400, 100_000)
        parity = radius % 2
        spins = (radius,) + tuple(2 * rng.randrange(radius // 2 + 1) + parity
                                  for _ in range(5))
        check(spins)
        count += 1
    for radius in range(1400, 1501):
        for low in (radius % 2, radius // 2, radius):
            check((radius, low, low, low, low, low))
            count += 1
        assert 13 + radius * radius // 72 <= (radius + 1) ** 2 // 72
        assert (radius + 2) ** 12 <= 4096 * (radius + 1) ** 12
    assert 4096 * 1401 ** 12 <= 2 ** 144
    assert 144 <= 1400 ** 2 // 72
    tail_count = 0
    for w in (Fraction(0), Fraction(1, 400), Fraction(1, 10), Fraction(1, 2)):
        assert 4096 * w ** 13 <= Fraction(1, 2)
        for start in (1400, 1401, 1500):
            terms = [4096 * (m + 1) ** 12 * w ** (m * m // 72)
                     for m in range(start, start + 8)]
            for length in (0, 1, 3, 8):
                assert sum(terms[:length]) <= 2 * terms[0]
                tail_count += 1
    print(f"PASS: {count} exact cube dimension/exponent checks")
    print(f"PASS: {tail_count} exact degree-12 radial tails and seed <= 1")
    print("For M>=1400: C4(target)+floor(M^2/72)<=C4(source)")
    print("Self-return envelope: 4096*(M+1)^6*w^floor(M^2/72)")
    print("Degree-12 radial envelope has successor ratio at most 1/2.")


if __name__ == "__main__":
    main()
