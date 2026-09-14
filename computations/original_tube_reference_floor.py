"""Exact scalar pilot for a collar-relative original tube reference floor.

This does not evaluate the full ambient numerator or bound otherCoreRemainder.
Lean independently proves the geometric count and all inequalities.
"""

from fractions import Fraction
import signal


def main():
    signal.alarm(30)
    collar_cap = 6 * (8 + 4 * 12)
    square_cap = 2 * collar_cap
    assert (collar_cap, square_cap) == (336, 672)
    cases = 0
    for delta in (Fraction(0), Fraction(1, 8388608), Fraction(1, 100), Fraction(1, 2)):
        for count in (0, 1, 2, 8, 336, 672, 1024):
            assert (1 - count * delta) * (1 + delta) ** count <= 1
            cases += 1
    print(f"linear inverse invariant: {cases} exact rational checks")
    print(f"collar cap={collar_cap}; squared comparison exponent={square_cap}")
    for denominator in (1024, 2048, 4096):
        nome = Fraction(1, denominator)
        delta = 128 * nome ** 3
        linear_floor = 1 - square_cap * delta
        ceiling = (1 + delta) ** square_cap
        assert Fraction(1, 2) <= linear_floor
        assert ceiling <= 2
        assert Fraction(1, 2) <= 1 / ceiling
        reference_floor = nome ** 36 / 2
        assert reference_floor > 0
        print(f"nome=1/{denominator}; delta={delta}; 1-672*delta={linear_floor}; "
              f"inverse collar ceiling~{float(1 / ceiling):.10f}; "
              f"reference coefficient~{float(reference_floor):.6e}")
    print("OPEN: signed other-core bound, positive full response, limit persistence, continuum/Clay.")


if __name__ == "__main__":
    main()
