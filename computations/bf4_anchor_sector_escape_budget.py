"""Exact pilot for the fixed-anchor, extent-one sector escape budget.

Untrusted arithmetic only: Lean independently checks the rational constants
and proves the all-cutoff series and physical partition comparisons.
The ambient corner box uses 6*n^4 faces, not the usual closed-box count.
"""

from fractions import Fraction


def main() -> None:
    coupling = Fraction(1, 400)
    degree = 13
    face_count = 6 * 2**4
    ratio = 2**degree * coupling**3
    ceiling = 1 / (1 - ratio)
    partition_ceiling = Fraction(65, 64)
    failure = Fraction(384, 425)
    escape = failure * (partition_ceiling - 1)
    demand = 1 - failure - escape
    assert ratio == Fraction(2, 15625)
    assert ceiling == Fraction(15625, 15623)
    assert 1 + ratio * ceiling == ceiling
    assert ceiling**face_count <= partition_ceiling
    # Small blocks avoid a deep evaluator stack in the Lean certificate.
    assert ceiling**16 <= Fraction(10021, 10000)
    assert Fraction(10021, 10000) ** 6 <= partition_ceiling
    assert escape == Fraction(6, 425)
    assert demand == Fraction(7, 85) > 0
    traffic_floor = demand / partition_ceiling
    assert traffic_floor == Fraction(448, 5525) > 0
    print(f"anchor={coupling}; degree={degree}; ambient faces={face_count}")
    print(f"successive ratio={ratio}; one-face ceiling={ceiling}")
    print(f"tensor ceiling <= {partition_ceiling}: PASS (exact rational)")
    print(f"relative escape <= {escape}; successful demand >= {demand}")
    print(f"partition-normalized sector traffic >= {traffic_floor}")
    print("Scope: fixed anchor and extent one; not a volume or continuum bound.")


if __name__ == "__main__":
    main()
