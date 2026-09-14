"""Exact scalar budget for a finite certificate of the ORIGINAL response.

This does not evaluate the Yang--Mills response or certify its positivity.
It checks only the two-error interval and the completeness margin; Lean
independently checks the arithmetic and pins the sampled covariance.
"""

from fractions import Fraction


def check_budget() -> None:
    volume_error = Fraction(1, 8)
    representative_error = Fraction(1, 8)
    total_error = volume_error + representative_error
    retained_floor = Fraction(1, 2)
    assert 1 - total_error == retained_floor + total_error
    assert 0 < retained_floor
    print("two_error_fraction =", total_error)
    print("retained_positive_floor_fraction =", retained_floor)
    print("physical response evaluation: NOT PERFORMED")


if __name__ == "__main__":
    check_budget()
