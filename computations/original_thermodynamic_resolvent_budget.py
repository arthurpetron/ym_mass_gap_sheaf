"""Exact scalar budget for the original fixed-spacing two-step resolvent.

This checks only the scalar arithmetic used by the Lean geometric-series
argument. It is not an independent Yang--Mills estimate or a proof oracle.
Run: python3 -m computations.original_thermodynamic_resolvent_budget
"""

from fractions import Fraction


def certificate_candidate() -> dict[str, Fraction]:
    one_step_squared_rate = Fraction(1, 2)
    two_step_squared_rate = one_step_squared_rate**2
    partial_sum_squared_ceiling = Fraction(4)
    assert two_step_squared_rate * partial_sum_squared_ceiling == 1
    assert 2 + 2 * two_step_squared_rate * partial_sum_squared_ceiling == 4
    assert partial_sum_squared_ceiling * Fraction(1, 4) == 1
    return {
        "one_step_squared_rate": one_step_squared_rate,
        "two_step_squared_rate": two_step_squared_rate,
        "partial_sum_squared_ceiling": partial_sum_squared_ceiling,
        "tail_tolerance_factor": Fraction(1, 4),
    }


if __name__ == "__main__":
    for name, value in certificate_candidate().items():
        print(f"{name} = {value}")
