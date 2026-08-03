"""Exact regression gates for the two cutoff-one Haar-five values."""

from computations.cutoff_one_haar5_moment_balance import (
    EXPECTED_CENTERED_DEFECT_NUMERATOR,
    EXPECTED_CENTERED_NUMERATOR,
    EXPECTED_HAAR5_DIFFERENCE,
    EXPECTED_VACUUM_ROW_HAAR5,
    cutoff_one_haar5_moment_balance,
    render_balance_report,
)
from computations.whole_corrected_slab_kraus import EXPECTED_BINARY_MASS


def test_two_haar_five_values_are_evaluated_and_strictly_compared() -> None:
    balance = cutoff_one_haar5_moment_balance()

    assert balance.validates()
    assert balance.based_cycles == (0, 4, 5, 6, 10)
    assert balance.closed_surface_count == 128
    assert balance.vacuum_row_surface_count == 2
    assert balance.vacuum_row == EXPECTED_VACUUM_ROW_HAAR5
    assert balance.constant_quadratic == EXPECTED_BINARY_MASS
    assert balance.comparison_difference == EXPECTED_HAAR5_DIFFERENCE
    assert balance.haar5_values_strictly_ordered_for_positive_w


def test_exact_centered_vacuum_balance_has_positive_defect() -> None:
    balance = cutoff_one_haar5_moment_balance()

    assert balance.centered_numerator == EXPECTED_CENTERED_NUMERATOR
    assert balance.centered_defect_numerator == EXPECTED_CENTERED_DEFECT_NUMERATOR
    assert balance.centered_sides_strictly_differ_for_positive_w
    report = render_balance_report(balance)
    assert "signed centered moment  = N(w) / C(w)" in report
    assert "physical centered moment= N(w) / C(w)^2" in report
    assert "only at the degenerate point w = 0" in report
