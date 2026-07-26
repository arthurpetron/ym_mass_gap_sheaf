"""Regression gates for the exact BF4 cutoff-one CP-order pilot."""

from fractions import Fraction

import pytest

from computations.transverse_cutoff_one_cp_order import (
    cutoff_one_cp_order_audit,
    cutoff_one_cp_order_pilot,
    evaluate_moment_matrix,
    shifted_moment_matrix,
    transverse_cutoff_one_moment_polynomial_matrix,
)


def test_moment_polynomial_matrix_is_exact_and_sparse() -> None:
    matrix = transverse_cutoff_one_moment_polynomial_matrix()
    assert len(matrix) == 10
    assert all(len(row) == 10 for row in matrix)
    assert sum(bool(entry) for row in matrix for entry in row) == 28
    assert len(
        {
            tuple(sorted(entry.items()))
            for row in matrix
            for entry in row
        }
    ) == 7
    assert matrix[8][8] == {
        0: Fraction(1),
        6: Fraction(1, 4),
        10: Fraction(5, 256),
        12: Fraction(1, 512),
    }
    assert matrix[8][9] == {
        2: Fraction(1),
        4: Fraction(1, 16),
        8: Fraction(17, 128),
        10: Fraction(1, 1024),
        12: Fraction(1, 256),
    }


def test_zero_activity_is_the_haar_reference_symbol() -> None:
    matrix = evaluate_moment_matrix(Fraction(0))
    assert matrix == tuple(
        tuple(Fraction(row == column) for column in range(10))
        for row in range(10)
    )


def test_strong_coupling_pilot_has_exact_cp_order_mass() -> None:
    pilot = cutoff_one_cp_order_pilot(Fraction(1, 2), Fraction(1, 3))
    assert pilot.validates()
    assert pilot.cutoff_one_schur_map_cp
    assert pilot.corridor_difference_cp
    assert all(pivot > 0 for pivot in pilot.shifted_pivots)
    assert pilot.shifted_matrix == shifted_moment_matrix(
        Fraction(1, 2),
        Fraction(1, 3),
    )
    assert not pilot.physical_corrected_slab_choi_reconstructed


def test_weak_coupling_cutoff_one_truncation_has_exact_cp_obstruction() -> None:
    audit = cutoff_one_cp_order_audit()
    assert audit.validates()
    assert not audit.weak_pilot.cutoff_one_schur_map_cp
    assert audit.weak_obstruction_features == (8, 9)
    assert audit.weak_obstruction_quadratic_form == Fraction(
        -2738971,
        1048576,
    )
    assert audit.weak_obstruction_principal_determinant == Fraction(
        -67554016350623,
        4398046511104,
    )
    assert audit.weak_obstruction_principal_block == (
        (
            Fraction(10962521, 2097152),
            Fraction(3425373, 524288),
        ),
        (
            Fraction(3425373, 524288),
            Fraction(10962521, 2097152),
        ),
    )


def test_audit_remains_fail_closed_beyond_the_finite_schur_pilot() -> None:
    audit = cutoff_one_cp_order_audit()
    assert audit.finite_schur_cp_equivalence_proved
    assert not audit.finite_compression_sufficient_for_physical_cp_order
    assert not audit.all_label_completion_proved
    assert (
        audit.first_open_obligation
        == "reconstruct-open-index-all-label-choi-and-prove-cp-domination"
    )


def test_invalid_pilot_parameters_fail_closed() -> None:
    with pytest.raises(ValueError, match="nonnegative"):
        evaluate_moment_matrix(Fraction(-1))
