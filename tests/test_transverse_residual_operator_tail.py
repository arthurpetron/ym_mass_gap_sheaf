"""Regression gates for the transverse residual Gram/Choi tail lift."""

from fractions import Fraction

import pytest

from computations.transverse_residual_operator_tail import (
    operator_tail_cauchy_step,
    transverse_residual_operator_tail,
)


def test_fixed_coupling_operator_tail_lifts_the_scalar_modulus() -> None:
    certificate = transverse_residual_operator_tail(
        Fraction(1, 2),
        5,
        Fraction(1, 2),
        5,
    )
    assert certificate.validates()
    assert certificate.residual_face_count == 21
    assert certificate.open_index_feature_slots == 18
    assert certificate.density_tail_compressed_trace_norm_bound == (
        certificate.density_tail.residual_uniform_tail_bound
        * certificate.retained_feature_norm_squared
    )
    assert certificate.density_tail_full_feature_trace_norm_bound == (
        certificate.density_tail.residual_uniform_tail_bound
        * certificate.full_feature_norm_squared_upper
    )


def test_full_measure_compression_stays_positive_without_truncation_claim() -> None:
    certificate = transverse_residual_operator_tail(
        Fraction(1, 2),
        5,
        Fraction(3, 4),
        8,
    )
    assert certificate.full_measure_gram_positive
    assert certificate.finite_full_measure_compression_positive
    assert certificate.finite_full_measure_choi_compression_cp
    assert not (
        certificate.character_truncated_density_positivity_proved_by_tail
    )
    assert not certificate.character_truncation_cp_inferred
    assert certificate.fixed_coupling_trace_class_cauchy_name
    assert not certificate.physical_source_target_choi_reconstructed


def test_feature_tail_retains_both_coherent_cross_corners() -> None:
    certificate = transverse_residual_operator_tail(
        Fraction(1, 2),
        8,
        Fraction(1, 2),
        8,
    )
    assert certificate.cross_trace_norm_bound**2 >= (
        certificate.cross_squared_bound
    )
    assert certificate.feature_compression_trace_norm_tail_bound == (
        2 * certificate.cross_trace_norm_bound
        + certificate.outside_diagonal_trace_norm_bound
    )
    assert certificate.orthogonal_intertwiner_projection_nonexpansive
    assert certificate.unitary_recoupling_invariant


def test_exact_fixed_coupling_cauchy_step_meets_a_rational_tolerance() -> None:
    step = operator_tail_cauchy_step(
        Fraction(1, 2),
        Fraction(1, 2),
        Fraction(1, 100000),
        8,
        8,
    )
    assert step.validates()
    assert step.meets_tolerance
    assert step.combined_trace_norm_bound < Fraction(1, 100000)

    coarse = operator_tail_cauchy_step(
        Fraction(1, 2),
        Fraction(1, 2),
        Fraction(1),
        5,
        5,
    )
    assert coarse.validates()
    assert not coarse.meets_tolerance


def test_operator_bound_also_controls_operator_norm_but_not_spacing_limit() -> None:
    certificate = transverse_residual_operator_tail(
        Fraction(3, 4),
        12,
        Fraction(3, 4),
        12,
    )
    assert (
        certificate.combined_finite_approximation_operator_norm_bound
        == certificate.combined_finite_approximation_trace_norm_bound
    )
    assert certificate.ambient_volume_independent
    assert not certificate.spacing_uniform_in_weak_coupling_limit
    assert (
        certificate.first_open_obligation
        == "assemble-all-label-source-target-choi-and-prove-cp-order"
    )


def test_invalid_operator_tail_inputs_fail_closed() -> None:
    with pytest.raises(ValueError, match="strictly between"):
        transverse_residual_operator_tail(
            Fraction(1),
            5,
            Fraction(1, 2),
            5,
        )
    with pytest.raises(ValueError, match="positive"):
        operator_tail_cauchy_step(
            Fraction(1, 2),
            Fraction(1, 2),
            Fraction(0),
            5,
            5,
        )
