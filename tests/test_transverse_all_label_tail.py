"""Regression gates for the BF4 transverse all-label Cauchy modulus."""

from fractions import Fraction

import pytest

from computations.transverse_all_label_tail import (
    CONNECTED_CORE_FACE_COUNT,
    DECORATION_FACE_COUNT,
    TRANSVERSE_RESIDUAL_FACE_COUNT,
    least_transverse_all_label_cutoff,
    transverse_all_label_uniform_tail,
)


def test_residual_tail_tensorizes_exactly() -> None:
    certificate = transverse_all_label_uniform_tail(Fraction(1, 2), 1)
    assert certificate.validates()
    assert certificate.connected_core_face_count == CONNECTED_CORE_FACE_COUNT
    assert certificate.decoration_face_count == DECORATION_FACE_COUNT
    assert certificate.residual_face_count == TRANSVERSE_RESIDUAL_FACE_COUNT
    assert certificate.composed_residual_uniform_tail_bound == (
        certificate.residual_uniform_tail_bound
    )
    assert certificate.normalized_haar_is_uniformly_nonexpansive
    assert certificate.boundary_uniform
    assert certificate.ambient_volume_independent
    assert not certificate.spacing_uniform_in_weak_coupling_limit


def test_all_label_function_exists_but_cp_frontier_stays_open() -> None:
    certificate = transverse_all_label_uniform_tail(Fraction(3, 4), 3)
    assert certificate.validates()
    assert certificate.coherent_all_label_residual_function_constructed
    assert not certificate.recoupling_amplitudes_controlled_by_this_tail
    assert not certificate.cp_order_domination_proved


def test_uniform_tail_decreases_along_sampled_cutoffs() -> None:
    bounds = tuple(
        transverse_all_label_uniform_tail(
            Fraction(1, 2),
            cutoff,
        ).residual_uniform_tail_bound
        for cutoff in range(1, 6)
    )
    assert all(
        right < left
        for left, right in zip(bounds[:-1], bounds[1:], strict=True)
    )


def test_constructive_cutoff_schedule_is_minimal() -> None:
    point = least_transverse_all_label_cutoff(
        Fraction(1, 2),
        Fraction(1, 10**6),
    )
    assert point.validates()
    assert point.residual_uniform_tail_bound <= point.tolerance
    if point.cutoff:
        try:
            previous = transverse_all_label_uniform_tail(
                point.coupling,
                point.cutoff - 1,
            )
        except ValueError:
            pass
        else:
            assert previous.residual_uniform_tail_bound > point.tolerance


def test_invalid_parameters_fail_closed() -> None:
    with pytest.raises(ValueError):
        transverse_all_label_uniform_tail(Fraction(1), 1)
    with pytest.raises(ValueError):
        least_transverse_all_label_cutoff(Fraction(1, 2), Fraction(0))
