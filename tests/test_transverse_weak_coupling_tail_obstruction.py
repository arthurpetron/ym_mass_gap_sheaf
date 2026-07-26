"""Exact gates for the BF4 fixed-cutoff weak-coupling obstruction."""

from fractions import Fraction

import pytest

from computations.transverse_weak_coupling_tail_obstruction import (
    fixed_cutoff_fails_requested_uniform_tolerance,
    fixed_cutoff_weak_coupling_obstruction,
)


def test_explicit_bernoulli_witnesses_are_exact() -> None:
    for cutoff in range(8):
        certificate = fixed_cutoff_weak_coupling_obstruction(cutoff)
        assert certificate.validates()
        assert 0 < certificate.witness_coupling < 1
        assert certificate.actual_identity_tail_term >= (
            certificate.certified_identity_tail_lower_bound
        )


def test_first_three_witnesses_are_pinned() -> None:
    zero = fixed_cutoff_weak_coupling_obstruction(0)
    one = fixed_cutoff_weak_coupling_obstruction(1)
    two = fixed_cutoff_weak_coupling_obstruction(2)
    assert (
        zero.first_omitted_casimir4,
        zero.witness_coupling,
        zero.certified_identity_tail_lower_bound,
    ) == (3, Fraction(5, 6), Fraction(2))
    assert (
        one.first_omitted_casimir4,
        one.witness_coupling,
        one.certified_identity_tail_lower_bound,
    ) == (8, Fraction(15, 16), Fraction(9, 2))
    assert (
        two.first_omitted_casimir4,
        two.witness_coupling,
        two.certified_identity_tail_lower_bound,
    ) == (15, Fraction(29, 30), Fraction(8))


def test_fixed_cutoff_absolute_strategy_stays_fail_closed() -> None:
    certificate = fixed_cutoff_fails_requested_uniform_tolerance(
        3,
        Fraction(1),
    )
    assert certificate.certified_identity_tail_lower_bound == Fraction(25, 2)
    assert not certificate.fixed_cutoff_uniform_absolute_tail_possible
    assert not certificate.fixed_cutoff_uniform_relative_tail_possible
    assert not certificate.spacing_uniform_residual_product_modulus_proved
    assert certificate.omitted_block_exceeds_retained_head
    assert (
        certificate.spacing_dependent_cutoff_or_all_label_regrouping_required
    )


def test_fixed_cutoff_relative_tail_exceeds_one_half() -> None:
    for cutoff in range(8):
        certificate = fixed_cutoff_weak_coupling_obstruction(cutoff)
        assert certificate.relative_block_last_label == 2 * cutoff + 1
        assert certificate.omitted_identity_block_lower_bound > (
            certificate.retained_identity_head_upper_bound
        )
        retained_count = cutoff + 1
        assert certificate.relative_tail_margin == Fraction(
            retained_count
            * (2 * retained_count + 1)
            * (5 * retained_count - 1),
            12,
        )
        # The complete omitted tail is larger still, so at this witness
        # coupling tail / (head + tail) is strictly greater than one half.
        assert not certificate.fixed_cutoff_uniform_relative_tail_possible


def test_invalid_requests_are_rejected() -> None:
    with pytest.raises(ValueError):
        fixed_cutoff_weak_coupling_obstruction(-1)
    with pytest.raises(ValueError):
        fixed_cutoff_fails_requested_uniform_tolerance(1, Fraction(-1))
    with pytest.raises(ValueError, match="below"):
        fixed_cutoff_fails_requested_uniform_tolerance(1, Fraction(9, 2))
