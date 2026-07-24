"""Regression tests for the exact Core-B diagonal-cumulative scout."""

from __future__ import annotations

import pytest

from computations.core_b_diagonal_cumulative_scout import (
    canonical_consumer_report,
    even_low_diagonal_offset,
    payment_report,
    predicted_canonical_consumer_content,
    predicted_canonical_consumer_reserve,
    predicted_even_low_region_content,
    predicted_low_region_content,
    predicted_low_region_reserve,
    predicted_payment_length,
    verify_canonical_consumer,
    verify_even_low_region_prefix,
    verify_low_region_closed_forms,
    verify_predicted_minimum,
)


@pytest.mark.parametrize(
    ("row", "offset", "length"),
    [
        (1, 0, 1),
        (4, 0, 2),
        (5, 0, 3),
        (5, 1, 2),
        (6, 0, 4),
        (6, 1, 3),
        (6, 2, 2),
        (6, 3, 1),
    ],
)
def test_predicted_diagonal_length_is_exact_for_checked_cells(
    row: int, offset: int, length: int
) -> None:
    assert predicted_payment_length(row, offset) == length
    assert verify_predicted_minimum(row, offset)


def test_pair_repairs_first_zero_reserve_cell() -> None:
    single = payment_report(4, 0, 1)
    paired = payment_report(4, 0, 2)
    assert single.reserve == 0
    assert not single.paid
    assert paired.reserve == 614400
    assert paired.paid


@pytest.mark.parametrize("row", [3, 4, 5, 6])
def test_low_region_common_content_and_reserve_closed_forms(row: int) -> None:
    assert predicted_low_region_content(row) == 4 * row**2 + 4 * row - 2
    assert predicted_low_region_reserve(row) == 4 * row**5 * (row + 1) ** 2 * (row + 2)
    assert all(verify_low_region_closed_forms(row, offset) for offset in range(row - 2))


def test_invalid_diagonal_indices_are_rejected() -> None:
    with pytest.raises(ValueError, match="row one"):
        predicted_payment_length(0, 0)
    with pytest.raises(ValueError, match="nonnegative"):
        predicted_payment_length(1, -1)
    with pytest.raises(ValueError, match="positive"):
        payment_report(1, 0, 0)


@pytest.mark.parametrize("row", [4, 5, 6])
def test_adjacent_even_low_diagonal_has_zero_constant_reserve(row: int) -> None:
    assert predicted_even_low_region_content(row) == 4 * row**2 - 4
    for length in range(1, row - 2):
        offset = even_low_diagonal_offset(row, length)
        report = payment_report(row, offset, length)
        assert report.reserve == 0
        assert not report.paid
        assert verify_even_low_region_prefix(row, length)


def test_canonical_consumer_parity_formulas_and_true_endpoint_payment() -> None:
    for length in range(1, 8):
        report = canonical_consumer_report(length)
        assert report.content == predicted_canonical_consumer_content(length)
        assert report.reserve == predicted_canonical_consumer_reserve(length)
        assert report.paid_at_worst_endpoint
        assert report.paid_with_sixfold_slack
        assert report.uncancelled_adverse_at_half >= report.discounted_adverse_at_half
        assert report.uncancelled_paid_with_fourfold_slack
        assert report.atomwise_adverse_at_half >= report.uncancelled_adverse_at_half
        assert report.atomwise_paid_with_twofold_slack
        assert verify_canonical_consumer(length)
