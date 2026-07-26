"""Exact gates for grouped backward-message order."""

from fractions import Fraction

import pytest

from computations.boundary_message_uniform_order import (
    endpoint_weight_cancellation,
    finite_grouped_message_order,
    intermediate_potential_harnack_obstruction,
    kinetic_boundary_message_uniform_order,
    physical_backward_message_order_frontier,
    uniform_kernel_limit_message_order,
)


def test_grouped_row_harnack_orders_every_backward_message() -> None:
    certificate = finite_grouped_message_order(
        ((4, 9), (7, 7)),
        (1, 2),
    )

    assert certificate.validates()
    assert certificate.backward_message == (Fraction(22), Fraction(21))
    assert certificate.row_ratio_lower == Fraction(7, 9)
    assert certificate.row_ratio_upper == Fraction(7, 4)
    assert certificate.message_ratio_lower == Fraction(21, 22)
    assert certificate.message_ratio_upper == 1
    assert certificate.common_reference_mass == Fraction(4, 9)
    assert certificate.terminal_message_independent_coefficient
    assert certificate.exact_markov_minorization


def test_positive_endpoint_spatial_weights_cancel_from_markovization() -> None:
    certificate = endpoint_weight_cancellation(
        ((2, 1), (1, 3)),
        (5, 7),
        (11, 13),
        (17, 19),
    )

    assert certificate.validates()
    assert (
        certificate.weighted_markov_kernel
        == certificate.core_updated_terminal_markov_kernel
    )
    assert certificate.source_endpoint_weight_cancels
    assert certificate.target_endpoint_weight_absorbed_into_terminal


def test_kinetic_23_cycle_message_order_is_spacing_uniform_after_grouping() -> None:
    for coupling in (
        Fraction(1, 2),
        Fraction(3, 4),
        Fraction(9, 10),
        Fraction(99, 100),
    ):
        certificate = kinetic_boundary_message_uniform_order(coupling)

        assert certificate.validates()
        assert certificate.grouped_coupling <= Fraction(1, 2)
        assert certificate.one_cycle_floor == Fraction(1055, 2272)
        assert certificate.one_cycle_ceiling == Fraction(3489, 2272)
        assert certificate.markov_common_mass == (
            Fraction(1055, 3489) ** 46
        )
        assert certificate.terminal_message_independent
        assert certificate.spacing_uniform_under_grouped_heat_cap
        assert not certificate.interior_spatial_feynman_kac_weights_included
        assert not certificate.physical_backward_message_order_proved


def test_invalid_grouped_order_inputs_fail_closed() -> None:
    with pytest.raises(ValueError):
        finite_grouped_message_order(((1, 0), (1, 1)), (1, 1))
    with pytest.raises(ValueError):
        finite_grouped_message_order(((1, 1),), (1,), reference_source=2)
    with pytest.raises(ValueError):
        endpoint_weight_cancellation(((1,),), (0,), (1,), (1,))
    with pytest.raises(ValueError):
        kinetic_boundary_message_uniform_order(Fraction(1))


def test_physical_frontier_is_reduced_to_the_interior_feynman_kac_harnack() -> None:
    frontier = physical_backward_message_order_frontier()

    assert frontier.validates()
    assert frontier.finite_grouped_row_ratio_theorem_proved
    assert frontier.backward_message_order_terminal_independent
    assert frontier.endpoint_spatial_weight_cancellation_proved
    assert frontier.correct_relative_message_coordinate == (
        "g_j=h_j/sqrt(W_spatial)"
    )
    assert frontier.kinetic_23_cycle_spacing_uniform_order_proved
    assert frontier.kinetic_markov_common_mass == (
        Fraction(1055, 3489) ** 46
    )
    assert not frontier.interior_spatial_feynman_kac_weights_included
    assert not frontier.physical_grouped_two_sided_harnack_proved
    assert not frontier.physical_spacing_uniform_backward_message_order_proved
    assert frontier.uniform_positive_kernel_limit_criterion_proved
    assert not frontier.physical_grouped_feynman_kac_uniform_limit_proved
    assert not frontier.physical_limit_kernel_strictly_positive_proved
    assert not frontier.global_floor_ceiling_potential_comparison_usable


def test_uniform_positive_kernel_limit_closes_message_order_stably() -> None:
    certificate = uniform_kernel_limit_message_order(
        ((4, 5), (6, 7)),
        (
            (Fraction(41, 10), Fraction(49, 10)),
            (Fraction(61, 10), Fraction(69, 10)),
        ),
        Fraction(1, 5),
    )

    assert certificate.validates()
    assert certificate.actual_uniform_error == Fraction(1, 10)
    assert certificate.limit_floor == 4
    assert certificate.approximating_floor == Fraction(19, 5)
    assert certificate.approximating_ceiling == Fraction(36, 5)
    assert certificate.terminal_independent_markov_common_mass == (
        Fraction(19, 36) ** 2
    )
    assert certificate.uniform_message_order_proved


def test_uniform_limit_error_must_stay_below_the_positive_floor() -> None:
    with pytest.raises(ValueError):
        uniform_kernel_limit_message_order(
            ((1, 2), (3, 4)),
            ((1, 2), (3, 4)),
            Fraction(1),
        )


def test_arbitrary_interior_potential_can_destroy_spacing_uniform_order() -> None:
    for denominator in (2, 3, 10, 100):
        certificate = intermediate_potential_harnack_obstruction(denominator)

        assert certificate.validates()
        assert certificate.terminal_independent_markov_common_mass == (
            Fraction(denominator, denominator**2 - denominator + 1)
        )
        assert (
            certificate.terminal_independent_markov_common_mass
            <= certificate.common_mass_upper_bound
            == Fraction(2, denominator)
        )
        assert certificate.arbitrary_positive_potential_uniform_order_refuted
        assert not certificate.physical_yang_mills_harnack_refuted

    with pytest.raises(ValueError):
        intermediate_potential_harnack_obstruction(1)
