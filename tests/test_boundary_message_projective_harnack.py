"""Exact gates for the projective physical Feynman--Kac route."""

from fractions import Fraction

import pytest

from computations.boundary_message_projective_harnack import (
    cross_ratio_backward_message_order,
    intrinsic_perron_remainder_budget,
    localized_rank_one_profile_witness,
    physical_feynman_kac_projective_route,
    relative_rank_one_projective_order,
)


def test_cross_ratio_orders_every_doob_row_for_every_terminal_message() -> None:
    certificate = cross_ratio_backward_message_order(
        ((4, 9), (7, 7)),
        (1, 2),
    )

    assert certificate.validates()
    assert certificate.max_four_boundary_cross_ratio == Fraction(9, 4)
    assert certificate.common_markov_mass == Fraction(4, 9)
    assert certificate.every_source_pair_ordered
    assert certificate.terminal_message_independent_coefficient
    assert certificate.row_column_scaling_invariant


def test_row_and_column_profiles_cancel_from_the_cross_ratio() -> None:
    core = cross_ratio_backward_message_order(
        ((4, 9), (7, 7)),
        (1, 2),
    )
    scaled = cross_ratio_backward_message_order(
        ((4 * 5 * 11, 9 * 5 * 13), (7 * 7 * 11, 7 * 7 * 13)),
        (1, 2),
    )

    assert scaled.validates()
    assert scaled.max_four_boundary_cross_ratio == core.max_four_boundary_cross_ratio
    assert scaled.common_markov_mass == core.common_markov_mass


def test_relative_rank_one_convergence_closes_projective_order() -> None:
    certificate = relative_rank_one_projective_order(
        (
            (Fraction(21, 2), Fraction(19, 10)),
            (Fraction(57, 4), Fraction(63, 20)),
        ),
        (2, 3),
        (5, 1),
        (7, 11),
        Fraction(1, 20),
    )

    assert certificate.validates()
    assert certificate.actual_relative_error == Fraction(1, 20)
    assert certificate.certified_cross_ratio_ceiling == (Fraction(21, 19) ** 2)
    assert certificate.certified_common_markov_mass == (Fraction(19, 21) ** 2)
    assert certificate.spacing_dependent_profiles_allowed
    assert not certificate.absolute_kernel_floor_required


def test_localized_rank_one_profiles_need_no_absolute_positive_limit() -> None:
    for parameter in (2, 10, 100):
        certificate = localized_rank_one_profile_witness(parameter)

        assert certificate.validates()
        assert certificate.absolute_kernel_floor == Fraction(
            1,
            (parameter + 1) ** 2,
        )
        assert certificate.absolute_kernel_floor <= Fraction(
            1,
            parameter**2,
        )
        assert certificate.max_four_boundary_cross_ratio == 1
        assert certificate.common_markov_mass == 1
        assert certificate.absolute_floor_collapses
        assert certificate.projective_order_stays_exact


def test_intrinsic_perron_budget_returns_an_exact_common_mass() -> None:
    certificate = intrinsic_perron_remainder_budget(
        Fraction(2),
        Fraction(1, 4),
        4,
    )

    assert certificate.validates()
    assert certificate.relative_rank_one_error == Fraction(1, 64)
    assert certificate.common_markov_mass == Fraction(63, 65) ** 2
    assert certificate.closes_projective_harnack


def test_physical_route_fails_closed_at_the_uniform_cross_ratio() -> None:
    route = physical_feynman_kac_projective_route()

    assert route.validates()
    assert route.cross_ratio_orders_every_terminal_message
    assert route.source_target_profiles_cancel_exactly
    assert route.spacing_dependent_perron_profiles_allowed
    assert not route.absolute_positive_kernel_limit_required
    assert route.fixed_coupling_compact_positivity_improving
    assert route.fixed_coupling_intrinsic_perron_convergence_available
    assert route.fixed_coupling_two_buffer_remainder_formula == ("delta_s,m <= C_s^2 q_s^(m-2)")
    assert route.interior_spatial_weights_in_physical_grouped_kernel
    assert route.spatial_complex_two_sphere_homotopy_type_certified
    assert route.unique_flat_spatial_su2_gauge_orbit_proved
    assert route.multiple_topological_flat_wells_refuted
    assert route.linearized_spatial_curvature_coercivity_floor == Fraction(
        1,
        11,
    )
    assert route.global_nonlinear_spatial_curvature_coercivity_constant == Fraction(1, 81)
    assert route.nonlinear_global_spatial_curvature_coercivity_proved
    assert route.linearized_temporal_relative_coupling_rank == 5
    assert not route.microscopic_temporal_ellipticity_on_all_23_cycles
    assert route.exact_nonlinear_five_holonomy_factorization_proved
    assert route.eighteen_dimensional_fibers_conditionally_integrated
    assert route.five_holonomy_feynman_kac_operator_identity_proved
    assert not route.spatial_temporal_hypocoercive_perron_bound_proved
    assert route.boundary_connected_interaction_target_identified
    assert not route.spacing_uniform_physical_cross_ratio_proved
    assert not route.spacing_uniform_intrinsic_buffer_bound_proved
    assert not route.spacing_uniform_bulk_spectral_budget_proved
    assert not route.boundary_spanning_connected_expansion_bound_proved
    assert not route.physical_backward_message_order_proved
    assert route.first_open_obligation == (
        "prove-spacing-uniform-five-holonomy-effective-perron-budget"
    )


def test_projective_inputs_fail_closed() -> None:
    with pytest.raises(ValueError):
        cross_ratio_backward_message_order(((1, 0), (1, 1)), (1, 1))
    with pytest.raises(ValueError):
        relative_rank_one_projective_order(
            ((1, 1), (1, 1)),
            (1, 1),
            (1, 1),
            (1, 1),
            Fraction(1),
        )
    with pytest.raises(ValueError):
        localized_rank_one_profile_witness(1)
    with pytest.raises(ValueError):
        intrinsic_perron_remainder_budget(
            Fraction(2),
            Fraction(1, 2),
            1,
        )
