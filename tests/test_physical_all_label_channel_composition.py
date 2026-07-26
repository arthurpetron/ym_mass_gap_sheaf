"""Exact gates for the BF4 mass-preserving channel promotion."""

from fractions import Fraction

import pytest

from computations.physical_all_label_channel_composition import (
    dyadic_fixed_distance_iteration_no_go,
    finite_peter_weyl_channel_carrier,
    mass_preserving_channel_promotion,
)


def test_finite_channel_carrier_has_positive_invertible_heat_deweighting() -> None:
    carrier = finite_peter_weyl_channel_carrier(2, Fraction(1, 2))

    assert carrier.validates()
    assert carrier.one_slot_dimension == 6
    assert carrier.source_dimension == carrier.target_dimension == 6**9
    assert carrier.one_slot_heat_weights == (
        Fraction(1),
        Fraction(1, 4),
        Fraction(3, 256),
    )
    assert carrier.every_heat_weight_strictly_positive
    assert carrier.heat_weight_chi_congruence_invertible


def test_positive_measure_difference_normalizes_to_a_cptp_residual() -> None:
    promotion = mass_preserving_channel_promotion(
        Fraction(1, 2),
        Fraction(1, 2),
    )

    assert promotion.validates()
    assert 0 < promotion.domination_coefficient < 1
    assert promotion.positive_difference_measure_mass == (
        1 - promotion.domination_coefficient
    )
    assert promotion.normalized_residual_measure_mass == 1
    assert promotion.normalized_residual_random_unitary_channel_cptp
    assert promotion.normalized_residual_channel_unital
    assert promotion.residual_channel_coefficient == (
        1 - promotion.domination_coefficient
    )


def test_all_label_channel_is_projective_even_though_its_choi_is_not_trace_class() -> None:
    promotion = mass_preserving_channel_promotion(
        Fraction(3, 4),
        Fraction(1, 2),
    )

    assert promotion.projective_cutoff_restriction_compatible
    assert promotion.normal_all_label_random_unitary_channel_defined
    assert not promotion.unweighted_all_label_choi_trace_class
    assert promotion.abstract_same_carrier_convolution_composition_proved
    assert not promotion.physical_consecutive_slab_rg_identification_proved


def test_iterating_the_microscopic_certificate_loses_fixed_distance_mass() -> None:
    previous_bound = Fraction(1)
    for level in range(1, 7):
        no_go = dyadic_fixed_distance_iteration_no_go(level)

        assert no_go.validates()
        assert no_go.microscopic_step_count == 2**level
        assert no_go.corridor_tagged_history_mass_upper_bound <= (
            no_go.spacing_power_bound_on_corridor_tagged_mass
        )
        assert no_go.bernoulli_corridor_history_upper_bound_proved
        assert (
            no_go.spacing_power_bound_on_corridor_tagged_mass
            < previous_bound
        )
        assert not no_go.corridor_tagged_composition_spacing_uniform
        assert not no_go.direct_grouped_relative_order_refuted
        previous_bound = no_go.spacing_power_bound_on_corridor_tagged_mass


def test_invalid_channel_carrier_and_dyadic_inputs_fail_closed() -> None:
    with pytest.raises(ValueError):
        finite_peter_weyl_channel_carrier(-1, Fraction(1, 2))
    with pytest.raises(ValueError):
        finite_peter_weyl_channel_carrier(1, Fraction(1))
    with pytest.raises(ValueError):
        dyadic_fixed_distance_iteration_no_go(0)
