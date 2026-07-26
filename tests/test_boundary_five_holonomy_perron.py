"""Exact Gaussian spectrum and spacing budget for the reduced transfer."""

from fractions import Fraction

from computations.boundary_five_holonomy_perron import (
    five_holonomy_gaussian_perron,
    five_holonomy_spacing_budget,
)


def test_exact_five_holonomy_generalized_spectrum() -> None:
    certificate = five_holonomy_gaussian_perron()

    assert certificate.validates()
    assert certificate.spatial_form_determinant == 6
    assert certificate.kinetic_form_determinant == Fraction(1, 384)
    assert certificate.generalized_operator_trace == 24
    assert certificate.generalized_operator_determinant == 4**3 * 6**2
    assert certificate.generalized_eigenvalue_four_multiplicity == 3
    assert certificate.generalized_eigenvalue_six_multiplicity == 2
    assert certificate.generalized_minimal_polynomial_identity
    assert certificate.gaussian_slow_ratio_algebraic_form == "3-2*sqrt(2)"
    assert certificate.gaussian_fast_ratio_algebraic_form == "4-sqrt(15)"
    assert certificate.gaussian_largest_nonvacuum_ratio_upper == Fraction(
        1,
        5,
    )
    assert certificate.eventual_nonlinear_spectral_ratio_upper == Fraction(
        1,
        4,
    )


def test_global_buffer_closes_dyadic_spacing_model() -> None:
    certificate = five_holonomy_spacing_budget()

    assert certificate.validates()
    assert certificate.single_plaquette_log_ratio_exponent == 9
    assert certificate.symmetric_effective_heat_factor_count == 48
    assert certificate.effective_kernel_log_ratio_exponent == 432
    assert certificate.perron_buffer_power_of_kernel_ratio == 2
    assert certificate.buffer_square_log_exponent == 1728
    assert certificate.sufficient_physical_length_strict_threshold == ("L>1728/kappa")
    assert certificate.dyadic_model_heat_time_over_spacing_floor == 1
    assert certificate.dyadic_model_sufficient_integer_length == 1729
    assert certificate.dyadic_model_spacing_uniform_perron_budget_proved
    assert certificate.one_loop_af_heat_time_over_spacing_diverges
    assert certificate.constructive_bare_af_floor_theorem == (
        "YMGap.Continuum.BareAFDiagnostic.BareAFImpliesLinearFloor"
    )
    assert certificate.bare_af_envelope_implies_heat_time_spacing_floor_proved
    assert certificate.exponential_af_envelope_closes_every_fixed_positive_length


def test_physical_scaling_gate_remains_fail_closed() -> None:
    certificate = five_holonomy_spacing_budget()

    assert certificate.required_heat_time_over_spacing_floor
    assert not certificate.physical_bf4_af_envelope_instantiated
    assert not certificate.physical_heat_time_over_spacing_floor_proved
    assert not certificate.unconditional_arbitrary_trajectory_bound_possible
    assert certificate.first_open_obligation == (
        "instantiate-af-envelope-on-physical-bf4-trajectory"
    )
