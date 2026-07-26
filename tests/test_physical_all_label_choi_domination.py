"""Exact gates for direct all-label physical/corridor Choi domination."""

from fractions import Fraction

import pytest

from computations.physical_all_label_choi_domination import (
    dyadic_domination_collapse,
    least_relative_heat_majorant_cutoff,
    peter_weyl_source_target_carrier,
    physical_all_label_choi_domination,
    physical_choi_geometry_audit,
)


def test_physical_choi_geometry_is_the_exact_30_plus_21_plus_21_partition() -> None:
    geometry = physical_choi_geometry_audit()
    assert geometry.validates()
    assert geometry.full_face_count == 72
    assert geometry.selected_face_count == 30
    assert geometry.peeled_transverse_face_count == 21
    assert geometry.residual_face_count == 21
    assert geometry.selected_internal_link_count == 27
    assert geometry.protected_free_link_count == 18
    assert geometry.selected_boundaries_match_coarse_paths
    assert geometry.selected_only_semigroup_pushforward_exact


def test_source_target_carrier_has_shared_labels_and_complete_magnetics() -> None:
    carrier = peter_weyl_source_target_carrier(2)
    assert carrier.validates()
    assert carrier.one_slot_source_dimension == 6
    assert carrier.one_slot_target_dimension == 6
    assert carrier.one_slot_vectorized_coordinates == 14
    assert carrier.source_dimension == 6**9
    assert carrier.target_dimension == 6**9
    assert carrier.supported_choi_coordinate_count == 14**9
    assert carrier.same_label_on_source_and_target


def test_spacing_dependent_relative_cutoff_is_least_certified() -> None:
    expected = {
        Fraction(1, 2): 2,
        Fraction(3, 4): 3,
        Fraction(9, 10): 6,
        Fraction(99, 100): 23,
    }
    for coupling, cutoff in expected.items():
        point = least_relative_heat_majorant_cutoff(
            coupling,
            Fraction(1, 100),
        )
        assert point.validates()
        assert point.cutoff == cutoff
        assert point.relative_tail_bound <= Fraction(1, 100)


def test_direct_all_label_measure_order_lifts_to_full_choi_cp_order() -> None:
    certificate = physical_all_label_choi_domination(
        Fraction(1, 2),
        Fraction(1, 2),
    )
    assert certificate.validates()
    assert certificate.residual_density_lower_bound > 0
    assert certificate.cp_domination_coefficient == (
        certificate.physical_to_corridor_radon_nikodym_floor
    )
    assert (
        certificate.cp_domination_coefficient
        * certificate.physical_to_corridor_partition_ratio_upper_bound
        == certificate.physical_to_corridor_partition_ratio_lower_bound
    )
    assert certificate.physical_source_target_choi_defined
    assert certificate.direct_all_label_measure_regrouping_used
    assert not certificate.character_truncation_used_in_physical_operator
    assert certificate.normalized_measure_domination_proved
    assert certificate.full_trace_class_choi_cp_domination_proved
    assert certificate.every_finite_feature_compression_cp_dominated
    assert certificate.signed_recoupling_basis_independent


def test_cp_result_remains_fail_closed_at_physical_distance() -> None:
    certificate = physical_all_label_choi_domination(
        Fraction(3, 4),
        Fraction(1, 2),
    )
    assert certificate.cp_domination_coefficient > 0
    assert certificate.cp_domination_coefficient <= (
        certificate.coefficient_collapse_upper_bound
    )
    assert not (
        certificate.entrywise_all_label_recoupling_contraction_materialized
    )
    assert not certificate.consecutive_scale_channel_composition_proved
    assert certificate.cp_residual_mass_preserving_channel_proved
    assert certificate.abstract_same_carrier_convolution_composition_proved
    assert not certificate.physical_consecutive_slab_rg_identification_proved
    assert not certificate.spacing_uniform_cp_domination_proved
    assert not certificate.physical_coupling_spacing_condition_proved
    assert not certificate.jacobi_identity_formalized_in_repo


def test_dyadic_certificate_collapse_is_exact_and_strict() -> None:
    previous = Fraction(1)
    for level in range(1, 7):
        collapse = dyadic_domination_collapse(level)
        assert collapse.validates()
        assert collapse.cp_domination_coefficient > 0
        assert collapse.certified_upper_bound < previous
        assert not collapse.spacing_uniform_positive_floor_certified
        previous = collapse.certified_upper_bound


def test_invalid_source_target_and_schedule_inputs_fail_closed() -> None:
    with pytest.raises(ValueError):
        peter_weyl_source_target_carrier(-1)
    with pytest.raises(ValueError):
        least_relative_heat_majorant_cutoff(
            Fraction(1),
            Fraction(1, 100),
        )
    with pytest.raises(ValueError):
        least_relative_heat_majorant_cutoff(
            Fraction(1, 2),
            Fraction(1),
        )
    with pytest.raises(ValueError):
        dyadic_domination_collapse(0)
