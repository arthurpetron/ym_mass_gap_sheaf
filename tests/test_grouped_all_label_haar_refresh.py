"""Exact regression gates for the grouped all-label Haar refresh candidate."""

from fractions import Fraction

import pytest

from computations.grouped_all_label_haar_refresh import (
    ALL_LABEL_HAAR_FLOOR,
    BF32_COARSE_HOLONOMY_COUNT,
    GROUPED_HEAT_CAP,
    all_label_haar_floor_certificate,
    corrected_slab_corridor_geometry_audit,
    cumulative_heat_mode_witness,
    fixed_distance_corridor_certificate,
    grouped_heat_coordinate,
    grouped_physical_packet_frontier,
    heat_mode_multiplier,
    least_steps_below_cap,
    transverse_cutoff_one_fusion_audit,
    transverse_leaf_reduction_audit,
)


def test_exact_all_label_floor_at_grouped_half():
    certificate = all_label_haar_floor_certificate(Fraction(1, 2), 1)
    assert certificate.validates()
    assert certificate.grouped_coupling == GROUPED_HEAT_CAP
    assert certificate.first_excited_absolute_bound == Fraction(1, 2)
    assert certificate.remaining_absolute_tail_bound == Fraction(81, 2272)
    assert certificate.nonvacuum_absolute_bound == Fraction(1217, 2272)
    assert certificate.common_haar_floor == ALL_LABEL_HAAR_FLOOR
    assert certificate.packet_mass(BF32_COARSE_HOLONOMY_COUNT) == (
        Fraction(1055, 2272) ** 9
    )


def test_semigroup_coordinate_and_every_label_are_exact():
    coupling = Fraction(3, 4)
    steps = 3
    grouped = grouped_heat_coordinate(coupling, steps)
    assert grouped == Fraction(27, 64)
    for label in range(10):
        assert heat_mode_multiplier(coupling, steps, label) == (
            grouped ** (label * (label + 2))
        )
        assert heat_mode_multiplier(coupling, steps, label) > 0


def test_least_grouping_length_is_located_without_logs():
    samples = (
        (Fraction(1, 2), 1),
        (Fraction(3, 4), 3),
        (Fraction(9, 10), 7),
        (Fraction(99, 100), 69),
    )
    for coupling, expected_steps in samples:
        steps = least_steps_below_cap(coupling)
        assert steps == expected_steps
        assert coupling**steps <= GROUPED_HEAT_CAP
        if steps > 1:
            assert coupling ** (steps - 1) > GROUPED_HEAT_CAP


def test_fixed_distance_dyadic_model_has_one_uniform_packet():
    expected_packet = ALL_LABEL_HAAR_FLOOR**BF32_COARSE_HOLONOMY_COUNT
    for level in range(1, 9):
        denominator = 2**level
        spacing = Fraction(1, denominator)
        coupling = 1 - spacing
        certificate = fixed_distance_corridor_certificate(
            spacing,
            Fraction(1),
            coupling,
        )
        assert certificate.validates()
        assert certificate.grouped_steps == denominator
        assert certificate.grouped_coupling <= GROUPED_HEAT_CAP
        assert certificate.common_haar_floor == ALL_LABEL_HAAR_FLOOR
        assert certificate.nine_holonomy_packet_mass == expected_packet
        mode = cumulative_heat_mode_witness(certificate)
        assert mode.validates()
        assert mode.grouped_separator <= Fraction(1, 8)
        assert mode.lattice_margin >= Fraction(7, 8 * denominator)
        assert mode.rescaled_bare_margin >= Fraction(7, 8)
        assert mode.rescaled_bare_floor == Fraction(7, 16)
        assert not mode.physical_transfer_identification_proved


def test_fixed_distance_condition_fails_closed_when_heat_time_is_too_short():
    certificate = fixed_distance_corridor_certificate(
        Fraction(1, 10),
        Fraction(1),
        Fraction(99, 100),
    )
    assert certificate.validates()
    assert certificate.grouped_coupling == Fraction(99, 100) ** 10
    assert not certificate.cumulative_heat_condition
    assert certificate.common_haar_floor is None
    assert certificate.nine_holonomy_packet_mass is None
    with pytest.raises(ValueError):
        all_label_haar_floor_certificate(Fraction(99, 100), 10)


def test_nine_corrected_slab_corridors_and_transverse_obstruction():
    audit = corrected_slab_corridor_geometry_audit()
    assert audit.validates()
    assert audit.corridor_count == 9
    assert audit.corridor_face_count_census == ((2, 3), (4, 6))
    assert audit.selected_face_count == 30
    assert audit.selected_faces_pairwise_disjoint
    assert audit.internal_link_count == 27
    assert audit.internal_links_pairwise_disjoint
    assert audit.every_disk_boundary_matches_coarse_path
    assert audit.off_corridor_incidence_per_internal_link_census == ((2, 27),)
    assert audit.every_internal_link_transversely_coupled
    assert not audit.literal_semigroup_factorization_of_full_integrand


def test_transverse_factor_graph_reduces_to_exact_21_face_core():
    audit = transverse_leaf_reduction_audit()
    assert audit.validates()
    assert audit.initial_off_corridor_faces == 42
    assert audit.peeled_face_count == 21
    assert audit.residual_core_face_count == 21
    assert audit.residual_free_link_degree_census == ((1, 9), (2, 9), (3, 5))
    assert audit.residual_component_face_count_census == ((1, 6), (15, 1))
    assert audit.protected_links_in_residual_core == 18
    assert audit.every_residual_leaf_is_corridor_protected
    assert audit.heat_normalization_makes_each_peel_exact
    assert audit.maximal_for_unprotected_leaf_rule


def test_transverse_core_complete_cutoff_one_fusion_ledger():
    audit = transverse_cutoff_one_fusion_audit()
    assert audit.validates()
    assert len(audit.connected_core_faces) == 15
    assert len(audit.decoration_faces) == 6
    assert audit.internal_trivalent_link_count == 5
    assert audit.core_protected_link_count == 9
    assert audit.binary_internal_admissible_assignments == 1024
    assert audit.binary_boundary_parity_profiles == 128
    assert audit.binary_fillings_per_parity_profile == 8
    assert audit.complete_core_boundary_label_profiles == 4761
    assert audit.complete_core_fusion_paths == 10673
    assert audit.complete_residual_boundary_label_profiles == 304704
    assert audit.complete_residual_fusion_paths == 683072
    assert audit.internal_intertwiner_multiplicity_one
    assert audit.singlet_triplet_boundary_channels_retained
    assert audit.parity_only_boundary_carrier_refuted
    assert audit.coherent_partial_haar_tensors_evaluated
    assert not audit.cp_order_domination_proved
    assert not audit.all_label_completion_proved


def test_physical_promotion_frontier_remains_fail_closed():
    frontier = grouped_physical_packet_frontier()
    assert frontier.validates()
    assert frontier.common_haar_packet_constructed
    assert frontier.common_packet_faithful_on_all_peter_weyl_labels
    assert frontier.nine_geometric_corridors_pinned
    assert frontier.transverse_interaction_obstruction_pinned
    assert frontier.transverse_leaf_reduction_pinned
    assert frontier.transverse_cutoff_one_fusion_ledger_pinned
    assert frontier.transverse_cutoff_one_coherent_loop_tensors_pinned
    assert frontier.transverse_cutoff_one_complete_residual_tensors_pinned
    assert frontier.transverse_arbitrary_cutoff_recoupling_carrier_pinned
    assert frontier.transverse_arbitrary_cutoff_open_magnetic_tensors_pinned
    assert frontier.transverse_cutoff_one_open_index_network_pinned
    assert frontier.transverse_fixed_coupling_all_label_cauchy_modulus_pinned
    assert frontier.transverse_fixed_coupling_operator_trace_tail_pinned
    assert frontier.transverse_cutoff_one_weak_coupling_cp_obstruction_pinned
    assert (
        frontier.transverse_fixed_cutoff_weak_coupling_tail_obstruction_pinned
    )
    assert not frontier.transverse_open_index_all_label_choi_reconstructed
    assert frontier.basis_free_physical_all_label_source_target_choi_defined
    assert frontier.direct_all_label_measure_regrouping_used
    assert frontier.spacing_dependent_cutoff_schedule_pinned
    assert frontier.fixed_coupling_physical_corridor_cp_domination_proved
    assert not (
        frontier.spacing_uniform_physical_corridor_cp_domination_proved
    )
    assert not frontier.consecutive_scale_channel_composition_proved
    assert frontier.cumulative_heat_condition_contains_rescaled_bare_mode_floor
    assert not frontier.interacting_map_cp_dominates_corridor
    assert not frontier.physical_coupling_spacing_condition_proved
    assert not frontier.actual_grouped_all_label_packet_proved
    assert not frontier.spacing_uniform_refresh_mass_proved
