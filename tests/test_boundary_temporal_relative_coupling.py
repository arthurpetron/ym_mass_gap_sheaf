"""Exact relative-rank audit for the temporal plaquette sector."""

from computations.boundary_temporal_relative_coupling import (
    TRANSMITTED_CYCLE_INDICES,
    boundary_temporal_relative_coupling,
    finite_fiber_feynman_kac_identity,
)


def test_temporal_sector_transmits_exactly_five_relative_cycles() -> None:
    certificate = boundary_temporal_relative_coupling()

    assert certificate.validates()
    assert certificate.temporal_face_count == 24
    assert certificate.internal_temporal_link_count == 20
    assert certificate.temporal_base_graph_vertex_count == 20
    assert certificate.temporal_base_graph_edge_count == 24
    assert certificate.temporal_base_graph_connected
    assert certificate.temporal_base_graph_cycle_rank == 5
    assert certificate.every_temporal_face_is_base_edge_cylinder
    assert certificate.temporal_links_biject_base_graph_vertices
    assert certificate.base_graph_tree_extends_to_full_boundary_tree
    assert certificate.base_graph_chord_edges_match_transmitted_full_cycle_edges
    assert certificate.source_boundary_cycle_count == 23
    assert certificate.target_boundary_cycle_count == 23
    assert certificate.full_linearized_matrix_shape == (24, 66)
    assert certificate.full_linearized_rank == 24
    assert certificate.temporal_link_submatrix_rank == 19
    assert certificate.relative_boundary_coupling_rank == 5


def test_effective_temporal_rows_are_five_source_target_differences() -> None:
    certificate = boundary_temporal_relative_coupling()

    assert certificate.left_annihilator_shape == (5, 24)
    assert certificate.left_annihilator_rank == 5
    assert certificate.left_annihilator_kills_temporal_links
    assert certificate.effective_boundary_matrix_shape == (5, 46)
    assert certificate.effective_boundary_matrix_rank == 5
    assert (
        certificate.transmitted_source_cycle_indices
        == TRANSMITTED_CYCLE_INDICES
        == (0, 4, 5, 6, 10)
    )
    assert certificate.transmitted_target_cycle_indices == TRANSMITTED_CYCLE_INDICES
    assert certificate.effective_rows_are_source_minus_target_coordinates
    assert not certificate.microscopic_temporal_ellipticity_on_all_23_cycles
    assert certificate.exact_nonlinear_five_holonomy_factorization_proved
    assert certificate.eighteen_dimensional_fibers_conditionally_integrated
    assert certificate.five_holonomy_feynman_kac_operator_identity_proved
    assert not certificate.spatial_temporal_hypocoercive_perron_bound_proved


def test_fiber_feynman_kac_reduction_is_an_exact_operator_identity() -> None:
    certificate = finite_fiber_feynman_kac_identity()

    assert certificate.validates()
    assert certificate.slab_count == 3
    assert certificate.full_grouped_transfer == certificate.fiber_reduced_grouped_transfer
