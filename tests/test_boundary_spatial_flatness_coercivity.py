"""Exact topology and linearized coercivity of the spatial boundary."""

from fractions import Fraction

from computations.boundary_spatial_flatness_coercivity import (
    boundary_spatial_flatness_coercivity,
)


def test_spatial_boundary_is_one_flat_spherical_gauge_well() -> None:
    certificate = boundary_spatial_flatness_coercivity()

    assert certificate.validates()
    assert certificate.spatial_face_count == 24
    assert certificate.spatial_link_count == 48
    assert certificate.spatial_vertex_count == 26
    assert certificate.euler_characteristic == 2
    assert certificate.initial_edge_face_degree_census == (
        (1, 24),
        (2, 6),
        (3, 12),
        (4, 6),
    )
    assert certificate.vertex_edge_boundary_rank_gf2 == 25
    assert certificate.edge_face_boundary_rank_gf2 == 23
    assert certificate.betti_numbers_gf2 == (1, 0, 1)
    assert certificate.face_edge_collapse_count == 18
    assert certificate.residual_core_face_count == 6
    assert certificate.residual_core_link_count == 12
    assert certificate.residual_core_vertex_count == 8
    assert certificate.residual_core_every_edge_degree_two
    assert certificate.residual_core_every_vertex_link_one_cycle
    assert certificate.graph_leaf_collapse_count == 18
    assert certificate.deformation_retracts_to_cube_boundary
    assert certificate.two_sphere_homotopy_type_certified
    assert certificate.unique_flat_su2_gauge_orbit
    assert certificate.multiple_topological_flat_wells_refuted


def test_tree_gauge_curvature_map_has_an_exact_positive_floor() -> None:
    certificate = boundary_spatial_flatness_coercivity()

    assert certificate.spanning_tree_link_count == 25
    assert certificate.gauge_fixed_cycle_count == 23
    assert certificate.linearized_curvature_matrix_shape == (24, 23)
    assert certificate.linearized_curvature_rank_gf2 == 23
    assert certificate.curvature_gram_trace == 47
    assert certificate.curvature_gram_determinant == 6
    assert certificate.shifted_gram_scale == 11
    assert certificate.shifted_gram_leading_principal_minor_count == 23
    assert certificate.shifted_gram_minimum_leading_principal_minor == 32
    assert certificate.conservative_linearized_coercivity_floor == Fraction(1, 11)
    assert certificate.omitted_redundant_face_id == 0
    assert certificate.punctured_face_count == 23
    assert certificate.punctured_face_edge_collapse_count == 23
    assert certificate.punctured_residual_spanning_tree_link_count == 25
    assert certificate.triangular_nonabelian_reconstruction_proved
    assert certificate.maximum_reconstruction_face_l1_weight == 9
    assert certificate.maximum_reconstruction_face_coefficient == 2
    assert certificate.reconstruction_coefficient_square_sum == 81
    assert certificate.global_nonlinear_curvature_coercivity_constant == Fraction(1, 81)
    assert certificate.nonlinear_global_curvature_coercivity_proved
    assert not certificate.spacing_uniform_intrinsic_perron_budget_proved
