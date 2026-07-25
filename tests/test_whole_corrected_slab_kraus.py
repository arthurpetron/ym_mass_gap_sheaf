"""Exact regression gates for the complete BF3.1 cutoff-one milestone."""

from collections import Counter
from fractions import Fraction

from computations.whole_corrected_slab_kraus import (
    BF31_LEAN_THEOREMS,
    EXPECTED_BINARY_MASS,
    EXPECTED_FIRST_COARSE_MODE,
    EXPECTED_FIRST_COARSE_REMAINDER,
    EXPECTED_FIRST_NORMALIZED_REMAINDER_NUMERATOR,
    bf31_certificate,
    binary_whole_slab_kraus_kernel,
    coarse_face_paths,
    coarse_projection_fibre,
    coarse_projection_fibre_census,
    coarse_target_mode,
    exact_coarse_face_mode,
    first_coarse_mode_audit,
    fundamental_adjacent_swap_matrices,
    joint_intertwiner_transport_audit,
    normalized_remainder_numerator,
    projection_block_witness,
    whole_slab_geometry,
)


def test_smallest_whole_corrected_slab_geometry_is_complete() -> None:
    geometry = whole_slab_geometry()

    assert geometry.validates()
    assert (geometry.face_count, geometry.edge_count, geometry.free_link_count) == (
        72,
        116,
        65,
    )
    assert (
        geometry.lower_spatial_faces,
        geometry.temporal_faces,
        geometry.upper_spatial_faces,
    ) == (24, 24, 24)
    assert len(coarse_face_paths()) == 9
    assert geometry.binary_cycle_rank == 7
    assert geometry.binary_assignment_count == 128


def test_cutoff_one_whole_slab_kernel_has_32_exact_kraus_blocks() -> None:
    kernel = binary_whole_slab_kraus_kernel()

    assert kernel.validates()
    assert kernel.boundary_dimension == 64
    assert kernel.kraus_rank == 32
    assert kernel.physical_assignment_count == 128
    assert kernel.unnormalized_mass == EXPECTED_BINARY_MASS
    assert kernel.independent_direct_mass == kernel.unnormalized_mass
    vectors = Counter(
        tuple(tuple(component.items()) for component in block.kraus_vector)
        for block in kernel.blocks
    )
    assert vectors == {
        (((0, Fraction(1)),), ((18, Fraction(4)),)): 1,
        (((9, Fraction(2)),), ((21, Fraction(2)),)): 5,
        (((15, Fraction(2)),), ((21, Fraction(2)),)): 8,
        (((18, Fraction(2)),), ((18, Fraction(2)),)): 4,
        (((18, Fraction(4)),), ((24, Fraction(1)),)): 2,
        (((21, Fraction(2)),), ((9, Fraction(2)),)): 1,
        (((21, Fraction(2)),), ((15, Fraction(2)),)): 4,
        (((21, Fraction(2)),), ((21, Fraction(2)),)): 6,
        (((24, Fraction(1)),), ((18, Fraction(4)),)): 1,
    }


def test_every_binary_coarse_word_has_a_complete_coherent_fibre() -> None:
    census = coarse_projection_fibre_census()

    assert census.validates()
    assert census.coarse_mode_count == 512
    assert census.fibre_size_census == ((128, 512),)
    assert census.coherent_channel_count == 65536
    assert census.maximum_valence_census == (
        (0, 1),
        (2, 1420),
        (4, 31731),
        (6, 32384),
    )
    assert census.maximum_invariant_dimension_census == (
        (1, 1421),
        (2, 31731),
        (5, 32384),
    )
    assert all(len(coarse_projection_fibre(mask)) == 128 for mask in range(512))


def test_joint_four_and_six_valent_transport_is_signed_and_coherent() -> None:
    audit = joint_intertwiner_transport_audit()
    four = fundamental_adjacent_swap_matrices(4)
    six = fundamental_adjacent_swap_matrices(6)

    assert audit.validates()
    assert audit.invariant_dimensions == ((2, 1), (4, 2), (6, 5))
    assert len(four) == 3
    assert len(six) == 5
    assert four[0][0][0].coeff == -1
    assert four[1][0][1].square == Fraction(3, 4)
    assert six[2][3][4].square == Fraction(8, 9)
    assert audit.all_involutive
    assert audit.all_braid_relations
    assert audit.all_distant_swaps_commute
    assert audit.coherent_channel_count == 65536


def test_first_whole_slab_coarse_mode_has_a_literal_nonzero_remainder() -> None:
    audit = first_coarse_mode_audit()

    assert audit.validates()
    assert exact_coarse_face_mode(0) == EXPECTED_BINARY_MASS
    assert normalized_remainder_numerator(0) == {}
    assert coarse_target_mode(1) == {12: Fraction(2)}
    assert audit.whole_slab_mode == EXPECTED_FIRST_COARSE_MODE
    assert audit.isolated_disk_mode == {12: Fraction(2)}
    assert audit.raw_whole_slab_correction == EXPECTED_FIRST_COARSE_REMAINDER
    assert (
        audit.normalized_remainder_numerator
        == EXPECTED_FIRST_NORMALIZED_REMAINDER_NUMERATOR
    )
    assert audit.reflected_mode_equal


def test_all_four_projection_blocks_are_retained_and_finite_closure_fails() -> None:
    cutoff_one = projection_block_witness(1)
    cutoff_four = projection_block_witness(4)

    assert cutoff_one.validates()
    assert cutoff_one.outside_label == 2
    assert cutoff_one.pq_leading == cutoff_one.qp_leading == {8: Fraction(3)}
    assert cutoff_one.qq_leading == {16: Fraction(9)}
    assert not cutoff_one.finite_carrier_closed

    assert cutoff_four.validates()
    assert cutoff_four.outside_label == 5
    assert cutoff_four.outside_heat_exponent == 35
    assert cutoff_four.pq_leading == {35: Fraction(6)}


def test_bf31_closes_the_complete_cutoff_one_milestone() -> None:
    certificate = bf31_certificate()

    assert certificate.validates()
    assert certificate.exit_kind == "cutoff-one-whole-slab-with-coherent-remainder"
    assert certificate.surrogate_scaffold_theorems == BF31_LEAN_THEOREMS
    assert not certificate.surrogate_is_physical_identification
    assert certificate.intertwiner_transport.validates()
    assert certificate.normalized_vacuum_remainder == {}
    assert certificate.remainder_norm_status == "open-BF3.2"
    assert certificate.all_label_status == "open-nonzero-PQ-tail"
    assert certificate.next_gate == "BF3.2-all-label-kernel-and-vanishing-remainder"
