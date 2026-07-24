"""Exact regression pins for the BF1.6 reflection-cut carrier."""

from fractions import Fraction

from computations.reflection_cut_half_surface import (
    REFLECTED_STRAND_TWO,
    STRAND_ONE,
    STRAND_THREE,
    STRAND_TWO,
    cut_reflection_transport_audit,
    fundamental_cut_kernel_identity,
    half_carrier_gram_audit,
    half_surface_reconstruction_audit,
    reflect_hypercube_mask,
    reflection_cut_carrier,
    reflection_cut_census,
)


def test_three_strands_split_into_canonical_cut_loops() -> None:
    carrier = reflection_cut_carrier()
    census = reflection_cut_census()

    assert census.validates()
    assert census.packet_face_splits == ((1, 4, 1), (6, 0, 0), (2, 6, 2))
    assert census.cut_loop_lengths == (4, 6)
    assert census.cut_segment_count == 10
    assert census.cut_vertex_leg_counts == ((2, 2), (4, 4))
    assert census.boundary_invariant_dimension == 16

    assert len(carrier.packets[0].cut_loops) == 1
    assert carrier.packets[1].cut_loops == ()
    assert len(carrier.packets[2].cut_loops) == 1


def test_reflection_fixes_cut_graph_and_exchanges_half_packets() -> None:
    assert reflect_hypercube_mask(STRAND_ONE) == STRAND_ONE
    assert reflect_hypercube_mask(STRAND_THREE) == STRAND_THREE
    assert reflect_hypercube_mask(STRAND_TWO) == REFLECTED_STRAND_TWO
    assert REFLECTED_STRAND_TWO == 0x2111C0
    assert reflect_hypercube_mask(REFLECTED_STRAND_TWO) == STRAND_TWO

    transport = cut_reflection_transport_audit()
    assert transport.validates()
    assert transport.segment_permutation == tuple(range(10))
    assert transport.vertex_permutation == tuple(range(6))


def test_temporal_gauge_half_tensor_reconstructs_bf15_exactly() -> None:
    assert fundamental_cut_kernel_identity()
    audit = half_surface_reconstruction_audit()

    assert audit.validates()
    assert audit.generator_amplitudes == (
        Fraction(1, 16),
        Fraction(1, 16),
        Fraction(1, 256),
    )
    assert audit.pair_amplitude == Fraction(41, 648)
    assert audit.family_feature_pairing.boundary_leg_count == 10
    assert audit.family_feature_pairing.lower_nonzero_components == 10
    assert audit.family_feature_pairing.upper_nonzero_components == 194560
    assert audit.family_feature_pairing.common_nonzero_components == 10
    assert audit.family_feature_pairing.amplitude == Fraction(83, 5184)


def test_positive_half_packet_has_exact_sos_gram() -> None:
    audit = half_carrier_gram_audit()
    assert audit.validates()
    assert audit.matrix == (
        (Fraction(41, 648), Fraction(83, 5184)),
        (Fraction(83, 5184), Fraction(85, 20736)),
    )
    assert audit.determinant == Fraction(1, 331776)
    assert audit.ldlt_lower_entry == Fraction(83, 328)
    assert audit.ldlt_diagonal == (
        Fraction(41, 648),
        Fraction(1, 20992),
    )
