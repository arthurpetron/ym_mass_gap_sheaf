"""Regression gates for the complete first-branching interface census."""

from collections import Counter
from fractions import Fraction

from computations.dual_spin_gluing import (
    BRANCHED_INTERFACE_EDGE,
    build_two_cell_spin_gluing,
    channel_edge_invariant_multiplicities,
    permute_face_mask,
    relative_boundary_defect,
)
from computations.dual_spin_interface_census import (
    FIRST_BRANCHING_OVERLAP,
    bounded_overlap_pair_orbit_representatives,
    bounded_overlap_resolved_channel_quotient,
    brick_symmetry_face_maps,
    cell_local_channel_value,
    channel_interface_carrier,
    coordinate_torus_homology_class,
    exact_interface_channel_value,
    first_branching_census,
    interface_genus_one_surface_masks,
    minimal_interface_torus_channel_value,
    minimal_interface_torus_channels,
    nonzero_defect_channel_representatives,
    pairing_interface_channel_value,
    resolved_channel_is_admissible,
)

EXPECTED_OVERLAP_CENSUS = (
    (0, 234),
    (1, 288),
    (2, 2940),
    (3, 5232),
    (4, 15192),
    (5, 34992),
    (6, 60546),
    (7, 97824),
    (8, 145746),
    (9, 161424),
    (10, 157434),
    (11, 125088),
    (12, 75870),
    (13, 43344),
    (14, 17526),
    (15, 9888),
    (16, 3324),
    (17, 1104),
    (18, 402),
    (19, 48),
    (20, 18),
)

EXPECTED_NONZERO_DEFECT_CHANNELS = (
    (0x31AD1B6D9E, 0x240001),
    (0x31AD1B6D9E, 0x240041),
    (0x31AD1B6D9E, 0x240201),
    (0x31AD1B6D9E, 0x241001),
    (0x31AD1B6D9E, 0x600001),
    (0x31AD1B6D9E, 0x600041),
    (0x31AD1B6D9E, 0x601001),
    (0x31AD1B6D9E, 0x640000),
    (0x31AD1B6D9E, 0x640040),
    (0x31AD1B6D9E, 0x641000),
    (0xB5EA1B6D9E, 0x240001),
    (0xB5EA1B6D9E, 0x440041),
    (0xB5EA1B6D9E, 0x600041),
    (0xB5EA1B6D9E, 0x640040),
)


def test_full_brick_symmetry_preserves_interface_tori() -> None:
    maps = brick_symmetry_face_maps()
    surfaces = set(interface_genus_one_surface_masks())
    assert len(maps) == 96
    assert len(set(maps)) == 96
    assert all(len(permutation) == 42 for permutation in maps)
    assert all(
        {permute_face_mask(surface, permutation) for surface in surfaces} == surfaces
        for permutation in maps
    )


def test_first_branching_pair_and_channel_cardinalities() -> None:
    census = first_branching_census()
    assert FIRST_BRANCHING_OVERLAP == 5
    assert census.closed_surfaces == 8192
    assert census.genus_one_surfaces == 237
    assert census.interface_genus_one_surfaces == 234
    assert census.physical_pairs == 958464
    assert census.overlap_census == EXPECTED_OVERLAP_CENSUS
    assert census.filtered_pairs == 58878
    assert census.filtered_pair_orbits == 1219
    assert census.raw_orbit_representative_channels == 27122
    assert census.admissible_orbit_representative_channels == 15744
    assert census.resolved_channel_orbits == 2166
    assert census.nonzero_defect_channel_orbits == 14
    assert len(bounded_overlap_pair_orbit_representatives()) == 1219
    assert len(bounded_overlap_resolved_channel_quotient().representatives) == 2166


def test_fast_admissibility_matches_literal_edge_multiplicities() -> None:
    representatives = bounded_overlap_resolved_channel_quotient().representatives
    for surface, selected in representatives[::37]:
        literal = channel_edge_invariant_multiplicities(surface, selected)
        assert resolved_channel_is_admissible(surface, selected) == all(literal)


def test_nonzero_defect_orbits_are_exactly_the_pinned_branch_family() -> None:
    channels = nonzero_defect_channel_representatives()
    assert channels == EXPECTED_NONZERO_DEFECT_CHANNELS
    for channel in channels:
        assert relative_boundary_defect(*channel) == 1 << BRANCHED_INTERFACE_EDGE
        carrier = channel_interface_carrier(channel)
        defect_packets = [packet for packet in carrier if packet.relative_defect]
        assert len(defect_packets) == 1
        assert tuple(strand.label for strand in defect_packets[0].strands) == (2, 2, 2)
        assert defect_packets[0].invariant_dimension == 1


def test_complete_first_branching_defect_sector_is_strictly_positive() -> None:
    values = [
        exact_interface_channel_value(channel)
        for channel in nonzero_defect_channel_representatives()
    ]
    assert all(value > 0 for value in values)
    assert Counter(values) == Counter(
        {
            Fraction(1, 18874368): 10,
            Fraction(1, 75497472): 1,
            Fraction(1, 226492416): 3,
        }
    )
    assert sum(values, start=Fraction(0)) == Fraction(7, 12582912)


def test_pairing_expansion_matches_both_signs_of_generic_integrator() -> None:
    for channel in (
        (0x31AD1B6D9E, 0x240001),
        (0x24636D9E, 0x21),
    ):
        assert pairing_interface_channel_value(channel) == exact_interface_channel_value(
            channel
        )


def test_complete_minimal_interface_torus_stratum_obeys_quadratic_sign() -> None:
    channels = minimal_interface_torus_channels()
    assert len(channels) == 34
    assert sum(cell_local_channel_value(channel) is not None for channel in channels) == 33

    values = [
        minimal_interface_torus_channel_value(channel)
        for channel in channels
    ]
    classes = [coordinate_torus_homology_class(channel) for channel in channels]
    assert all(homology_class is not None for homology_class in classes)
    assert all(
        (value < 0) == (homology_class == (1, 1))
        for value, homology_class in zip(values, classes, strict=True)
    )
    assert Counter(values) == Counter(
        {
            Fraction(1, 65536): 15,
            Fraction(1, 589824): 8,
            Fraction(1, 5308416): 9,
            Fraction(-1, 196608): 2,
        }
    )
    assert sum(values, start=Fraction(0)) == Fraction(23, 98304)


def test_empty_overlap_family_has_no_hidden_branch() -> None:
    certificate = build_two_cell_spin_gluing()
    empty_overlap_channels = [
        channel
        for channel in bounded_overlap_resolved_channel_quotient(0).representatives
        if channel[1] == 0
    ]
    assert len(empty_overlap_channels) == 12
    assert all(
        not relative_boundary_defect(surface, selected)
        and surface & certificate.interface_face_mask
        for surface, selected in empty_overlap_channels
    )
