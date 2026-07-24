"""Regression gates for the first six-valent interior-link probe."""

from fractions import Fraction

from computations.interior_link4d_probe import (
    central_link_stabilizer_maps,
    composite_pair_orbits,
    composite_pair_probe_survey,
    duplicate_pair_channel_sum,
    elementary_surfaces,
    evaluate_duplicate_pair,
    incident_faces,
    is_closed_binary_surface,
    minimal_interior_link_brick,
    pair_probe_survey,
    sign_counts,
    two_cube_composite_surfaces,
    unordered_pair_orbits,
)


def test_minimal_brick_has_a_six_valent_interior_link() -> None:
    complex_, faces, meta, central_edge = minimal_interior_link_brick()
    assert len(complex_.edges) == 135
    assert len(faces) == len(meta) == 126
    assert len(complex_.free) == 82
    assert len(incident_faces(faces, central_edge)) == 6


def test_twelve_elementary_surfaces_are_closed_and_cross_central_link_twice() -> None:
    _complex, faces, meta, central_edge = minimal_interior_link_brick()
    central_faces = set(incident_faces(faces, central_edge))
    surfaces = elementary_surfaces(meta)
    assert len(surfaces) == 12
    assert len({surface.mask for surface in surfaces}) == 12
    assert all(surface.mask.bit_count() == 6 for surface in surfaces)
    assert all(is_closed_binary_surface(faces, surface.mask) for surface in surfaces)
    assert {sum((surface.mask >> face) & 1 for face in central_faces) for surface in surfaces} == {
        2
    }


def test_stabilizer_classifies_all_66_unordered_pairs() -> None:
    _complex, _faces, meta, _central_edge = minimal_interior_link_brick()
    maps = central_link_stabilizer_maps(meta)
    masks = tuple(surface.mask for surface in elementary_surfaces(meta))
    orbits = unordered_pair_orbits(masks, maps)
    assert len(maps) == 96
    assert sum(map(len, orbits)) == 66


def test_duplicate_surface_pair_orbits_are_exactly_nonnegative() -> None:
    probes = pair_probe_survey()
    assert probes
    assert sign_counts(probes) == (66, 0, 0)
    assert all(probe.value > 0 for probe in probes)
    # The family genuinely retains two fundamental strands on shared faces.
    assert any(probe.overlap > 0 for probe in probes)
    assert any(2 in probe.central_strand_counts for probe in probes)
    complex_, faces, _meta, _edge = minimal_interior_link_brick()
    assert all(
        evaluate_duplicate_pair(complex_, faces, probe.left, probe.right)
        == duplicate_pair_channel_sum(
            complex_,
            faces,
            probe.left,
            probe.right,
        )
        for probe in probes
    )
    # Pin the exact value set, not just its sign.
    assert {probe.value for probe in probes} == {
        Fraction(1, 256),
        Fraction(1, 128),
    }


def test_two_cube_composite_family_has_65_pair_orbits() -> None:
    _complex, _faces, meta, _edge = minimal_interior_link_brick()
    composites = two_cube_composite_surfaces(meta)
    orbits = composite_pair_orbits(meta)
    assert len(composites) == 66
    assert len(orbits) == 65
    assert sum(map(len, orbits)) == 2145


def test_composite_duplicate_strand_headline_values_are_positive() -> None:
    probes = composite_pair_probe_survey((0, 2, 6))
    assert [probe.value for probe in probes] == [
        Fraction(41, 10368),
        Fraction(31, 3888),
        Fraction(41, 5184),
    ]
    assert sign_counts(probes) == (
        sum(probe.orbit_size for probe in probes),
        0,
        0,
    )


def test_every_orbit_activating_all_six_central_plaquettes_is_positive() -> None:
    _complex, faces, meta, central_edge = minimal_interior_link_brick()
    central_faces = incident_faces(faces, central_edge)
    orbits = composite_pair_orbits(meta)
    indices = tuple(
        index
        for index, orbit in enumerate(orbits)
        if sum(
            (((orbit[0][0] >> face) & 1) + ((orbit[0][1] >> face) & 1)) > 0
            for face in central_faces
        )
        == 6
    )
    assert indices == (20, 56, 57, 58, 59, 60, 61, 62, 63, 64)

    probes = composite_pair_probe_survey(indices)
    assert sum(probe.orbit_size for probe in probes) == 252
    assert sign_counts(probes) == (252, 0, 0)
    assert [probe.value for probe in probes] == [
        Fraction(41, 10368),
        Fraction(1, 32768),
        Fraction(1, 32768),
        Fraction(1, 16384),
        Fraction(1, 16384),
        Fraction(1, 16384),
        Fraction(1, 16384),
        Fraction(1, 16384),
        Fraction(1, 16384),
        Fraction(1, 16384),
    ]
    assert all(all(strands > 0 for strands in probe.central_strand_counts) for probe in probes)
