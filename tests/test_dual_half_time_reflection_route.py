"""Regression pins for the corrected CD-2 reflection geometry."""

from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
    build_corrected_page_reflection_pair,
    corrected_slab_reflection_is_involutive,
    current_cd2_reflection_route_frontier,
    legacy_bottom_spatial_reflection_witness,
    legacy_box_reflection_is_closed,
    slab_face_reflection_permutation,
    time_reflect_plaquette,
)


def test_legacy_physical_box_has_exact_reflection_obstruction() -> None:
    for extent in (1, 2, 3):
        source, reflected = legacy_bottom_spatial_reflection_witness(extent)
        assert source == ((0, 0, 0, 0), (0, 1))
        assert reflected == ((0, 0, 0, extent), (0, 1))
        assert time_reflect_plaquette(extent, source) == reflected
        assert not legacy_box_reflection_is_closed(extent)


def test_corrected_slab_face_map_is_an_exact_involution() -> None:
    for extent in (1, 3):
        plaquettes = boundary_complete_slab_plaquettes(extent)
        permutation = slab_face_reflection_permutation(extent)
        assert len(permutation) == len(plaquettes)
        assert sorted(permutation) == list(range(len(plaquettes)))
        assert all(
            permutation[permutation[face_id]] == face_id
            for face_id in range(len(permutation))
        )
        assert corrected_slab_reflection_is_involutive(extent)


def test_central_four_plus_two_page_carrier_has_reflected_partner() -> None:
    pair = build_corrected_page_reflection_pair()
    assert pair.half == 1
    assert pair.extent == 3
    assert pair.lower_link == ((1, 1, 1, 1), 0)
    assert pair.upper_link == ((1, 1, 1, 2), 0)
    assert len(pair.lower_active_face_ids) == 4
    assert len(pair.upper_active_face_ids) == 4
    assert len(pair.lower_temporal_face_ids) == 2
    assert len(pair.upper_temporal_face_ids) == 2
    assert set(pair.reflected_lower_face_ids) == set(pair.upper_incident_face_ids)
    assert pair.is_closed()


def test_route_requires_corrected_slab_physical_term() -> None:
    frontier = current_cd2_reflection_route_frontier()
    assert not frontier.legacy_physical_term_reflection_closed
    assert frontier.corrected_slab_face_permutation_pinned
    assert frontier.corrected_page_pair_pinned
    assert not frontier.corrected_slab_spin_foam_term_pinned
    assert not frontier.legacy_to_corrected_term_bridge_pinned
    assert not frontier.viable_physical_term_route_selected()
    assert frontier.first_open_field() == "corrected_slab_term_or_legacy_bridge"
    assert not frontier.is_reflection_route_closed()
