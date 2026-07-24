"""Regression pins for the physical 4+2 wheel page carrier."""

from itertools import product

import pytest

from computations.dual_positivity_geometry_bridge import (
    Z4_PLANES,
    box_plaquettes,
    box_vertices,
    build_four_page_physical_slice,
    current_wheel_geometry_frontier,
    distinct_box_links,
    edges_of,
    incident_plaquette_ids,
)
from computations.exact_haar_network import invariant_multiplicity


def test_python_geometry_mirrors_production_box_counts() -> None:
    assert len(box_vertices(1)) == 1
    assert len(box_plaquettes(1)) == 6
    assert len(box_vertices(2)) == 16
    assert len(box_plaquettes(2)) == 96
    assert Z4_PLANES == ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
    assert len(distinct_box_links(2)) > 0


def test_first_interior_direction_zero_link_has_exact_six_page_ids() -> None:
    physical_slice = build_four_page_physical_slice()
    assert physical_slice.central_link == ((1, 1, 1, 1), 0)
    assert physical_slice.incident_face_ids == (66, 79, 86, 90, 91, 92)
    assert physical_slice.active_face_ids == (66, 79, 90, 91)
    assert physical_slice.vacuum_face_ids == (86, 92)
    assert physical_slice.active_local_positions == (0, 1, 3, 4)
    assert physical_slice.vacuum_local_positions == (2, 5)
    assert incident_plaquette_ids(2, physical_slice.central_link) == (
        66,
        79,
        86,
        90,
        91,
        92,
    )


def test_each_incident_face_really_contains_the_pinned_link() -> None:
    physical_slice = build_four_page_physical_slice()
    plaquettes = box_plaquettes(physical_slice.extent)
    assert all(
        physical_slice.central_link in edges_of(plaquettes[face_id])
        for face_id in physical_slice.incident_face_ids
    )
    assert physical_slice.is_physical_page_slice()


def test_two_vacuum_pages_reduce_six_valent_to_four_valent_invariant() -> None:
    physical_slice = build_four_page_physical_slice()
    for labels in product(range(4), repeat=4):
        active = (labels[0], labels[1], labels[2], labels[3])
        six = physical_slice.six_labels(active)
        assert six[2] == 0
        assert six[5] == 0
        assert invariant_multiplicity(six) == invariant_multiplicity(active)
    assert physical_slice.exhaustive_vacuum_reduction(3)


def test_geometry_frontier_stops_at_cyclic_rim_embedding() -> None:
    frontier = current_wheel_geometry_frontier()
    assert frontier.six_valent_link_pinned
    assert frontier.four_active_page_slice_pinned
    assert frontier.vacuum_reduction_verified
    assert not frontier.cyclic_rim_words_embedded
    assert not frontier.reflection_orientation_pinned
    assert frontier.first_open_field() == "cyclic_rim_words_embedded"
    assert not frontier.is_full_geometry_pinned()


def test_extent_one_has_no_canonical_interior_link() -> None:
    with pytest.raises(ValueError):
        build_four_page_physical_slice(1)
