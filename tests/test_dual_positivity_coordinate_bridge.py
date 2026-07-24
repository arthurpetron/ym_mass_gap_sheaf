"""Regression pins for the exact unit-rim physical coordinate bridge."""

from fractions import Fraction

import pytest

from computations.dual_positivity_coordinate_bridge import (
    PINNED_UNIT_RIM_MANIFEST_SHA256,
    build_unit_rim_coordinate_bridge,
    physical_schur_face_weight,
)
from computations.dual_positivity_manifest import manifest_sha256


def test_unit_rim_coordinate_bridge_closes_exact_coordinate_slice() -> None:
    bridge = build_unit_rim_coordinate_bridge(
        coupling=Fraction(1, 2),
        physical_cutoff=2,
        box_extent=1,
    )
    frontier = bridge.semantic_frontier()
    assert manifest_sha256(bridge.manifest) == PINNED_UNIT_RIM_MANIFEST_SHA256
    assert frontier.manifest_integrity
    assert frontier.coupling_coordinate_pinned
    assert frontier.boundary_channel_supported
    assert frontier.page_sum_cutoff_complete
    assert bridge.sector_activity() == bridge.compressed_activity()
    assert bridge.compressed_activity() == bridge.directly_contracted_activity()


def test_manifest_activity_has_the_pinned_exact_physical_value() -> None:
    bridge = build_unit_rim_coordinate_bridge(
        coupling=Fraction(1, 2),
        physical_cutoff=2,
        box_extent=1,
    )
    expected = (
        Fraction(1, 4)
        + Fraction(9, 2) * Fraction(1, 2) ** 16
        + Fraction(6) * Fraction(1, 2) ** 24
        + Fraction(21, 4) * Fraction(1, 2) ** 32
    )
    assert bridge.sector_activity() == expected


def test_each_sector_uses_dim_times_four_casimir_weight() -> None:
    bridge = build_unit_rim_coordinate_bridge(
        coupling=Fraction(2, 3),
        physical_cutoff=2,
        box_extent=3,
    )
    assert bridge.sector_coordinate_identity()
    assert physical_schur_face_weight(Fraction(2, 3), 0) == 1
    assert physical_schur_face_weight(Fraction(2, 3), 1) == 2 * Fraction(2, 3) ** 3
    assert physical_schur_face_weight(Fraction(2, 3), 2) == 3 * Fraction(2, 3) ** 8


def test_cutoff_one_supports_rim_but_not_complete_page_sum() -> None:
    bridge = build_unit_rim_coordinate_bridge(
        coupling=Fraction(1, 3),
        physical_cutoff=1,
        box_extent=1,
    )
    frontier = bridge.semantic_frontier()
    assert frontier.boundary_channel_supported
    assert not frontier.page_sum_cutoff_complete
    assert frontier.first_open_field() == "geometry_pinned"
    assert not frontier.is_cd2_closed()


def test_cutoff_zero_does_not_support_unit_rim() -> None:
    bridge = build_unit_rim_coordinate_bridge(
        coupling=Fraction(1),
        physical_cutoff=0,
        box_extent=1,
    )
    frontier = bridge.semantic_frontier()
    assert not frontier.boundary_channel_supported
    assert not frontier.page_sum_cutoff_complete
    assert not frontier.is_cd2_closed()


def test_partial_bridge_cannot_claim_cd2() -> None:
    bridge = build_unit_rim_coordinate_bridge(
        coupling=Fraction(1, 2),
        physical_cutoff=2,
        box_extent=1,
    )
    frontier = bridge.semantic_frontier()
    assert frontier.closed_fields() == (
        "manifest_integrity",
        "coupling_coordinate_pinned",
        "boundary_channel_supported",
        "page_sum_cutoff_complete",
    )
    assert frontier.first_open_field() == "geometry_pinned"
    assert not frontier.geometry_pinned
    assert not frontier.integrator_semantics_proved
    assert not frontier.complete_reflected_channels
    assert not frontier.physical_kernel_constructed
    assert not frontier.overlap_remainder_constructed
    assert not frontier.is_cd2_closed()


@pytest.mark.parametrize(
    ("coupling", "spin"),
    [
        (Fraction(-1), 0),
        (Fraction(1), -1),
    ],
)
def test_invalid_physical_schur_weight_inputs_are_rejected(
    coupling: Fraction, spin: int
) -> None:
    with pytest.raises(ValueError):
        physical_schur_face_weight(coupling, spin)
