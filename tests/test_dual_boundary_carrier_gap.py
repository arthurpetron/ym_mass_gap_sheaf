"""Regression tests for the four-rim versus one-interface carrier gap."""

import pytest

from computations.dual_boundary_carrier_gap import (
    MultiLinkBoundaryChannel,
    build_abstract_unit_rim_embedding,
    current_boundary_carrier_frontier,
)


def test_unit_rim_keeps_four_ordered_slots_despite_equal_labels() -> None:
    embedding = build_abstract_unit_rim_embedding(cutoff=2)
    assert embedding.channel.modes == (1, 1, 1, 1)
    assert embedding.channel.arity == 4
    assert len(set(embedding.channel.slot_ids)) == 4
    assert embedding.slot_provenance_is_preserved()
    assert embedding.channel.supported()


def test_manifest_rim_words_have_exact_cyclic_orientation() -> None:
    embedding = build_abstract_unit_rim_embedding(cutoff=2)
    assert embedding.integrated_link_ids == (0, 1, 2, 3)
    assert embedding.rim_words == (
        ((0, 1), (1, -1)),
        ((1, 1), (2, -1)),
        ((2, 1), (3, -1)),
        ((3, 1), (0, -1)),
    )
    assert embedding.is_cyclic()
    assert embedding.is_abstractly_closed()


def test_single_interface_cd1_carrier_cannot_encode_four_rim_slots() -> None:
    frontier = current_boundary_carrier_frontier()
    assert frontier.existing_single_interface_arity == 1
    assert frontier.required_wheel_arity == 4
    assert not frontier.single_interface_carrier_is_sufficient()
    assert frontier.abstract_cyclic_embedding_pinned


def test_physical_boundary_carrier_stops_at_half_time_slot_map() -> None:
    frontier = current_boundary_carrier_frontier()
    assert not frontier.physical_half_time_slot_ids_pinned
    assert not frontier.reflection_slot_permutation_pinned
    assert not frontier.intertwiner_basis_pinned
    assert frontier.first_open_field() == "physical_half_time_slot_ids_pinned"
    assert not frontier.is_cd2_boundary_carrier_closed()


def test_cutoff_zero_rejects_the_unit_rim_support() -> None:
    embedding = build_abstract_unit_rim_embedding(cutoff=0)
    assert not embedding.channel.supported()
    assert not embedding.is_abstractly_closed()


@pytest.mark.parametrize(
    ("slots", "modes"),
    [
        (("a",), ()),
        (("a", "a"), (0, 0)),
        (("a",), (-1,)),
    ],
)
def test_malformed_multi_link_carriers_are_rejected(
    slots: tuple[str, ...], modes: tuple[int, ...]
) -> None:
    with pytest.raises(ValueError):
        MultiLinkBoundaryChannel(cutoff=1, slot_ids=slots, modes=modes)
