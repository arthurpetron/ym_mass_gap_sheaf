"""Exact carrier audit for the four-rim CD-2 boundary channel.

The current Lean ``DualBoundaryState`` is the correct CD-1 carrier for one
reflected interface: one ``CharacterPacket`` and one representation-mode
index.  The wheel channel is different.  It has four ordered rim slots and
four cyclic words ``X_i X_(i+1)^-1``.  Equal labels in the unit-rim example
do not erase those four slot identities.

This module packages the minimal multi-slot carrier, verifies the abstract
cyclic word embedding from the exact manifest, and makes the remaining
physical half-time slot map explicit.  It proves a structural requirement,
not a physical reflection theorem.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from computations.dual_positivity_manifest import (
    UnitRimManifest,
    build_unit_rim_manifest,
)

OrientedRimWord: TypeAlias = tuple[tuple[int, int], tuple[int, int]]


@dataclass(frozen=True)
class MultiLinkBoundaryChannel:
    """An ordered finite boundary representation assignment."""

    cutoff: int
    slot_ids: tuple[str, ...]
    modes: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.cutoff < 0:
            raise ValueError("a boundary cutoff must be nonnegative")
        if not self.slot_ids:
            raise ValueError("a boundary channel must contain at least one slot")
        if len(self.slot_ids) != len(self.modes):
            raise ValueError("boundary slot and mode lists have different lengths")
        if len(set(self.slot_ids)) != len(self.slot_ids):
            raise ValueError("boundary slot identifiers must be unique")
        if any(mode < 0 for mode in self.modes):
            raise ValueError("boundary modes must be nonnegative")

    @property
    def arity(self) -> int:
        """Return the number of independently tracked boundary slots."""

        return len(self.slot_ids)

    def supported(self) -> bool:
        """Check every representation label against the physical cutoff."""

        return max(self.modes) <= self.cutoff


@dataclass(frozen=True)
class AbstractWheelRimEmbedding:
    """The four-slot cyclic carrier read directly from the wheel manifest."""

    channel: MultiLinkBoundaryChannel
    integrated_link_ids: tuple[int, ...]
    rim_words: tuple[OrientedRimWord, ...]

    def is_cyclic(self) -> bool:
        """Check the exact ``(+i,-(i+1))`` wheel incidence and orientation."""

        size = self.channel.arity
        return (
            size == 4
            and self.integrated_link_ids == tuple(range(size))
            and len(self.rim_words) == size
            and all(
                word == ((index, 1), ((index + 1) % size, -1))
                for index, word in enumerate(self.rim_words)
            )
        )

    def slot_provenance_is_preserved(self) -> bool:
        """Ensure equal mode values have not collapsed distinct rim slots."""

        return len(set(self.channel.slot_ids)) == self.channel.arity

    def is_abstractly_closed(self) -> bool:
        """Decide the manifest-level carrier embedding."""

        return (
            self.channel.supported()
            and self.is_cyclic()
            and self.slot_provenance_is_preserved()
        )


@dataclass(frozen=True)
class BoundaryCarrierFrontier:
    """Status of the carrier upgrade required between CD-1 and CD-2."""

    existing_single_interface_arity: int
    required_wheel_arity: int
    abstract_cyclic_embedding_pinned: bool
    physical_half_time_slot_ids_pinned: bool = False
    reflection_slot_permutation_pinned: bool = False
    intertwiner_basis_pinned: bool = False

    def single_interface_carrier_is_sufficient(self) -> bool:
        """Check whether the old carrier has enough independent slots."""

        return self.existing_single_interface_arity >= self.required_wheel_arity

    def first_open_field(self) -> str | None:
        """Return the next missing carrier datum."""

        ordered = (
            ("abstract_cyclic_embedding_pinned", self.abstract_cyclic_embedding_pinned),
            (
                "physical_half_time_slot_ids_pinned",
                self.physical_half_time_slot_ids_pinned,
            ),
            (
                "reflection_slot_permutation_pinned",
                self.reflection_slot_permutation_pinned,
            ),
            ("intertwiner_basis_pinned", self.intertwiner_basis_pinned),
        )
        for name, closed in ordered:
            if not closed:
                return name
        return None

    def is_cd2_boundary_carrier_closed(self) -> bool:
        """Require the physical slots, reflection, and intertwiner basis."""

        return (
            not self.single_interface_carrier_is_sufficient()
            and self.first_open_field() is None
        )


def build_abstract_unit_rim_embedding(
    cutoff: int,
    manifest: UnitRimManifest | None = None,
) -> AbstractWheelRimEmbedding:
    """Construct and check the four-slot manifest carrier."""

    payload = build_unit_rim_manifest() if manifest is None else manifest
    slots = tuple(f"wheel-rim:{index}" for index in range(len(payload.rim_spins)))
    words_raw = tuple(word.steps for word in payload.topology.rim_words)
    if any(len(word) != 2 for word in words_raw):
        raise ValueError("every wheel rim word must contain exactly two oriented links")
    words = tuple(
        ((word[0][0], word[0][1]), (word[1][0], word[1][1]))
        for word in words_raw
    )
    embedding = AbstractWheelRimEmbedding(
        channel=MultiLinkBoundaryChannel(
            cutoff=cutoff,
            slot_ids=slots,
            modes=payload.rim_spins,
        ),
        integrated_link_ids=payload.topology.integrated_links,
        rim_words=words,
    )
    if cutoff >= max(payload.rim_spins) and not embedding.is_abstractly_closed():
        raise AssertionError("the exact manifest failed its four-rim carrier audit")
    return embedding


def current_boundary_carrier_frontier(cutoff: int = 2) -> BoundaryCarrierFrontier:
    """Return the honest carrier frontier after the abstract rim embedding."""

    embedding = build_abstract_unit_rim_embedding(cutoff)
    return BoundaryCarrierFrontier(
        existing_single_interface_arity=1,
        required_wheel_arity=embedding.channel.arity,
        abstract_cyclic_embedding_pinned=embedding.is_abstractly_closed(),
    )
