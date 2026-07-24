"""BF1.6 spacing-changing Haar block on a corrected-slab half-carrier.

Four fine spatial plaquettes in a ``2 x 2`` disk are embedded in the lower
half of the extent-three corrected reflection slab.  Every internal link is
integrated exactly and the result is projected onto the coarse boundary
character basis.  At cutoff two the unnormalized coarse modes are

``1, 2 s^12, 3 s^32``.

This is the heat-kernel semigroup at four times the fine heat time, obtained
from the literal four-plaquette Haar network.  Labels ``0, 1, 2`` are
transported identically, the reflection partner is the corresponding upper
disk, and the exact remainder outside the selected cutoff-two carrier is
zero.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from typing import TypeAlias

from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
    slab_face_reflection_permutation,
)
from computations.dual_positivity_geometry_bridge import Link4, Plaquette4
from computations.exact_haar_network import (
    GaugeFixedComplex,
    SPoly,
    chi,
    dimension,
    heat_activity,
    sp_add_into,
    sp_clean,
)

ModeLedger: TypeAlias = tuple[tuple[int, SPoly], ...]


def _two_by_two_disk() -> tuple[
    GaugeFixedComplex,
    tuple[tuple[tuple[int, int], ...], ...],
    tuple[tuple[int, int], ...],
]:
    def vertex(first: int, second: int) -> int:
        return 3 * first + second

    edges: list[tuple[int, int]] = []
    edge_ids: dict[tuple[int, int], int] = {}

    def edge(tail: int, head: int) -> int:
        key = tail, head
        if key not in edge_ids:
            edge_ids[key] = len(edges)
            edges.append(key)
        return edge_ids[key]

    for first in range(2):
        for second in range(3):
            edge(vertex(first, second), vertex(first + 1, second))
    for first in range(3):
        for second in range(2):
            edge(vertex(first, second), vertex(first, second + 1))
    complex_ = GaugeFixedComplex(9, edges)

    plaquettes: list[tuple[tuple[int, int], ...]] = []
    for first in range(2):
        for second in range(2):
            plaquettes.append(
                (
                    (edge(vertex(first, second), vertex(first + 1, second)), 1),
                    (
                        edge(
                            vertex(first + 1, second),
                            vertex(first + 1, second + 1),
                        ),
                        1,
                    ),
                    (
                        edge(
                            vertex(first, second + 1),
                            vertex(first + 1, second + 1),
                        ),
                        -1,
                    ),
                    (
                        edge(
                            vertex(first, second),
                            vertex(first, second + 1),
                        ),
                        -1,
                    ),
                )
            )
    coarse_boundary = (
        (edge(vertex(0, 0), vertex(1, 0)), 1),
        (edge(vertex(1, 0), vertex(2, 0)), 1),
        (edge(vertex(2, 0), vertex(2, 1)), 1),
        (edge(vertex(2, 1), vertex(2, 2)), 1),
        (edge(vertex(1, 2), vertex(2, 2)), -1),
        (edge(vertex(0, 2), vertex(1, 2)), -1),
        (edge(vertex(0, 1), vertex(0, 2)), -1),
        (edge(vertex(0, 0), vertex(0, 1)), -1),
    )
    return complex_, tuple(plaquettes), coarse_boundary


def _lower_block_plaquettes() -> tuple[Plaquette4, ...]:
    return tuple(
        ((first, second, 0, 0), (0, 1))
        for first in range(2)
        for second in range(2)
    )


def _coarse_boundary_links() -> tuple[tuple[Link4, int], ...]:
    return (
        (((0, 0, 0, 0), 0), 1),
        (((1, 0, 0, 0), 0), 1),
        (((2, 0, 0, 0), 1), 1),
        (((2, 1, 0, 0), 1), 1),
        (((1, 2, 0, 0), 0), -1),
        (((0, 2, 0, 0), 0), -1),
        (((0, 1, 0, 0), 1), -1),
        (((0, 0, 0, 0), 1), -1),
    )


@dataclass(frozen=True)
class HalfSurfaceBlockPushforward:
    """Exact unnormalized fine-to-coarse transport for one spatial disk."""

    corrected_slab_extent: int
    corrected_slab_half: int
    fine_face_ids: tuple[int, ...]
    reflected_fine_face_ids: tuple[int, ...]
    coarse_boundary_links: tuple[tuple[Link4, int], ...]
    spacing_factor: int
    cutoff: int
    coarse_modes: ModeLedger
    coarse_intertwiner_transport: tuple[tuple[int, int], ...]
    haar_total_mass: SPoly
    identity_mass: SPoly
    remainder_outside_carrier: ModeLedger

    def validates(self) -> bool:
        expected_modes: ModeLedger = (
            (0, {0: Fraction(1)}),
            (1, {12: Fraction(2)}),
            (2, {32: Fraction(3)}),
        )
        return (
            self.corrected_slab_extent == 3
            and self.corrected_slab_half == 1
            and len(self.fine_face_ids) == 4
            and len(self.reflected_fine_face_ids) == 4
            and len(self.coarse_boundary_links) == 8
            and self.spacing_factor == 2
            and self.cutoff == 2
            and self.coarse_modes == expected_modes
            and self.coarse_intertwiner_transport == ((0, 0), (1, 1), (2, 2))
            and self.haar_total_mass == {0: Fraction(1)}
            and self.identity_mass
            == {
                0: Fraction(1),
                12: Fraction(4),
                32: Fraction(9),
            }
            and self.remainder_outside_carrier == ()
        )


@cache
def half_surface_block_pushforward(
    cutoff: int = 2,
) -> HalfSurfaceBlockPushforward:
    if cutoff != 2:
        raise ValueError("the BF1.6 regression certificate is pinned at cutoff two")
    complex_, plaquettes, coarse_boundary = _two_by_two_disk()
    fine_factors = [
        heat_activity(complex_.holonomy_of(face), cutoff)
        for face in plaquettes
    ]
    coarse_modes: list[tuple[int, SPoly]] = []
    for label in range(cutoff + 1):
        projection = complex_.contract_invariant(
            fine_factors
            + [chi(label, complex_.holonomy_of(coarse_boundary))]
        )
        coarse_modes.append((label, projection))

    remainder: list[tuple[int, SPoly]] = []
    for label in range(cutoff + 1, 2 * cutoff + 1):
        projection = complex_.contract_invariant(
            fine_factors
            + [chi(label, complex_.holonomy_of(coarse_boundary))]
        )
        if projection:
            remainder.append((label, projection))

    mode_dict = dict(coarse_modes)
    identity_mass: SPoly = {}
    for label, mode in coarse_modes:
        sp_add_into(identity_mass, mode, Fraction(dimension(label)))

    extent = 3
    half = 1
    slab_plaquettes = boundary_complete_slab_plaquettes(extent)
    face_index = {
        plaquette: index for index, plaquette in enumerate(slab_plaquettes)
    }
    lower_faces = _lower_block_plaquettes()
    if not set(lower_faces).issubset(face_index):
        raise AssertionError("the local disk left the corrected slab")
    fine_face_ids = tuple(face_index[plaquette] for plaquette in lower_faces)
    reflection = slab_face_reflection_permutation(extent)
    reflected_face_ids = tuple(reflection[index] for index in fine_face_ids)
    return HalfSurfaceBlockPushforward(
        corrected_slab_extent=extent,
        corrected_slab_half=half,
        fine_face_ids=fine_face_ids,
        reflected_fine_face_ids=reflected_face_ids,
        coarse_boundary_links=_coarse_boundary_links(),
        spacing_factor=2,
        cutoff=cutoff,
        coarse_modes=tuple(coarse_modes),
        coarse_intertwiner_transport=tuple(
            (label, label) for label in range(cutoff + 1)
        ),
        haar_total_mass=mode_dict[0],
        identity_mass=sp_clean(identity_mass),
        remainder_outside_carrier=tuple(remainder),
    )


@dataclass(frozen=True)
class BF16Certificate:
    """Complete finite BF1.6 positive-exit certificate."""

    cut_census_valid: bool
    reflection_transport_valid: bool
    reconstruction_valid: bool
    gram_valid: bool
    block_pushforward: HalfSurfaceBlockPushforward

    @property
    def exit_kind(self) -> str:
        return "positive-finite-selected-sector"

    def validates(self) -> bool:
        return (
            self.cut_census_valid
            and self.reflection_transport_valid
            and self.reconstruction_valid
            and self.gram_valid
            and self.block_pushforward.validates()
        )


@cache
def bf16_certificate() -> BF16Certificate:
    from computations.reflection_cut_half_surface import (
        cut_reflection_transport_audit,
        half_carrier_gram_audit,
        half_surface_reconstruction_audit,
        reflection_cut_census,
    )

    return BF16Certificate(
        cut_census_valid=reflection_cut_census().validates(),
        reflection_transport_valid=cut_reflection_transport_audit().validates(),
        reconstruction_valid=half_surface_reconstruction_audit().validates(),
        gram_valid=half_carrier_gram_audit().validates(),
        block_pushforward=half_surface_block_pushforward(),
    )
