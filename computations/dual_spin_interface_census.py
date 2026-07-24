"""Exact first-branching census for the two-four-cube SU(2) dual.

The two-cell brick has 8,192 closed binary surfaces and 234 genus-one
surfaces which use at least one plaquette in the shared three-face.  Each
such torus is the symmetric difference of 4,096 unordered binary-surface
pairs, giving 958,464 physical pairs.

This module quotients that finite family by the full 96-element cuboid
symmetry group.  The first branching filtration consists of pairs with at
most five overlap faces: five is the first order at which the relative
mod-two boundary can terminate at an admissible trivalent spin-one packet.
The stratum has 58,878 pairs, 1,219 pair orbits, and 2,166 admissible
resolved-channel orbits.  Exactly 14 of those orbits have nonzero relative
boundary defect.  Their exact Haar amplitudes are all positive.

The cutoff at overlap five is an explicit filtration boundary, not a claim
about the remaining pair space.  Direct quaternion-polynomial integration
does not scale across all 2,166 representatives; the next gate must contract
the decorated interface packets in a fusion basis.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import permutations, product
from typing import TypeAlias, cast

from computations.dual_spin_gluing import (
    InterfaceEdgePacket,
    build_two_cell_spin_gluing,
    decorated_interface_carrier,
    permute_face_mask,
    relative_boundary_defect,
    two_cell_brick,
)
from computations.exact_haar_network import invariant_multiplicity
from computations.hypercube4d_survey import (
    kernel_basis,
    surface_betti_numbers_mod2,
    surfaces,
)

FacePermutation: TypeAlias = tuple[int, ...]
ResolvedChannel: TypeAlias = tuple[int, int]
SurfacePair: TypeAlias = tuple[int, int]

FIRST_BRANCHING_OVERLAP = 5


@dataclass(frozen=True)
class InterfacePairCensus:
    """Pinned cardinalities for the interface-bearing pair filtration."""

    closed_surfaces: int
    genus_one_surfaces: int
    interface_genus_one_surfaces: int
    physical_pairs: int
    overlap_census: tuple[tuple[int, int], ...]
    filtered_pairs: int
    filtered_pair_orbits: int
    raw_orbit_representative_channels: int
    admissible_orbit_representative_channels: int
    resolved_channel_orbits: int
    nonzero_defect_channel_orbits: int


@dataclass(frozen=True)
class ResolvedChannelQuotient:
    """Symmetry quotient of a bounded-overlap resolved-channel family."""

    raw_representative_channels: int
    admissible_representative_channels: int
    representatives: tuple[ResolvedChannel, ...]


def _permute_surface_pair(
    pair: SurfacePair,
    permutation: FacePermutation,
) -> SurfacePair:
    return cast(
        SurfacePair,
        tuple(
            sorted(
                (
                    permute_face_mask(pair[0], permutation),
                    permute_face_mask(pair[1], permutation),
                )
            )
        ),
    )


@cache
def brick_symmetry_face_maps() -> tuple[FacePermutation, ...]:
    """Return the full 96-element face action of the ``(2,1,1,1)`` brick."""

    _complex, _faces, meta = two_cell_brick()
    shape = (2, 1, 1, 1)
    lookup = {face: index for index, face in enumerate(meta)}
    maps: list[FacePermutation] = []
    for transverse_permutation in permutations((1, 2, 3)):
        axis_map = (0, *transverse_permutation)
        for reflections in product((False, True), repeat=4):
            permutation: list[int] = []
            for point, first, second in meta:
                transformed_point = [0, 0, 0, 0]
                for old_axis, coordinate in enumerate(point):
                    transformed_coordinate = (
                        shape[old_axis]
                        - coordinate
                        - int(old_axis in (first, second))
                        if reflections[old_axis]
                        else coordinate
                    )
                    transformed_point[axis_map[old_axis]] = transformed_coordinate
                new_first, new_second = sorted((axis_map[first], axis_map[second]))
                permutation.append(
                    lookup[
                        (
                            cast(tuple[int, int, int, int], tuple(transformed_point)),
                            new_first,
                            new_second,
                        )
                    ]
                )
            maps.append(tuple(permutation))
    result = tuple(sorted(set(maps)))
    if len(result) != 96:
        raise AssertionError("the two-cell cuboid symmetry action is not faithful")
    return result


@cache
def closed_surface_masks() -> tuple[int, ...]:
    """Return all closed binary surfaces in the two-cell brick."""

    complex_, faces, _meta = two_cell_brick()
    result = tuple(surfaces(kernel_basis(complex_, faces)))
    if len(result) != 8192:
        raise AssertionError("the two-cell binary cycle space changed dimension")
    return result


@cache
def genus_one_surface_masks() -> tuple[int, ...]:
    """Return every connected mod-two genus-one surface in the brick."""

    complex_, faces, _meta = two_cell_brick()
    return tuple(
        surface
        for surface in closed_surface_masks()
        if surface_betti_numbers_mod2(complex_, faces, surface) == (1, 2, 1)
    )


@cache
def interface_genus_one_surface_masks() -> tuple[int, ...]:
    """Return genus-one surfaces which use the shared three-face."""

    interface = build_two_cell_spin_gluing().interface_face_mask
    return tuple(surface for surface in genus_one_surface_masks() if surface & interface)


@cache
def interface_pair_overlap_census() -> tuple[tuple[int, int], ...]:
    """Count all physical pairs by their number of coincident faces."""

    counts: Counter[int] = Counter()
    for surface in interface_genus_one_surface_masks():
        for left in closed_surface_masks():
            right = left ^ surface
            if left < right:
                counts[(left & right).bit_count()] += 1
    return tuple(sorted(counts.items()))


@cache
def bounded_overlap_pair_orbit_representatives(
    maximum_overlap: int = FIRST_BRANCHING_OVERLAP,
) -> tuple[SurfacePair, ...]:
    """Classify physical interface pairs through a fixed overlap order."""

    if maximum_overlap < 0:
        raise ValueError("the overlap cutoff must be nonnegative")
    pairs = {
        (left, right)
        for surface in interface_genus_one_surface_masks()
        for left in closed_surface_masks()
        for right in (left ^ surface,)
        if left < right and (left & right).bit_count() <= maximum_overlap
    }
    maps = brick_symmetry_face_maps()
    representatives: list[SurfacePair] = []
    while pairs:
        representative = min(pairs)
        orbit = {
            _permute_surface_pair(representative, permutation)
            for permutation in maps
        }
        if not orbit <= pairs:
            raise AssertionError("bounded-overlap pair family is not symmetry stable")
        pairs.difference_update(orbit)
        representatives.append(representative)
    return tuple(representatives)


@cache
def _edge_face_indices() -> tuple[tuple[int, ...], ...]:
    complex_, faces, _meta = two_cell_brick()
    return tuple(
        tuple(
            face_index
            for face_index, face in enumerate(faces)
            if any(face_edge == edge for face_edge, _orientation in face)
        )
        for edge in range(len(complex_.edges))
    )


@cache
def _face_count() -> int:
    _complex, faces, _meta = two_cell_brick()
    return len(faces)


def resolved_channel_is_admissible(surface: int, selected: int) -> bool:
    """Test every local SU(2) invariant without invoking the Haar integrator."""

    face_count = _face_count()
    if (
        surface < 0
        or selected < 0
        or surface & selected
        or (surface | selected) >> face_count
    ):
        raise ValueError("surface and selected masks must be disjoint brick masks")
    labels = tuple(
        1 if (surface >> face) & 1 else 2 if (selected >> face) & 1 else 0
        for face in range(face_count)
    )
    return all(
        invariant_multiplicity(tuple(labels[face] for face in incident if labels[face])) > 0
        for incident in _edge_face_indices()
    )


@cache
def bounded_overlap_resolved_channel_quotient(
    maximum_overlap: int = FIRST_BRANCHING_OVERLAP,
) -> ResolvedChannelQuotient:
    """Quotient all admissible resolved channels in the bounded pair family."""

    maps = brick_symmetry_face_maps()
    representatives: set[ResolvedChannel] = set()
    raw_count = 0
    admissible_count = 0
    for left, right in bounded_overlap_pair_orbit_representatives(maximum_overlap):
        surface = left ^ right
        overlap_faces = [
            face
            for face in range(max((left | right).bit_length(), 1))
            if ((left & right) >> face) & 1
        ]
        for selection in range(1 << len(overlap_faces)):
            raw_count += 1
            selected = sum(
                1 << face
                for index, face in enumerate(overlap_faces)
                if (selection >> index) & 1
            )
            if not resolved_channel_is_admissible(surface, selected):
                continue
            admissible_count += 1
            representatives.add(
                min(
                    (
                        permute_face_mask(surface, permutation),
                        permute_face_mask(selected, permutation),
                    )
                    for permutation in maps
                )
            )
    return ResolvedChannelQuotient(
        raw_representative_channels=raw_count,
        admissible_representative_channels=admissible_count,
        representatives=tuple(sorted(representatives)),
    )


@cache
def nonzero_defect_channel_representatives(
    maximum_overlap: int = FIRST_BRANCHING_OVERLAP,
) -> tuple[ResolvedChannel, ...]:
    """Return the genuinely branched resolved-channel orbit representatives."""

    return tuple(
        (surface, selected)
        for surface, selected in bounded_overlap_resolved_channel_quotient(
            maximum_overlap
        ).representatives
        if relative_boundary_defect(surface, selected)
    )


def channel_interface_carrier(
    channel: ResolvedChannel,
) -> tuple[InterfaceEdgePacket, ...]:
    """Return the decorated interface state of a resolved-channel orbit."""

    return decorated_interface_carrier(*channel)


@cache
def exact_interface_channel_value(channel: ResolvedChannel) -> Fraction:
    """Evaluate one resolved-channel representative by exact Haar integration."""

    from computations.interior_link4d_probe import evaluate_active_assignment

    complex_, faces, _meta = two_cell_brick()
    surface, selected = channel
    spins = tuple(
        1
        if (surface >> face) & 1
        else 2
        if (selected >> face) & 1
        else 0
        for face in range(len(faces))
    )
    return evaluate_active_assignment(complex_, faces, spins)


@cache
def first_branching_census() -> InterfacePairCensus:
    """Return the complete cardinality certificate through overlap five."""

    quotient = bounded_overlap_resolved_channel_quotient()
    overlap_census = interface_pair_overlap_census()
    return InterfacePairCensus(
        closed_surfaces=len(closed_surface_masks()),
        genus_one_surfaces=len(genus_one_surface_masks()),
        interface_genus_one_surfaces=len(interface_genus_one_surface_masks()),
        physical_pairs=sum(count for _overlap, count in overlap_census),
        overlap_census=overlap_census,
        filtered_pairs=sum(
            count
            for overlap, count in overlap_census
            if overlap <= FIRST_BRANCHING_OVERLAP
        ),
        filtered_pair_orbits=len(bounded_overlap_pair_orbit_representatives()),
        raw_orbit_representative_channels=quotient.raw_representative_channels,
        admissible_orbit_representative_channels=(
            quotient.admissible_representative_channels
        ),
        resolved_channel_orbits=len(quotient.representatives),
        nonzero_defect_channel_orbits=len(nonzero_defect_channel_representatives()),
    )
