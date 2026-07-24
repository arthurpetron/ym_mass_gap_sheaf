"""Exact duplicate-surface probes at a genuinely six-valent four-dimensional link.

The anisotropic brick ``[0,1] x [0,2]^3`` is the smallest rectangular
four-dimensional cubical complex containing a link with all six transverse
plaquettes present.  The distinguished link runs from ``(0,1,1,1)`` to
``(1,1,1,1)`` in direction zero.

Twelve unit three-cubes contain that link.  Each cube boundary is a closed
binary plaquette surface.  Multiplying two such boundary observables retains
two independent fundamental character factors on every shared face and
forces the Haar integral on the distinguished link to use its full
higher-valent invariant projector.  This is therefore a first finite probe
beyond the trivalent four-cube boundary.

Unused brick links integrate to one.  :func:`evaluate_active_assignment`
removes them before gauge fixing; this is an exact support reduction, not a
change to the amplitude.
"""

from __future__ import annotations

import itertools
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import TypeAlias, cast

from computations.exact_haar_network import (
    P_ONE,
    GaugeFixedComplex,
    brick_complex_nd,
    chi,
)

Point4: TypeAlias = tuple[int, int, int, int]
Face: TypeAlias = list[tuple[int, int]]
FaceMeta: TypeAlias = tuple[tuple[int, ...], int, int]
FacePermutation: TypeAlias = tuple[int, ...]
SpinAssignment: TypeAlias = tuple[int, ...]

MINIMAL_SHAPE = (1, 2, 2, 2)
CENTRAL_LINK_TAIL: Point4 = (0, 1, 1, 1)
CENTRAL_LINK_HEAD: Point4 = (1, 1, 1, 1)


@dataclass(frozen=True)
class ElementarySurface:
    """Boundary of one unit three-cube containing the central link."""

    base: Point4
    axes: tuple[int, int, int]
    mask: int


@dataclass(frozen=True)
class PairProbe:
    """One stabilizer-orbit representative and its exact amplitude."""

    left: int
    right: int
    orbit_size: int
    overlap: int
    central_strand_counts: tuple[int, int, int, int, int, int]
    value: Fraction


def minimal_interior_link_brick() -> tuple[GaugeFixedComplex, list[Face], list[FaceMeta], int]:
    """Build the minimal brick and locate its distinguished six-valent link."""

    complex_, faces, meta = brick_complex_nd(MINIMAL_SHAPE)
    points = list(itertools.product(*(range(length + 1) for length in MINIMAL_SHAPE)))
    vertex_ids = {cast(Point4, point): index for index, point in enumerate(points)}
    central_edge = complex_.edges.index(
        (
            vertex_ids[CENTRAL_LINK_TAIL],
            vertex_ids[CENTRAL_LINK_HEAD],
        )
    )
    return complex_, faces, meta, central_edge


def incident_faces(faces: Sequence[Face], edge: int) -> tuple[int, ...]:
    """Return the face indices incident to ``edge``."""

    if edge < 0:
        raise ValueError("edge indices must be nonnegative")
    return tuple(
        face_index
        for face_index, face in enumerate(faces)
        if any(face_edge == edge for face_edge, _orientation in face)
    )


def unit_cube_boundary_mask(
    meta: Sequence[FaceMeta],
    base: Point4,
    axes: tuple[int, int, int],
) -> int:
    """Encode the six plaquettes in a unit three-cell boundary."""

    if tuple(sorted(axes)) != axes or len(set(axes)) != 3:
        raise ValueError("cube axes must be three distinct increasing directions")
    lookup = {face: index for index, face in enumerate(meta)}
    if len(lookup) != len(meta):
        raise ValueError("face metadata must be unique")

    mask = 0
    for first, second in itertools.combinations(axes, 2):
        normal = next(axis for axis in axes if axis not in (first, second))
        for side in (0, 1):
            point = list(base)
            point[normal] += side
            face = (tuple(point), first, second)
            try:
                mask |= 1 << lookup[face]
            except KeyError as error:
                raise ValueError(f"cube face {face} leaves the brick") from error
    return mask


def elementary_surfaces(meta: Sequence[FaceMeta]) -> tuple[ElementarySurface, ...]:
    """Return the 12 unit-cube boundaries containing the central link."""

    surfaces: list[ElementarySurface] = []
    transverse = (1, 2, 3)
    for first, second in itertools.combinations(transverse, 2):
        fixed = next(axis for axis in transverse if axis not in (first, second))
        axes = (0, first, second)
        for first_side in (0, 1):
            for second_side in (0, 1):
                base = list(CENTRAL_LINK_TAIL)
                base[first] = first_side
                base[second] = second_side
                base[fixed] = 1
                typed_base = cast(Point4, tuple(base))
                surfaces.append(
                    ElementarySurface(
                        typed_base,
                        axes,
                        unit_cube_boundary_mask(meta, typed_base, axes),
                    )
                )
    return tuple(surfaces)


def is_closed_binary_surface(
    faces: Sequence[Face],
    mask: int,
) -> bool:
    """Check the mod-two edge constraint for a face mask."""

    if mask < 0 or mask >> len(faces):
        return False
    used_edges = {
        edge
        for face_index, face in enumerate(faces)
        if (mask >> face_index) & 1
        for edge, _orientation in face
    }
    return all(
        sum(
            any(face_edge == edge for face_edge, _orientation in face)
            for face_index, face in enumerate(faces)
            if (mask >> face_index) & 1
        )
        % 2
        == 0
        for edge in used_edges
    )


def _transform_meta(
    face: FaceMeta,
    axis_map: tuple[int, int, int, int],
    reflected: tuple[bool, bool, bool, bool],
) -> FaceMeta:
    point, first, second = face
    face_directions = {first, second}
    transformed = [0, 0, 0, 0]
    for old_axis in range(4):
        new_axis = axis_map[old_axis]
        coordinate = point[old_axis]
        if reflected[old_axis]:
            coordinate = MINIMAL_SHAPE[new_axis] - coordinate - int(old_axis in face_directions)
        transformed[new_axis] = coordinate
    new_first, new_second = sorted((axis_map[first], axis_map[second]))
    return tuple(transformed), new_first, new_second


def central_link_stabilizer_maps(
    meta: Sequence[FaceMeta],
) -> tuple[FacePermutation, ...]:
    """Return the 96 brick symmetries preserving the central unoriented link."""

    lookup = {face: index for index, face in enumerate(meta)}
    if len(lookup) != len(meta):
        raise ValueError("face metadata must be unique")

    maps: list[FacePermutation] = []
    for transverse_image in itertools.permutations((1, 2, 3)):
        axis_map = cast(
            tuple[int, int, int, int],
            (0, *transverse_image),
        )
        for reflection_bits in range(16):
            reflected = cast(
                tuple[bool, bool, bool, bool],
                tuple(bool((reflection_bits >> axis) & 1) for axis in range(4)),
            )
            maps.append(tuple(lookup[_transform_meta(face, axis_map, reflected)] for face in meta))

    identity = tuple(range(len(meta)))
    maps.sort(key=lambda permutation: (permutation != identity, permutation))
    if len(maps) != 96 or len(set(maps)) != 96:
        raise AssertionError("central-link stabilizer action is not faithful")
    return tuple(maps)


def permute_mask(mask: int, permutation: Sequence[int]) -> int:
    """Apply an old-face to new-face permutation to a mask."""

    if mask < 0:
        raise ValueError("face masks must be nonnegative")
    out = 0
    for old_face, new_face in enumerate(permutation):
        if (mask >> old_face) & 1:
            out |= 1 << new_face
    return out


def unordered_pair_orbits(
    masks: Sequence[int],
    maps: Sequence[FacePermutation],
) -> tuple[tuple[tuple[int, int], ...], ...]:
    """Classify distinct unordered mask pairs under simultaneous symmetry."""

    pairs = {
        tuple(sorted((left, right)))
        for left_index, left in enumerate(masks)
        for right in masks[left_index + 1 :]
    }
    orbits: list[tuple[tuple[int, int], ...]] = []
    while pairs:
        representative = min(pairs)
        orbit = tuple(
            sorted(
                {
                    cast(
                        tuple[int, int],
                        tuple(
                            sorted(
                                (
                                    permute_mask(representative[0], permutation),
                                    permute_mask(representative[1], permutation),
                                )
                            )
                        ),
                    )
                    for permutation in maps
                }
            )
        )
        if not set(orbit) <= pairs:
            raise ValueError("the pair set is not stable under the supplied maps")
        pairs.difference_update(orbit)
        orbits.append(orbit)
    return tuple(orbits)


def fused_highest_channel_assignment(
    left: int,
    right: int,
    face_count: int,
) -> SpinAssignment:
    """Keep only the spin-one channel on every duplicate fundamental face.

    This is one term in the exact ``chi_1**2 = chi_0 + chi_2`` expansion, not
    the complete duplicate-surface observable.
    """

    if left < 0 or right < 0 or (left | right) >> face_count:
        raise ValueError("surface mask leaves the face set")
    return tuple(((left >> face) & 1) + ((right >> face) & 1) for face in range(face_count))


def evaluate_active_assignment(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
    spins: Sequence[int],
) -> Fraction:
    """Evaluate a connected fixed-spin support after removing unused links."""

    if len(spins) != len(faces):
        raise ValueError("one doubled-spin label is required per face")
    if any(spin < 0 for spin in spins):
        raise ValueError("doubled spins must be nonnegative")
    active_faces = [index for index, spin in enumerate(spins) if spin]
    if not active_faces:
        return Fraction(1)

    active_edges = sorted(
        {edge for face_index in active_faces for edge, _orientation in faces[face_index]}
    )
    edge_map = {edge: index for index, edge in enumerate(active_edges)}
    active_vertices = sorted({vertex for edge in active_edges for vertex in complex_.edges[edge]})
    vertex_map = {vertex: index for index, vertex in enumerate(active_vertices)}
    reduced_complex = GaugeFixedComplex(
        len(active_vertices),
        [
            (
                vertex_map[complex_.edges[edge][0]],
                vertex_map[complex_.edges[edge][1]],
            )
            for edge in active_edges
        ],
    )
    reduced_faces = [
        [(edge_map[edge], orientation) for edge, orientation in faces[face_index]]
        for face_index in active_faces
    ]
    factors = [
        chi(
            spins[face_index],
            reduced_complex.holonomy_of(reduced_face),
        )
        for face_index, reduced_face in zip(
            active_faces,
            reduced_faces,
            strict=True,
        )
    ]
    value = reduced_complex.contract_invariant(factors or [dict(P_ONE)])
    if any(power != 0 for power in value):
        raise AssertionError(f"fixed-spin amplitude acquired heat powers: {value}")
    return value.get(0, Fraction(0))


def evaluate_duplicate_pair(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
    left: int,
    right: int,
) -> Fraction:
    """Evaluate two fundamental surface observables without fusing duplicates.

    Every shared face contributes two distinct ``chi(1, holonomy)`` factors.
    Haar contraction therefore applies the complete invariant projector at
    each link, including the distinguished six-valent link.
    """

    if left < 0 or right < 0 or (left | right) >> len(faces):
        raise ValueError("surface mask leaves the face set")
    occurrences = [
        face for mask in (left, right) for face in range(len(faces)) if (mask >> face) & 1
    ]
    if not occurrences:
        return Fraction(1)

    active_faces = sorted(set(occurrences))
    active_edges = sorted(
        {edge for face_index in active_faces for edge, _orientation in faces[face_index]}
    )
    edge_map = {edge: index for index, edge in enumerate(active_edges)}
    active_vertices = sorted({vertex for edge in active_edges for vertex in complex_.edges[edge]})
    vertex_map = {vertex: index for index, vertex in enumerate(active_vertices)}
    reduced_complex = GaugeFixedComplex(
        len(active_vertices),
        [
            (
                vertex_map[complex_.edges[edge][0]],
                vertex_map[complex_.edges[edge][1]],
            )
            for edge in active_edges
        ],
    )
    reduced_faces = {
        face_index: [(edge_map[edge], orientation) for edge, orientation in faces[face_index]]
        for face_index in active_faces
    }
    factors = [chi(1, reduced_complex.holonomy_of(reduced_faces[face])) for face in occurrences]
    value = reduced_complex.contract_invariant(factors)
    if any(power != 0 for power in value):
        raise AssertionError(f"fixed-spin amplitude acquired heat powers: {value}")
    return value.get(0, Fraction(0))


def duplicate_pair_channel_sum(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
    left: int,
    right: int,
) -> Fraction:
    """Expand every duplicate face by ``chi_1**2 = chi_0 + chi_2`` exactly."""

    if left < 0 or right < 0 or (left | right) >> len(faces):
        raise ValueError("surface mask leaves the face set")
    symmetric = left ^ right
    overlap_faces = [face for face in range(len(faces)) if ((left & right) >> face) & 1]
    total = Fraction(0)
    for selected in range(1 << len(overlap_faces)):
        spins = [1 if (symmetric >> face) & 1 else 0 for face in range(len(faces))]
        for position, face in enumerate(overlap_faces):
            if (selected >> position) & 1:
                spins[face] = 2
        total += evaluate_active_assignment(complex_, faces, spins)
    return total


def two_cube_composite_surfaces(meta: Sequence[FaceMeta]) -> tuple[int, ...]:
    """Return all 66 XORs of two distinct elementary cube boundaries."""

    elementary = tuple(surface.mask for surface in elementary_surfaces(meta))
    composites = {
        left ^ right
        for left_index, left in enumerate(elementary)
        for right in elementary[left_index + 1 :]
    }
    if len(composites) != 66:
        raise AssertionError("elementary surface boundaries lost independence")
    return tuple(sorted(composites))


def _probe_orbits(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
    central_edge: int,
    orbits: Sequence[tuple[tuple[int, int], ...]],
) -> tuple[PairProbe, ...]:
    central_faces = incident_faces(faces, central_edge)
    probes: list[PairProbe] = []
    for orbit in orbits:
        left, right = orbit[0]
        strand_counts = tuple(
            ((left >> face) & 1) + ((right >> face) & 1) for face in range(len(faces))
        )
        probes.append(
            PairProbe(
                left=left,
                right=right,
                orbit_size=len(orbit),
                overlap=(left & right).bit_count(),
                central_strand_counts=cast(
                    tuple[int, int, int, int, int, int],
                    tuple(strand_counts[face] for face in central_faces),
                ),
                value=evaluate_duplicate_pair(complex_, faces, left, right),
            )
        )
    return tuple(probes)


def pair_probe_survey() -> tuple[PairProbe, ...]:
    """Evaluate one exact representative of every elementary pair orbit."""

    complex_, faces, meta, central_edge = minimal_interior_link_brick()
    masks = tuple(surface.mask for surface in elementary_surfaces(meta))
    maps = central_link_stabilizer_maps(meta)
    return _probe_orbits(
        complex_,
        faces,
        central_edge,
        unordered_pair_orbits(masks, maps),
    )


def composite_pair_orbits(
    meta: Sequence[FaceMeta],
) -> tuple[tuple[tuple[int, int], ...], ...]:
    """Return the 65 ordered-by-complexity orbits of two-cube composites."""

    orbits = unordered_pair_orbits(
        two_cube_composite_surfaces(meta),
        central_link_stabilizer_maps(meta),
    )
    return tuple(
        sorted(
            orbits,
            key=lambda orbit: (
                (orbit[0][0] | orbit[0][1]).bit_count(),
                (orbit[0][0] & orbit[0][1]).bit_count(),
                orbit[0],
            ),
        )
    )


def composite_pair_probe_survey(
    indices: Iterable[int] | None = None,
) -> tuple[PairProbe, ...]:
    """Evaluate selected or all two-cube-composite pair-orbit representatives."""

    complex_, faces, meta, central_edge = minimal_interior_link_brick()
    orbits = composite_pair_orbits(meta)
    selected = orbits if indices is None else tuple(orbits[index] for index in indices)
    return _probe_orbits(complex_, faces, central_edge, selected)


def sign_counts(probes: Iterable[PairProbe]) -> tuple[int, int, int]:
    """Return orbit-weighted counts of positive, zero, and negative pairs."""

    positive = zero = negative = 0
    for probe in probes:
        if probe.value > 0:
            positive += probe.orbit_size
        elif probe.value < 0:
            negative += probe.orbit_size
        else:
            zero += probe.orbit_size
    return positive, zero, negative
