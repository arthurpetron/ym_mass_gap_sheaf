"""Exact relative spin-structure gluing on two adjacent four-cubes.

The ``(2,1,1,1)`` brick contains three product tori which span both unit
four-cubes and avoid the six plaquettes in their common three-face.  Each
torus splits into two cylinders.  A representative binary-surface pair has
six overlap plaquettes, but the relative boundary condition across the
interface ties four of them into two two-plaquette caps.  Together with two
one-plaquette caps, the admissible channel space is therefore the 16-state
``K_(2,2)`` ledger.

The exact channel weight is the one-cube crossing kernel with subdivision
factors.  A selected spin-one (doubled label two) cap which spans the two
cells acquires ``1/dim(2)=1/3``; the one-cell caps acquire no such factor.
This is the character-convolution/Schur-orthogonality gluing law.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import permutations
from typing import TypeAlias, cast

from computations.exact_haar_network import (
    GaugeFixedComplex,
    brick_complex_nd,
    invariant_multiplicity,
)
from computations.four_strand_crossing_kernel import CROSSING_WEIGHT
from computations.hypercube4d_survey import (
    edge_cycles_homologous_mod2,
    face_chain_boundary_mask,
    kernel_basis,
    surface_betti_numbers_mod2,
    surfaces,
)

Point4: TypeAlias = tuple[int, int, int, int]
Face: TypeAlias = list[tuple[int, int]]
FaceMeta: TypeAlias = tuple[Point4, int, int]

TWO_CELL_SHAPE = (2, 1, 1, 1)

# This representative is derived from the binary kernel of the two-cell
# brick.  Its symmetric difference is the product
# boundary([0,2]x[0,1]) x boundary([0,1]x[0,1]).
GLUED_PAIR_LEFT = 0x10880CAB33
GLUED_PAIR_RIGHT = 0x1AD1A17C6AD
GLUED_TORUS = GLUED_PAIR_LEFT ^ GLUED_PAIR_RIGHT
GLUED_OVERLAP = GLUED_PAIR_LEFT & GLUED_PAIR_RIGHT

# The first interface-bearing obstruction to a purely mod-two boundary
# carrier.  Three selected label-two faces meet at one interface edge and
# carry the unique invariant in ``Inv(1 tensor 1 tensor 1)``.
BRANCHED_PAIR_LEFT = 0x10886C4055
BRANCHED_PAIR_RIGHT = 0x2125772DCB
BRANCHED_TORUS = BRANCHED_PAIR_LEFT ^ BRANCHED_PAIR_RIGHT
BRANCHED_OVERLAP = BRANCHED_PAIR_LEFT & BRANCHED_PAIR_RIGHT
BRANCHED_SELECTION = 0x240001
BRANCHED_INTERFACE_EDGE = 21


@dataclass(frozen=True)
class TwoCellSpinGluing:
    """Finite combinatorial certificate for the relative gluing probe."""

    cell_face_masks: tuple[int, int]
    interface_face_mask: int
    interface_edge_mask: int
    spanning_tori: tuple[int, int, int]
    surface: int
    overlap: int
    patch_masks: tuple[int, int]
    cap_masks: tuple[int, int, int, int]
    homology_families: tuple[tuple[int, int], tuple[int, int]]
    crossing_edges: tuple[tuple[int, int], ...]


def two_cell_brick() -> tuple[GaugeFixedComplex, list[Face], list[FaceMeta]]:
    """Build the deterministic two-four-cube brick."""

    complex_, faces, raw_meta = brick_complex_nd(TWO_CELL_SHAPE)
    meta = [
        (cast(Point4, point), first_direction, second_direction)
        for point, first_direction, second_direction in raw_meta
    ]
    return complex_, faces, meta


def _cell_face_mask(meta: list[FaceMeta], cell: int) -> int:
    if cell not in (0, 1):
        raise ValueError("the two-cell brick has cells zero and one")
    return sum(
        1 << face_index
        for face_index, (point, first_direction, second_direction) in enumerate(meta)
        if point[0] >= cell and point[0] + int(0 in (first_direction, second_direction)) <= cell + 1
    )


def _surface_edge_mask(faces: list[Face], surface_mask: int) -> int:
    edge_mask = 0
    for face_index, face in enumerate(faces):
        if (surface_mask >> face_index) & 1:
            for edge, _orientation in face:
                edge_mask |= 1 << edge
    return edge_mask


def transverse_axis_maps(meta: list[FaceMeta]) -> tuple[tuple[int, ...], ...]:
    """Return the six permutations of the unit transverse directions."""

    lookup = {face: index for index, face in enumerate(meta)}
    maps: list[tuple[int, ...]] = []
    for transverse in permutations((1, 2, 3)):
        axis_map = (0, *transverse)
        permutation: list[int] = []
        for point, first, second in meta:
            transformed_point = [0, 0, 0, 0]
            for old_axis, coordinate in enumerate(point):
                transformed_point[axis_map[old_axis]] = coordinate
            new_first, new_second = sorted((axis_map[first], axis_map[second]))
            transformed = (
                cast(Point4, tuple(transformed_point)),
                new_first,
                new_second,
            )
            permutation.append(lookup[transformed])
        maps.append(tuple(permutation))
    identity = tuple(range(len(meta)))
    maps.sort(key=lambda permutation: (permutation != identity, permutation))
    if len(maps) != 6 or len(set(maps)) != 6:
        raise AssertionError("the transverse axis action is not faithful")
    return tuple(maps)


def permute_face_mask(mask: int, permutation: tuple[int, ...]) -> int:
    """Apply an old-face to new-face permutation."""

    if mask < 0 or mask >> len(permutation):
        raise ValueError("face mask leaves the supplied permutation")
    return sum(1 << permutation[face] for face in range(len(permutation)) if (mask >> face) & 1)


def spanning_two_cell_tori() -> tuple[int, int, int]:
    """Return the three tori which split as one cylinder in each cell."""

    complex_, faces, meta = two_cell_brick()
    cell_masks = _cell_face_mask(meta, 0), _cell_face_mask(meta, 1)
    interface = cell_masks[0] & cell_masks[1]
    candidates: list[int] = []
    for surface in surfaces(kernel_basis(complex_, faces)):
        patches = surface & cell_masks[0], surface & cell_masks[1]
        if (
            surface & interface == 0
            and surface.bit_count() == 24
            and all(patch.bit_count() == 12 for patch in patches)
            and surface_betti_numbers_mod2(complex_, faces, surface) == (1, 2, 1)
            and all(
                surface_betti_numbers_mod2(complex_, faces, patch) == (1, 1, 0) for patch in patches
            )
        ):
            candidates.append(surface)
    if len(candidates) != 3:
        raise AssertionError("the two-cell brick lost its three spanning product tori")
    return cast(tuple[int, int, int], tuple(sorted(candidates)))


def minimal_overlap_caps(
    faces: list[Face],
    surface_mask: int,
    overlap_mask: int,
) -> tuple[int, ...]:
    """Return minimal overlap 2-chains whose boundaries lie on the surface."""

    overlap_faces = [
        face_index for face_index in range(len(faces)) if (overlap_mask >> face_index) & 1
    ]
    surface_edges = _surface_edge_mask(faces, surface_mask)
    candidates: list[int] = []
    for size in range(1, len(overlap_faces) + 1):
        for local_mask in range(1, 1 << len(overlap_faces)):
            if local_mask.bit_count() != size:
                continue
            face_mask = sum(
                1 << face_index
                for position, face_index in enumerate(overlap_faces)
                if (local_mask >> position) & 1
            )
            boundary = face_chain_boundary_mask(faces, face_mask)
            if boundary == 0 or boundary & ~surface_edges:
                continue
            if any(cap & face_mask == cap for cap in candidates):
                continue
            candidates.append(face_mask)
    return tuple(sorted(candidates, key=lambda cap: (-cap.bit_count(), cap)))


def _homology_families(
    faces: list[Face],
    surface: int,
    caps: tuple[int, ...],
) -> tuple[tuple[int, ...], ...]:
    remaining = set(range(len(caps)))
    families: list[tuple[int, ...]] = []
    while remaining:
        representative = min(remaining)
        representative_cycle = face_chain_boundary_mask(faces, caps[representative])
        family = tuple(
            index
            for index in sorted(remaining)
            if edge_cycles_homologous_mod2(
                faces,
                surface,
                representative_cycle,
                face_chain_boundary_mask(faces, caps[index]),
            )
        )
        remaining.difference_update(family)
        families.append(family)
    return tuple(families)


def _cycle_vertices(
    complex_: GaugeFixedComplex,
    edge_mask: int,
) -> set[int]:
    return {
        vertex
        for edge, endpoints in enumerate(complex_.edges)
        if (edge_mask >> edge) & 1
        for vertex in endpoints
    }


@cache
def build_two_cell_spin_gluing() -> TwoCellSpinGluing:
    """Construct and validate the relative gluing certificate."""

    complex_, faces, meta = two_cell_brick()
    cell_masks = _cell_face_mask(meta, 0), _cell_face_mask(meta, 1)
    interface_faces = cell_masks[0] & cell_masks[1]
    interface_edges = _surface_edge_mask(faces, interface_faces)
    spanning_tori = spanning_two_cell_tori()
    if GLUED_TORUS not in spanning_tori:
        raise AssertionError("the pinned surface pair lost its spanning torus")
    caps = minimal_overlap_caps(faces, GLUED_TORUS, GLUED_OVERLAP)
    if len(caps) != 4 or sorted(cap.bit_count() for cap in caps) != [1, 1, 2, 2]:
        raise AssertionError("the relative overlap did not reduce to four caps")
    families = _homology_families(faces, GLUED_TORUS, caps)
    if tuple(len(family) for family in families) != (2, 2):
        raise AssertionError("the four caps did not form two homology families")

    crossing_edges: list[tuple[int, int]] = []
    for left in range(len(caps)):
        left_vertices = _cycle_vertices(
            complex_,
            face_chain_boundary_mask(faces, caps[left]),
        )
        for right in range(left + 1, len(caps)):
            right_vertices = _cycle_vertices(
                complex_,
                face_chain_boundary_mask(faces, caps[right]),
            )
            if len(left_vertices & right_vertices) % 2:
                crossing_edges.append((left, right))

    expected_crossings = {
        tuple(sorted((left, right))) for left in families[0] for right in families[1]
    }
    if set(crossing_edges) != expected_crossings:
        raise AssertionError("cap intersections are not the complete bipartite graph")

    return TwoCellSpinGluing(
        cell_face_masks=cell_masks,
        interface_face_mask=interface_faces,
        interface_edge_mask=interface_edges,
        spanning_tori=spanning_tori,
        surface=GLUED_TORUS,
        overlap=GLUED_OVERLAP,
        patch_masks=(
            GLUED_TORUS & cell_masks[0],
            GLUED_TORUS & cell_masks[1],
        ),
        cap_masks=caps,
        homology_families=cast(
            tuple[tuple[int, int], tuple[int, int]],
            families,
        ),
        crossing_edges=tuple(crossing_edges),
    )


def raw_channel_face_mask(channel_mask: int) -> int:
    """Decode one of the 64 raw overlap-plaquette channel selections."""

    overlap_faces = [
        face_index
        for face_index in range(GLUED_OVERLAP.bit_length())
        if (GLUED_OVERLAP >> face_index) & 1
    ]
    if channel_mask < 0 or channel_mask >> len(overlap_faces):
        raise ValueError("raw channel mask leaves the six overlap plaquettes")
    return sum(
        1 << face_index
        for position, face_index in enumerate(overlap_faces)
        if (channel_mask >> position) & 1
    )


def raw_channel_interface_defect(channel_mask: int) -> int:
    """Return the relative boundary left off the spanning torus."""

    return relative_boundary_defect(
        build_two_cell_spin_gluing().surface,
        raw_channel_face_mask(channel_mask),
    )


def relative_boundary_defect(
    surface_mask: int,
    selected_face_mask: int,
) -> int:
    """Return the part of a selected overlap boundary lying off a surface."""

    _complex, faces, _meta = two_cell_brick()
    if (
        surface_mask < 0
        or selected_face_mask < 0
        or (surface_mask | selected_face_mask) >> len(faces)
    ):
        raise ValueError("face mask leaves the two-cell brick")
    surface_edges = _surface_edge_mask(faces, surface_mask)
    return face_chain_boundary_mask(faces, selected_face_mask) & ~surface_edges


def channel_edge_invariant_multiplicities(
    surface_mask: int,
    selected_face_mask: int,
) -> tuple[int, ...]:
    """Return the SU(2) invariant multiplicity at every brick edge."""

    complex_, faces, _meta = two_cell_brick()
    if (
        surface_mask < 0
        or selected_face_mask < 0
        or surface_mask & selected_face_mask
        or (surface_mask | selected_face_mask) >> len(faces)
    ):
        raise ValueError("surface and selected overlap must be disjoint brick masks")
    labels = [
        1
        if (surface_mask >> face_index) & 1
        else 2
        if (selected_face_mask >> face_index) & 1
        else 0
        for face_index in range(len(faces))
    ]
    multiplicities: list[int] = []
    for edge in range(len(complex_.edges)):
        incident_labels = [
            labels[face_index]
            for face_index, face in enumerate(faces)
            if labels[face_index] and any(face_edge == edge for face_edge, _orientation in face)
        ]
        multiplicities.append(invariant_multiplicity(incident_labels))
    return tuple(multiplicities)


def raw_channel_is_admissible(channel_mask: int) -> bool:
    """Test exact SU(2) edge-invariant admissibility of one raw channel."""

    return all(
        multiplicity > 0
        for multiplicity in channel_edge_invariant_multiplicities(
            GLUED_TORUS,
            raw_channel_face_mask(channel_mask),
        )
    )


def admissible_raw_channel_masks() -> tuple[int, ...]:
    """Return the 16 raw channels whose relative interface defects cancel."""

    return tuple(
        mask for mask in range(1 << GLUED_OVERLAP.bit_count()) if raw_channel_is_admissible(mask)
    )


def cap_selection_face_mask(cap_selection: int) -> int:
    """Expand four global cap bits to their one- or two-face chains."""

    certificate = build_two_cell_spin_gluing()
    if cap_selection < 0 or cap_selection >> len(certificate.cap_masks):
        raise ValueError("cap selection leaves the four-cap ledger")
    return sum(
        cap for index, cap in enumerate(certificate.cap_masks) if (cap_selection >> index) & 1
    )


def cap_selection_raw_mask(cap_selection: int) -> int:
    """Encode a cap selection in the six raw overlap-face bits."""

    selected_faces = cap_selection_face_mask(cap_selection)
    overlap_faces = [
        face_index
        for face_index in range(GLUED_OVERLAP.bit_length())
        if (GLUED_OVERLAP >> face_index) & 1
    ]
    return sum(
        1 << position
        for position, face_index in enumerate(overlap_faces)
        if (selected_faces >> face_index) & 1
    )


def glued_channel_homology_parities(cap_selection: int) -> tuple[int, int]:
    """Return the two parities in ``H1(torus; GF(2))``."""

    certificate = build_two_cell_spin_gluing()
    if cap_selection < 0 or cap_selection >> len(certificate.cap_masks):
        raise ValueError("cap selection leaves the four-cap ledger")
    return cast(
        tuple[int, int],
        tuple(
            sum((cap_selection >> cap) & 1 for cap in family) % 2
            for family in certificate.homology_families
        ),
    )


def glued_channel_weight(cap_selection: int) -> Fraction:
    """Return the exact subdivided ``K_(2,2)`` channel weight."""

    certificate = build_two_cell_spin_gluing()
    if cap_selection < 0 or cap_selection >> len(certificate.cap_masks):
        raise ValueError("cap selection leaves the four-cap ledger")
    selected = tuple((cap_selection >> cap) & 1 for cap in range(len(certificate.cap_masks)))
    value = Fraction(1, 2 ** certificate.surface.bit_count())
    for cap, cap_mask in enumerate(certificate.cap_masks):
        if selected[cap]:
            value *= Fraction(1, 3) ** (cap_mask.bit_count() - 1)
    for left, right in certificate.crossing_edges:
        value *= CROSSING_WEIGHT[selected[left]][selected[right]]
    return value


def glued_partition() -> Fraction:
    """Sum the complete 16-channel relative gluing ledger."""

    return sum(
        (glued_channel_weight(selection) for selection in range(1 << 4)),
        start=Fraction(0),
    )
