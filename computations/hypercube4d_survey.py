"""Exact surveys of spin assignments on the boundary of a four-cube.

The boundary of the unit four-cube has 16 vertices, 32 edges, and 24 square
faces.  Every edge is incident to three faces, so this is the smallest closed
cubical complex with genuinely four-dimensional SU(2) intertwiner data.

This module keeps geometry, GF(2) surface enumeration, hyperoctahedral
symmetry, and exact Haar evaluation in one reproducible interface.  Doubled
spin labels are used throughout.  No amplitude values are inserted as lookup
tables: :func:`evaluate_assignment` builds the 24 actual plaquette holonomies
and sends them to the exact quaternion Haar integrator.

The survey separates three sharply different statements.  Every binary
surface is two-dimensional Yang--Mills.  All 7,997 highest-channel
projections of intersecting pairs have even vertex-sign parity, while the
genuine duplicate-strand pair sums the full four-valent intertwiner space
and is positive on all 100 symmetry orbits.  The unrestricted cutoff-two
fixed-face space does not stay positive: 6,704 of its 38,151 assignments are
negative.  The smallest exact witness found by total label sum is pinned in
``tests/test_hypercube4d_survey.py``.
"""

from __future__ import annotations

import itertools
from collections.abc import Iterable, Sequence
from fractions import Fraction
from importlib import import_module
from math import isqrt
from typing import Any, TypeAlias, cast

from computations.exact_haar_network import (
    P_ONE,
    GaugeFixedComplex,
    SPoly,
    brick_complex_nd,
    chi,
)

Point4: TypeAlias = tuple[int, int, int, int]
Face: TypeAlias = list[tuple[int, int]]
FaceMeta: TypeAlias = tuple[Point4, int, int]
FacePermutation: TypeAlias = list[int]
SpinAssignment: TypeAlias = tuple[int, ...]
AdmissibleEncoding: TypeAlias = tuple[int, int]
SixJDatum: TypeAlias = tuple[Fraction, int]
CoordinatePlane: TypeAlias = tuple[int, int]
TorusHomologyClass: TypeAlias = tuple[int, int]

# ``wigner_6j`` predates the repository's strict module-level typing.  The
# dynamic import keeps that legacy boundary local without weakening this
# survey's public types.
_WIGNER_6J: Any = import_module("computations.wigner_6j")


def hypercube() -> tuple[GaugeFixedComplex, list[Face], list[FaceMeta]]:
    """Construct the oriented two-skeleton of the unit four-cube.

    Face metadata is ``(basepoint, first_direction, second_direction)`` with
    the two directions increasing.  The ordering is inherited directly from
    the dimension-independent physical brick builder.
    """

    complex_, faces, raw_meta = brick_complex_nd((1, 1, 1, 1))
    meta = [
        (cast(Point4, point), first_direction, second_direction)
        for point, first_direction, second_direction in raw_meta
    ]
    if len(complex_.edges) != 32 or len(faces) != 24:
        raise AssertionError("the deterministic unit four-cube has wrong incidence")
    return complex_, faces, meta


def evaluate_assignment(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
    spins: Sequence[int],
) -> SPoly:
    """Evaluate one doubled-spin assignment by exact Haar contraction."""

    if len(spins) != len(faces):
        raise ValueError(f"one spin per face is required: expected {len(faces)}, got {len(spins)}")
    if any(spin < 0 for spin in spins):
        raise ValueError("doubled spins must be nonnegative")
    factors = [
        chi(spin, complex_.holonomy_of(face))
        for spin, face in zip(spins, faces, strict=True)
        if spin > 0
    ]
    return complex_.contract_invariant(factors or [dict(P_ONE)])


def evaluate_surface_pair(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
    left: int,
    right: int,
    *,
    label: int = 1,
) -> SPoly:
    """Evaluate two binary surfaces without fusing coincident face strands.

    A face in ``left & right`` contributes two independent ``chi_label``
    factors.  For the fundamental doubled label one, this retains the full
    four-strand projector at a crossing edge,
    ``Inv((1/2)^(tensor 4))``, rather than selecting only the highest
    spin-one face channel.
    """

    if left < 0 or right < 0 or (left | right) >> len(faces):
        raise ValueError("surface mask leaves the supplied face set")
    if label < 0:
        raise ValueError("doubled spins must be nonnegative")
    factors = [
        chi(label, complex_.holonomy_of(face))
        for mask in (left, right)
        for face_index, face in enumerate(faces)
        if (mask >> face_index) & 1
    ]
    return complex_.contract_invariant(factors or [dict(P_ONE)])


def surface_pair_fusion_expansion(
    left: int,
    right: int,
    face_count: int = 24,
) -> tuple[SpinAssignment, ...]:
    """Expand a fundamental surface pair into complete overlap-face channels.

    The SU(2) character identity ``chi_1^2 = chi_0 + chi_2`` gives one
    assignment for every subset of overlap faces: the symmetric difference
    carries doubled label one, selected overlap faces carry doubled label two,
    and the remaining overlap faces carry zero.
    """

    if left < 0 or right < 0 or (left | right) >> face_count:
        raise ValueError("surface mask leaves the requested face set")
    odd = left ^ right
    overlap_faces = [face for face in range(face_count) if ((left & right) >> face) & 1]
    assignments: list[SpinAssignment] = []
    for selection in range(1 << len(overlap_faces)):
        twos = sum(
            1 << face for index, face in enumerate(overlap_faces) if (selection >> index) & 1
        )
        assignments.append(decode_assignment((odd, twos), face_count))
    return tuple(assignments)


def binary_surface_pair_fusion_witness(
    encoding: AdmissibleEncoding,
    closed_surfaces: Sequence[int],
) -> tuple[int, int] | None:
    """Return a binary-surface pair whose fusion ledger contains ``encoding``.

    Writing the encoding as ``(odd, twos)``, a witness must satisfy

    ``left xor right = odd`` and ``twos`` contained in ``left & right``.

    The test is exact and does not enumerate overlap-channel subsets.
    """

    odd, twos = encoding
    if odd < 0 or twos < 0 or odd & twos:
        raise ValueError("fusion encodings must be disjoint nonnegative masks")
    surface_set = set(closed_surfaces)
    if any(surface < 0 for surface in surface_set):
        raise ValueError("closed-surface masks must be nonnegative")
    if odd not in surface_set:
        return None
    for left in sorted(surface_set):
        if twos & ~left:
            continue
        right = left ^ odd
        if right in surface_set and twos & ~(left & right) == 0:
            return left, right
    return None


def _edge_incidence_rows(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
) -> list[int]:
    """Return the edge-face incidence matrix as GF(2) bit rows."""

    rows: list[int] = []
    for edge_index in range(len(complex_.edges)):
        row = 0
        for face_index, face in enumerate(faces):
            if any(edge == edge_index for edge, _orientation in face):
                row |= 1 << face_index
        rows.append(row)
    return rows


def kernel_basis(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
) -> list[int]:
    """Compute a deterministic basis of closed binary face surfaces.

    The returned integers are 24-bit face masks spanning the kernel of the
    edge-face incidence map over GF(2).  Gaussian elimination is performed on
    integer bit rows, so there is no numerical linear algebra in this step.
    """

    face_count = len(faces)
    rows = _edge_incidence_rows(complex_, faces)
    pivot_rows: dict[int, int] = {}

    for initial in rows:
        row = initial
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivot_rows:
                pivot_rows[pivot] = row
                break
            row ^= pivot_rows[pivot]

    # Clear every other pivot occurrence, producing reduced rows with a
    # distinguished pivot column.
    for pivot in sorted(pivot_rows):
        pivot_row = pivot_rows[pivot]
        for other in list(pivot_rows):
            if other != pivot and ((pivot_rows[other] >> pivot) & 1):
                pivot_rows[other] ^= pivot_row

    free_columns = [column for column in range(face_count) if column not in pivot_rows]
    basis: list[int] = []
    for free in free_columns:
        vector = 1 << free
        for pivot, row in pivot_rows.items():
            if ((row >> free) & 1) != 0:
                vector |= 1 << pivot
        basis.append(vector)

    # Keep a local algebraic gate close to the construction.
    if any((row & vector).bit_count() % 2 for row in rows for vector in basis):
        raise AssertionError("GF(2) elimination returned a non-kernel vector")
    return basis


def surfaces(basis: Sequence[int]) -> list[int]:
    """Enumerate every binary surface spanned by ``basis`` exactly once."""

    out: list[int] = []
    for coefficients in range(1 << len(basis)):
        mask = 0
        for index, vector in enumerate(basis):
            if (coefficients >> index) & 1:
                mask ^= vector
        out.append(mask)
    if len(set(out)) != len(out):
        raise ValueError("the supplied vectors are not linearly independent")
    return sorted(out)


def _transform_meta(
    face: FaceMeta,
    axis_map: tuple[int, int, int, int],
    reflected: tuple[bool, bool, bool, bool],
) -> FaceMeta:
    """Apply one signed coordinate permutation to canonical face metadata."""

    point, first, second = face
    transformed_directions = {axis_map[first], axis_map[second]}
    transformed_point = [0, 0, 0, 0]
    for old_axis in range(4):
        new_axis = axis_map[old_axis]
        if new_axis in transformed_directions:
            # Reflection reverses this direction, but the underlying
            # unoriented square still has lower coordinate zero.
            transformed_point[new_axis] = 0
        else:
            transformed_point[new_axis] = (
                1 - point[old_axis] if reflected[old_axis] else point[old_axis]
            )
    direction_a, direction_b = sorted(transformed_directions)
    return (
        (
            transformed_point[0],
            transformed_point[1],
            transformed_point[2],
            transformed_point[3],
        ),
        direction_a,
        direction_b,
    )


def symmetry_maps(meta: Sequence[FaceMeta]) -> list[FacePermutation]:
    """Return all 384 hyperoctahedral permutations of the 24 faces.

    Each list maps an old face index to its transformed face index.  The
    identity is returned first; all remaining maps are ordered
    deterministically by axis permutation and reflection mask.
    """

    lookup = {face: index for index, face in enumerate(meta)}
    if len(lookup) != len(meta):
        raise ValueError("face metadata must be unique")

    maps: list[FacePermutation] = []
    for untyped_axis_map in itertools.permutations(range(4)):
        axis_map = cast(tuple[int, int, int, int], untyped_axis_map)
        for reflection_bits in range(16):
            reflected = cast(
                tuple[bool, bool, bool, bool],
                tuple(bool((reflection_bits >> axis) & 1) for axis in range(4)),
            )
            permutation = [lookup[_transform_meta(face, axis_map, reflected)] for face in meta]
            maps.append(permutation)

    identity = list(range(len(meta)))
    maps.sort(key=lambda permutation: (permutation != identity, permutation))
    if len(maps) != 384 or len({tuple(permutation) for permutation in maps}) != 384:
        raise AssertionError("hyperoctahedral face action is not faithful")
    return maps


def permute_mask(mask: int, permutation: Sequence[int]) -> int:
    """Apply an old-index-to-new-index face permutation to a bit mask."""

    if mask < 0:
        raise ValueError("face masks must be nonnegative")
    out = 0
    for old_index, new_index in enumerate(permutation):
        if (mask >> old_index) & 1:
            out |= 1 << new_index
    return out


def permute_assignment(
    spins: Sequence[int],
    permutation: Sequence[int],
) -> SpinAssignment:
    """Relabel a face-spin assignment by a symmetry permutation."""

    if len(spins) != len(permutation):
        raise ValueError("assignment and permutation lengths must agree")
    out = [0] * len(spins)
    for old_index, new_index in enumerate(permutation):
        out[new_index] = spins[old_index]
    return tuple(out)


def mask_orbits(
    masks: Iterable[int],
    maps: Sequence[FacePermutation],
) -> list[tuple[int, ...]]:
    """Partition a symmetry-stable collection of masks into exact orbits."""

    remaining = set(masks)
    orbits: list[tuple[int, ...]] = []
    while remaining:
        representative = min(remaining)
        orbit = tuple(sorted({permute_mask(representative, permutation) for permutation in maps}))
        if not set(orbit) <= remaining:
            raise ValueError("mask collection is not stable under the supplied maps")
        remaining.difference_update(orbit)
        orbits.append(orbit)
    return orbits


def surface_assignment(mask: int, face_count: int = 24, label: int = 1) -> SpinAssignment:
    """Return a uniform-label spin assignment supported on ``mask``."""

    if mask < 0:
        raise ValueError("face masks must be nonnegative")
    if face_count < 0:
        raise ValueError("face_count must be nonnegative")
    if label < 0:
        raise ValueError("label must be nonnegative")
    if mask >> face_count:
        raise ValueError("mask contains a face outside the requested complex")
    return tuple(label if (mask >> face) & 1 else 0 for face in range(face_count))


def superposed_surface_assignment(
    left: int,
    right: int,
    face_count: int = 24,
    left_label: int = 1,
    right_label: int = 1,
) -> SpinAssignment:
    """Add the labels of two closed surfaces on every common face.

    For the default labels the result lies in ``{0,1,2}``; an overlap face
    carries label two.  This is the smallest natural mixed-spin family that
    retains the parity constraint at every trivalent edge.
    """

    if left_label < 0 or right_label < 0:
        raise ValueError("surface labels must be nonnegative")
    if left < 0 or right < 0 or (left | right) >> face_count:
        raise ValueError("surface mask leaves the requested face set")
    return tuple(
        left_label * ((left >> face) & 1) + right_label * ((right >> face) & 1)
        for face in range(face_count)
    )


def pair_orbits(
    masks: Sequence[int],
    maps: Sequence[FacePermutation],
    *,
    intersecting_only: bool = False,
    distinct_only: bool = True,
) -> list[tuple[tuple[int, int], ...]]:
    """Classify unordered pairs of masks under simultaneous symmetry."""

    pairs = {
        (left, right)
        for left_index, left in enumerate(masks)
        for right in masks[left_index if not distinct_only else left_index + 1 :]
        if (not intersecting_only or (left & right) != 0)
    }
    orbits: list[tuple[tuple[int, int], ...]] = []
    while pairs:
        representative = min(pairs)
        untyped_orbit = tuple(
            sorted(
                {
                    tuple(
                        sorted(
                            (
                                permute_mask(representative[0], permutation),
                                permute_mask(representative[1], permutation),
                            )
                        )
                    )
                    for permutation in maps
                }
            )
        )
        orbit = cast(tuple[tuple[int, int], ...], untyped_orbit)
        orbit_set = set(orbit)
        if not orbit_set <= pairs:
            raise ValueError("pair collection is not stable under the supplied maps")
        pairs.difference_update(orbit_set)
        orbits.append(orbit)
    return orbits


def _edge_face_incidence(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
) -> list[tuple[int, int, int]]:
    incidence: list[tuple[int, int, int]] = []
    for edge_index in range(len(complex_.edges)):
        face_indices = tuple(
            face_index
            for face_index, face in enumerate(faces)
            if any(edge == edge_index for edge, _orientation in face)
        )
        if len(face_indices) != 3:
            raise ValueError(
                "local {0,1,2} enumeration requires trivalent edges; "
                f"edge {edge_index} has valence {len(face_indices)}"
            )
        incidence.append(face_indices)
    return incidence


def _even_label_masks(
    odd: int,
    face_count: int,
    edge_faces: Sequence[tuple[int, int, int]],
) -> list[int]:
    """Enumerate the admissible label-two masks above one fixed odd surface."""

    even_faces = [face for face in range(face_count) if ((odd >> face) & 1) == 0]
    # If an edge has two label-one faces, its remaining even face can be
    # either zero or two.  At an edge with no odd faces, the number of
    # label-two faces may be 0, 2, or 3, but not 1.
    active_constraints = [
        incident for incident in edge_faces if all(((odd >> face) & 1) == 0 for face in incident)
    ]
    constraint_indices: dict[int, list[int]] = {face: [] for face in even_faces}
    for constraint_index, incident in enumerate(active_constraints):
        for face in incident:
            constraint_indices[face].append(constraint_index)
    order = sorted(
        even_faces,
        key=lambda face: (-len(constraint_indices[face]), face),
    )
    assigned: dict[int, int] = {}
    masks: list[int] = []

    def search(position: int, twos: int) -> None:
        if position == len(order):
            masks.append(twos)
            return
        face = order[position]
        for value in (0, 1):
            assigned[face] = value
            viable = True
            for constraint_index in constraint_indices[face]:
                incident = active_constraints[constraint_index]
                assigned_values = [assigned[member] for member in incident if member in assigned]
                lower = sum(assigned_values)
                upper = lower + 3 - len(assigned_values)
                if not any(lower <= total <= upper for total in (0, 2, 3)):
                    viable = False
                    break
            if viable:
                search(
                    position + 1,
                    twos | ((1 << face) if value else 0),
                )
        assigned.pop(face)

    search(0, 0)
    return masks


def locally_admissible_assignments(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
) -> list[AdmissibleEncoding]:
    """Enumerate all locally admissible assignments with labels in ``{0,1,2}``.

    An assignment is encoded by two disjoint masks ``(odd, twos)``: faces in
    ``odd`` carry label one and faces in ``twos`` carry label two.  The odd
    mask must be a closed GF(2) surface.  Conditional on that mask, a fast
    exact constraint search enforces the triangle inequality on the remaining
    even labels.  This avoids a prohibitive scan of all ``3**24`` assignments.
    """

    edge_faces = _edge_face_incidence(complex_, faces)
    odd_surfaces = surfaces(kernel_basis(complex_, faces))
    encodings: list[AdmissibleEncoding] = []

    for odd in odd_surfaces:
        encodings.extend((odd, twos) for twos in _even_label_masks(odd, len(faces), edge_faces))

    return sorted(encodings)


def admissible_assignment_orbits(
    encodings: Iterable[AdmissibleEncoding],
    maps: Sequence[FacePermutation],
) -> list[tuple[AdmissibleEncoding, ...]]:
    """Symmetry-classify two-mask encodings of locally admissible assignments."""

    remaining = set(encodings)
    orbits: list[tuple[AdmissibleEncoding, ...]] = []
    while remaining:
        representative = min(remaining)
        orbit = tuple(
            sorted(
                {
                    (
                        permute_mask(representative[0], permutation),
                        permute_mask(representative[1], permutation),
                    )
                    for permutation in maps
                }
            )
        )
        if not set(orbit) <= remaining:
            raise ValueError("assignment collection is not stable under the supplied maps")
        remaining.difference_update(orbit)
        orbits.append(orbit)
    return orbits


def decode_assignment(
    encoding: AdmissibleEncoding,
    face_count: int = 24,
) -> SpinAssignment:
    """Decode an ``(odd, twos)`` mask pair to literal doubled-spin labels."""

    odd, twos = encoding
    if odd < 0 or twos < 0 or odd & twos or (odd | twos) >> face_count:
        raise ValueError("invalid disjoint-mask assignment encoding")
    return tuple(
        1 if (odd >> face) & 1 else 2 if (twos >> face) & 1 else 0 for face in range(face_count)
    )


def vertex_sixj_data(
    meta: Sequence[FaceMeta],
    spins: Sequence[int],
) -> tuple[SixJDatum, ...]:
    """Return exact ``(square, sign)`` data at all 16 four-cube vertices.

    At a vertex, write ``n_ij`` for the face in coordinate directions
    ``i < j``.  The standard six-j wiring is

    ``{n01 n02 n03; n23 n13 n12}``,

    whose four admissibility triangles are exactly the four trivalent edge
    triples incident to that vertex.  Doubled labels are converted to actual
    half-integer spins only at the call to :func:`sixj_squared`.
    """

    if len(spins) != len(meta):
        raise ValueError("one spin is required for every face metadata row")
    if any(spin < 0 for spin in spins):
        raise ValueError("doubled spins must be nonnegative")
    lookup = {face: index for index, face in enumerate(meta)}
    if len(lookup) != len(meta):
        raise ValueError("face metadata must be unique")

    data: list[SixJDatum] = []
    for untyped_vertex in itertools.product(range(2), repeat=4):
        vertex = cast(Point4, untyped_vertex)

        def face_label(
            first: int,
            second: int,
            vertex_: Point4 = vertex,
        ) -> int:
            base = list(vertex_)
            base[first] = 0
            base[second] = 0
            face = (
                cast(Point4, tuple(base)),
                min(first, second),
                max(first, second),
            )
            return spins[lookup[face]]

        labels = (
            face_label(0, 1),
            face_label(0, 2),
            face_label(0, 3),
            face_label(2, 3),
            face_label(1, 3),
            face_label(1, 2),
        )
        actual_spins = tuple(Fraction(label, 2) for label in labels)
        value: Any = _WIGNER_6J.sixj_squared(*actual_spins)
        data.append((Fraction(value.square), int(value.sign)))
    return tuple(data)


def vertex_sixj_signs(
    meta: Sequence[FaceMeta],
    spins: Sequence[int],
) -> tuple[int, ...]:
    """Return the exact Wigner-6j sign at each of the 16 vertices."""

    return tuple(sign for _square, sign in vertex_sixj_data(meta, spins))


def vertex_sixj_product(
    meta: Sequence[FaceMeta],
    spins: Sequence[int],
) -> Fraction:
    """Evaluate the trivalent four-cube spin network by its 16 vertex symbols.

    With normalized Haar measure and the face-character convention used by
    :func:`evaluate_assignment`, the boundary spin network is the product of
    the 16 local six-j symbols.  The individual symbols can be quadratic
    radicals; their product on the closed complex is rational.  This routine
    multiplies exact squares and signs, then verifies that the resulting
    rational square has a rational square root.
    """

    product_square = Fraction(1)
    product_sign = 1
    for square, sign in vertex_sixj_data(meta, spins):
        product_square *= square
        product_sign *= sign
    if product_sign == 0:
        return Fraction(0)
    numerator_root = isqrt(product_square.numerator)
    denominator_root = isqrt(product_square.denominator)
    if (
        numerator_root * numerator_root != product_square.numerator
        or denominator_root * denominator_root != product_square.denominator
    ):
        raise ValueError("closed vertex-sixj product did not have a rational square root")
    return product_sign * Fraction(numerator_root, denominator_root)


def surface_pair_fusion_value(
    meta: Sequence[FaceMeta],
    left: int,
    right: int,
) -> Fraction:
    """Evaluate the complete fundamental pair by summing every face channel."""

    return sum(
        (
            vertex_sixj_product(meta, spins)
            for spins in surface_pair_fusion_expansion(left, right, len(meta))
        ),
        start=Fraction(0),
    )


def intersecting_pair_sign_profile(
    left: int,
    right: int,
    meta: Sequence[FaceMeta],
) -> tuple[int, int]:
    """Count negative and zero raw vertex symbols for a surface pair."""

    signs = vertex_sixj_signs(
        meta,
        superposed_surface_assignment(left, right, len(meta)),
    )
    return signs.count(-1), signs.count(0)


def intersecting_pair_vertex_sign_census(
    masks: Sequence[int],
    meta: Sequence[FaceMeta],
) -> dict[tuple[int, int], int]:
    """Census physical vertex-6j signs over intersecting unordered pairs."""

    census: dict[tuple[int, int], int] = {}
    for left_index, left in enumerate(masks):
        for right in masks[left_index + 1 :]:
            if (left & right) == 0:
                continue
            profile = intersecting_pair_sign_profile(left, right, meta)
            census[profile] = census.get(profile, 0) + 1
    return census


def admissible_orbit_vertex_sign_census(
    orbits: Sequence[Sequence[AdmissibleEncoding]],
    meta: Sequence[FaceMeta],
) -> dict[tuple[int, int], int]:
    """Census physical vertex-6j signs over admissible assignment orbits."""

    census: dict[tuple[int, int], int] = {}
    for orbit in orbits:
        if not orbit:
            raise ValueError("assignment orbits must be nonempty")
        profile_signs = vertex_sixj_signs(meta, decode_assignment(orbit[0], len(meta)))
        profile = profile_signs.count(-1), profile_signs.count(0)
        census[profile] = census.get(profile, 0) + 1
    return census


def surface_cell_counts(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
    mask: int,
) -> tuple[int, int, int, int]:
    """Return ``(vertices, edges, faces, Euler characteristic)`` of a surface."""

    if mask < 0 or mask >> len(faces):
        raise ValueError("surface mask leaves the supplied face set")
    selected_faces = [face for index, face in enumerate(faces) if (mask >> index) & 1]
    selected_edges = {edge for face in selected_faces for edge, _orientation in face}
    selected_vertices = {vertex for edge in selected_edges for vertex in complex_.edges[edge]}
    vertex_count = len(selected_vertices)
    edge_count = len(selected_edges)
    face_count = len(selected_faces)
    return (
        vertex_count,
        edge_count,
        face_count,
        vertex_count - edge_count + face_count,
    )


def face_chain_boundary_mask(
    faces: Sequence[Face],
    face_mask: int,
) -> int:
    """Return the unoriented GF(2) edge boundary of a face chain."""

    if face_mask < 0 or face_mask >> len(faces):
        raise ValueError("face-chain mask leaves the supplied face set")
    boundary = 0
    for face_index, face in enumerate(faces):
        if (face_mask >> face_index) & 1:
            for edge, _orientation in face:
                boundary ^= 1 << edge
    return boundary


def edge_cycles_homologous_mod2(
    faces: Sequence[Face],
    surface_mask: int,
    left_cycle: int,
    right_cycle: int,
) -> bool:
    """Test whether two edge cycles differ by a face boundary in a surface."""

    if surface_mask < 0 or surface_mask >> len(faces):
        raise ValueError("surface mask leaves the supplied face set")
    if left_cycle < 0 or right_cycle < 0:
        raise ValueError("edge-chain masks must be nonnegative")
    surface_edges = 0
    face_boundaries: list[int] = []
    for face_index, face in enumerate(faces):
        if (surface_mask >> face_index) & 1:
            boundary = 0
            for edge, _orientation in face:
                surface_edges |= 1 << edge
                boundary ^= 1 << edge
            face_boundaries.append(boundary)
    if (left_cycle | right_cycle) & ~surface_edges:
        raise ValueError("edge chain leaves the supplied surface")

    pivots: dict[int, int] = {}
    for initial in face_boundaries:
        vector = initial
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = vector
                break
            vector ^= pivots[pivot]

    difference = left_cycle ^ right_cycle
    while difference:
        pivot = difference.bit_length() - 1
        if pivot not in pivots:
            return False
        difference ^= pivots[pivot]
    return True


def surface_betti_numbers_mod2(
    complex_: GaugeFixedComplex,
    faces: Sequence[Face],
    mask: int,
) -> tuple[int, int, int]:
    """Return the cellular Betti numbers over GF(2) of a face subcomplex."""

    if mask < 0 or mask >> len(faces):
        raise ValueError("surface mask leaves the supplied face set")
    selected_face_indices = [index for index in range(len(faces)) if (mask >> index) & 1]
    selected_edges = sorted(
        {edge for face_index in selected_face_indices for edge, _orientation in faces[face_index]}
    )
    selected_vertices = sorted(
        {vertex for edge in selected_edges for vertex in complex_.edges[edge]}
    )
    edge_position = {edge: position for position, edge in enumerate(selected_edges)}
    vertex_position = {vertex: position for position, vertex in enumerate(selected_vertices)}

    def gf2_rank(vectors: Iterable[int]) -> int:
        pivots: dict[int, int] = {}
        for initial in vectors:
            vector = initial
            while vector:
                pivot = vector.bit_length() - 1
                if pivot not in pivots:
                    pivots[pivot] = vector
                    break
                vector ^= pivots[pivot]
        return len(pivots)

    boundary_2_rank = gf2_rank(
        sum(1 << edge_position[edge] for edge, _orientation in faces[face_index])
        for face_index in selected_face_indices
    )
    boundary_1_rank = gf2_rank(
        (1 << vertex_position[left]) | (1 << vertex_position[right])
        for edge in selected_edges
        for left, right in (complex_.edges[edge],)
    )
    return (
        len(selected_vertices) - boundary_1_rank,
        len(selected_edges) - boundary_1_rank - boundary_2_rank,
        len(selected_face_indices) - boundary_2_rank,
    )


def coordinate_clifford_torus_mask(
    meta: Sequence[FaceMeta],
    first_plane: CoordinatePlane,
    second_plane: CoordinatePlane,
) -> int:
    """Return ``boundary(I^2_A) x boundary(I^2_B)`` as a face mask."""

    first_axes = set(first_plane)
    second_axes = set(second_plane)
    if (
        len(first_axes) != 2
        or len(second_axes) != 2
        or first_axes & second_axes
        or first_axes | second_axes != set(range(4))
    ):
        raise ValueError("the Clifford-torus factors must be complementary coordinate planes")
    return sum(
        1 << face_index
        for face_index, (_point, first_direction, second_direction) in enumerate(meta)
        if (
            (first_direction in first_axes and second_direction in second_axes)
            or (first_direction in second_axes and second_direction in first_axes)
        )
    )


def overlap_boundary_homology_class(
    face_meta: FaceMeta,
    first_plane: CoordinatePlane,
    second_plane: CoordinatePlane,
) -> TorusHomologyClass:
    """Classify an overlap-plaquette boundary in the product-torus basis.

    A plaquette parallel to ``first_plane`` bounds the cycle
    ``boundary(I^2_A) x {point}``, while one parallel to ``second_plane``
    bounds ``{point} x boundary(I^2_B)``.
    """

    # Validate the product decomposition even if the face is not one of its
    # two capping planes.
    coordinate_clifford_torus_mask((), first_plane, second_plane)
    face_plane = {face_meta[1], face_meta[2]}
    if face_plane == set(first_plane):
        return 1, 0
    if face_plane == set(second_plane):
        return 0, 1
    raise ValueError("the face is not parallel to either Clifford-torus factor")


def torus_mod2_intersection(
    left: TorusHomologyClass,
    right: TorusHomologyClass,
) -> int:
    """Return the mod-two intersection form in the product-torus basis."""

    if any(coordinate not in (0, 1) for coordinate in (*left, *right)):
        raise ValueError("torus homology coordinates must be binary")
    return (left[0] * right[1] + left[1] * right[0]) % 2


def exact_constant(value: SPoly) -> Fraction:
    """Extract the rational value of a fixed-spin amplitude."""

    if any(power != 0 for power in value):
        raise ValueError(f"fixed-spin amplitude depends on heat coordinate: {value}")
    return value.get(0, Fraction(0))
