"""BF2.1: the complete binary reflection-cut carrier on the four-cube.

The BF1.6 carrier retained two selected half states.  This module enumerates
every fundamental binary half-surface on one side of the time cut of the
unit four-cube.  A lower spatial face patch determines an even subgraph of
the cut cube.  There are

``64 patches = 32 cut signatures x 2 fillings``.

Gluing ordered pairs of fillings with a common signature is a bijection onto
the 128 closed binary surfaces.  The exact one- and two-strand reflected
Gram blocks are then read from the independently constructed Haar survey in
``hypercube4d_surface_gram``.

The executable census is the finite shadow of the general BF2.1 theorem:
the physical heat-kernel reflection form is a Gram/SOS form on the complete
boundary feature space, and exact Haar blocking acts on its positive
semidefinite cone by a completely positive map.  The proof and the precise
boundary of that statement are recorded in
``notes/bf2-1-general-reflection-positive-carrier.md``.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from typing import TypeAlias

from computations.hypercube4d_surface_gram import (
    RationalMatrix,
    build_surface_gram_survey,
)
from computations.hypercube4d_survey import FaceMeta, hypercube
from computations.intertwiner_resolved_carrier import (
    FusionPath,
    invariant_fusion_paths,
)
from computations.reflection_cut_half_surface import reflect_hypercube_mask

Point3: TypeAlias = tuple[int, int, int]
FillingWord: TypeAlias = tuple[int, ...]
RationalRectMatrix: TypeAlias = tuple[tuple[Fraction, ...], ...]


@dataclass(frozen=True, order=True)
class OrientedBinaryCutLoop:
    """One canonically oriented component of a binary cut signature."""

    vertices: tuple[Point3, ...]
    face_ids: tuple[int, ...]

    @property
    def length(self) -> int:
        return len(self.face_ids)


@dataclass(frozen=True, order=True)
class BinaryCutSignature:
    """An even subgraph of the spatial cube at the reflection cut."""

    face_mask: int
    loops: tuple[OrientedBinaryCutLoop, ...]
    active_vertices: tuple[Point3, ...]

    @property
    def edge_count(self) -> int:
        return self.face_mask.bit_count()

    @property
    def loop_lengths(self) -> tuple[int, ...]:
        return tuple(sorted(loop.length for loop in self.loops))


@dataclass(frozen=True, order=True)
class BinaryHalfSurfaceState:
    """A lower spatial filling with its exposed cut signature."""

    signature_mask: int
    lower_patch_mask: int
    filling_bit: int


@dataclass(frozen=True, order=True)
class BinaryCutVertexLeg:
    """One oriented, strand-resolved fundamental leg at the cut."""

    strand_index: int
    face_id: int
    orientation: int
    label: int = 1


@dataclass(frozen=True, order=True)
class BinaryCutVertexBasis:
    """The complete canonical invariant basis at one cut vertex."""

    vertex: Point3
    legs: tuple[BinaryCutVertexLeg, ...]
    fusion_paths: tuple[FusionPath, ...]

    @property
    def dimension(self) -> int:
        return len(self.fusion_paths)


@dataclass(frozen=True)
class BinaryReflectionCutCarrier:
    """Complete fundamental half-surface carrier for the unit four-cube."""

    lower_face_ids: tuple[int, ...]
    temporal_face_ids: tuple[int, ...]
    lower_cube_boundary_mask: int
    signatures: tuple[BinaryCutSignature, ...]
    states_by_signature: tuple[tuple[BinaryHalfSurfaceState, ...], ...]

    @property
    def states(self) -> tuple[BinaryHalfSurfaceState, ...]:
        return tuple(state for block in self.states_by_signature for state in block)

    def signature(self, face_mask: int) -> BinaryCutSignature:
        for signature in self.signatures:
            if signature.face_mask == face_mask:
                return signature
        raise KeyError(f"unknown binary cut signature {face_mask:#x}")

    def state_block(self, face_mask: int) -> tuple[BinaryHalfSurfaceState, ...]:
        for signature, states in zip(
            self.signatures,
            self.states_by_signature,
            strict=True,
        ):
            if signature.face_mask == face_mask:
                return states
        raise KeyError(f"unknown binary cut signature {face_mask:#x}")


def _cut_face_endpoints(metadata: FaceMeta) -> tuple[Point3, Point3]:
    point, direction, second = metadata
    if second != 3:
        raise ValueError("only temporal faces meet the time-reflection cut")
    start = point[:3]
    end = list(start)
    end[direction] += 1
    return start, (end[0], end[1], end[2])


def _walk_cut_component(
    start: Point3,
    first_face: int,
    endpoints: dict[int, tuple[Point3, Point3]],
    adjacency: dict[Point3, list[int]],
) -> OrientedBinaryCutLoop:
    vertices = [start]
    face_ids: list[int] = []
    current = start
    face_id = first_face
    while True:
        left, right = endpoints[face_id]
        following = right if current == left else left
        face_ids.append(face_id)
        if following == start:
            break
        vertices.append(following)
        candidates = [candidate for candidate in adjacency[following] if candidate != face_id]
        if len(candidates) != 1:
            raise AssertionError("a binary cut component ceased to be a simple cycle")
        current = following
        face_id = candidates[0]
    return OrientedBinaryCutLoop(tuple(vertices), tuple(face_ids))


def _canonical_cut_loops(
    face_mask: int,
    metadata: tuple[FaceMeta, ...],
) -> tuple[OrientedBinaryCutLoop, ...]:
    endpoints = {
        face_id: _cut_face_endpoints(row)
        for face_id, row in enumerate(metadata)
        if (face_mask >> face_id) & 1
    }
    adjacency: dict[Point3, list[int]] = defaultdict(list)
    for face_id, (left, right) in endpoints.items():
        adjacency[left].append(face_id)
        adjacency[right].append(face_id)
    if any(len(faces) != 2 for faces in adjacency.values()):
        raise AssertionError("a lower face boundary must be an even cut subgraph")

    unused = set(endpoints)
    loops: list[OrientedBinaryCutLoop] = []
    while unused:
        seed_face = min(unused)
        component_faces: set[int] = set()
        component_vertices: set[Point3] = set()
        frontier = [endpoints[seed_face][0]]
        while frontier:
            vertex = frontier.pop()
            if vertex in component_vertices:
                continue
            component_vertices.add(vertex)
            for face_id in adjacency[vertex]:
                component_faces.add(face_id)
                left, right = endpoints[face_id]
                frontier.append(right if vertex == left else left)
        start = min(component_vertices)
        candidates = tuple(
            _walk_cut_component(start, face_id, endpoints, adjacency)
            for face_id in sorted(adjacency[start])
        )
        loops.append(min(candidates))
        unused.difference_update(component_faces)
    return tuple(sorted(loops))


def _lower_boundary_signature(
    patch_mask: int,
    faces: Sequence[Sequence[tuple[int, int]]],
    lower_face_ids: tuple[int, ...],
    edge_to_temporal_face: dict[int, int],
) -> int:
    signature = 0
    for edge, temporal_face in edge_to_temporal_face.items():
        incident = sum(
            any(face_edge == edge for face_edge, _orientation in faces[face_id])
            for face_id in lower_face_ids
            if (patch_mask >> face_id) & 1
        )
        if incident % 2:
            signature |= 1 << temporal_face
    return signature


@cache
def binary_reflection_cut_carrier() -> BinaryReflectionCutCarrier:
    """Enumerate all fundamental half-surfaces at the unit four-cube cut."""

    _complex, raw_faces, raw_metadata = hypercube()
    faces = tuple(tuple(face) for face in raw_faces)
    metadata = tuple(raw_metadata)
    lower_face_ids = tuple(
        face_id
        for face_id, (point, _first, second) in enumerate(metadata)
        if second < 3 and point[3] == 0
    )
    temporal_face_ids = tuple(
        face_id
        for face_id, (_point, _first, second) in enumerate(metadata)
        if second == 3
    )
    edge_to_temporal_face = {
        faces[face_id][0][0]: face_id for face_id in temporal_face_ids
    }
    if len(edge_to_temporal_face) != 12:
        raise AssertionError("the cut cube must have twelve spatial edges")

    patches_by_signature: dict[int, list[int]] = defaultdict(list)
    for choice in range(1 << len(lower_face_ids)):
        patch = sum(
            1 << face_id
            for position, face_id in enumerate(lower_face_ids)
            if (choice >> position) & 1
        )
        signature = _lower_boundary_signature(
            patch,
            faces,
            lower_face_ids,
            edge_to_temporal_face,
        )
        patches_by_signature[signature].append(patch)

    signatures: list[BinaryCutSignature] = []
    state_blocks: list[tuple[BinaryHalfSurfaceState, ...]] = []
    for signature_mask, raw_patches in sorted(patches_by_signature.items()):
        patches = tuple(sorted(raw_patches))
        loops = _canonical_cut_loops(signature_mask, metadata)
        active_vertices = tuple(
            sorted({vertex for loop in loops for vertex in loop.vertices})
        )
        signatures.append(
            BinaryCutSignature(
                signature_mask,
                loops,
                active_vertices,
            )
        )
        state_blocks.append(
            tuple(
                BinaryHalfSurfaceState(signature_mask, patch, filling_bit)
                for filling_bit, patch in enumerate(patches)
            )
        )

    return BinaryReflectionCutCarrier(
        lower_face_ids,
        temporal_face_ids,
        sum(1 << face_id for face_id in lower_face_ids),
        tuple(signatures),
        tuple(state_blocks),
    )


def glue_binary_half_states(
    lower: BinaryHalfSurfaceState,
    reflected: BinaryHalfSurfaceState,
) -> int:
    """Glue two states across their common cut into one closed surface."""

    if lower.signature_mask != reflected.signature_mask:
        raise ValueError("half-surfaces can only be glued within one boundary block")
    return (
        lower.lower_patch_mask
        | lower.signature_mask
        | reflect_hypercube_mask(reflected.lower_patch_mask)
    )


@cache
def binary_cut_vertex_bases(
    signature_masks: tuple[int, ...],
) -> tuple[BinaryCutVertexBasis, ...]:
    """Resolve every bivalent or four-valent cut packet into fusion paths."""

    _complex, _faces, raw_metadata = hypercube()
    metadata = tuple(raw_metadata)
    incident: dict[Point3, list[BinaryCutVertexLeg]] = defaultdict(list)
    for strand_index, signature_mask in enumerate(signature_masks):
        if signature_mask < 0 or signature_mask >> len(metadata):
            raise ValueError("cut signature leaves the unit four-cube")
        for face_id, row in enumerate(metadata):
            if not ((signature_mask >> face_id) & 1):
                continue
            start, end = _cut_face_endpoints(row)
            incident[start].append(BinaryCutVertexLeg(strand_index, face_id, 1))
            incident[end].append(BinaryCutVertexLeg(strand_index, face_id, -1))

    bases: list[BinaryCutVertexBasis] = []
    for vertex, raw_legs in sorted(incident.items()):
        legs = tuple(sorted(raw_legs))
        if len(legs) not in (2, 4):
            raise AssertionError("one- and two-strand cuts must be bivalent or four-valent")
        paths = invariant_fusion_paths(tuple(leg.label for leg in legs))
        bases.append(BinaryCutVertexBasis(vertex, legs, paths))
    return tuple(bases)


@dataclass(frozen=True)
class ExactLDLT:
    """An exact, zero-pivot-safe ``L D L^T`` certificate."""

    lower: RationalMatrix
    diagonal: tuple[Fraction, ...]

    @property
    def rank(self) -> int:
        return sum(value != 0 for value in self.diagonal)

    @property
    def is_psd(self) -> bool:
        return all(value >= 0 for value in self.diagonal)

    def reconstructs(self, matrix: RationalMatrix) -> bool:
        size = len(matrix)
        if len(self.lower) != size or any(len(row) != size for row in matrix):
            return False
        reconstructed = tuple(
            tuple(
                sum(
                    (
                        self.lower[row][pivot]
                        * self.diagonal[pivot]
                        * self.lower[column][pivot]
                        for pivot in range(size)
                    ),
                    start=Fraction(0),
                )
                for column in range(size)
            )
            for row in range(size)
        )
        return reconstructed == matrix


def exact_ldlt(matrix: RationalMatrix) -> ExactLDLT:
    """Factor a symmetric rational matrix without dividing by zero pivots.

    For a positive-semidefinite matrix, a zero residual pivot forces the
    remaining residual row to vanish.  The function checks that condition
    exactly and therefore needs no floating-point tolerance.
    """

    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("LDLT requires a square matrix")
    if any(
        matrix[row][column] != matrix[column][row]
        for row in range(size)
        for column in range(size)
    ):
        raise ValueError("LDLT requires a symmetric matrix")

    lower = [
        [Fraction(int(row == column)) for column in range(size)]
        for row in range(size)
    ]
    diagonal: list[Fraction] = []
    for pivot in range(size):
        residual_pivot = matrix[pivot][pivot] - sum(
            (
                lower[pivot][prior] ** 2 * diagonal[prior]
                for prior in range(pivot)
            ),
            start=Fraction(0),
        )
        diagonal.append(residual_pivot)
        for row in range(pivot + 1, size):
            residual = matrix[row][pivot] - sum(
                (
                    lower[row][prior]
                    * lower[pivot][prior]
                    * diagonal[prior]
                    for prior in range(pivot)
                ),
                start=Fraction(0),
            )
            if residual_pivot:
                lower[row][pivot] = residual / residual_pivot
            elif residual:
                raise ArithmeticError(
                    "zero LDLT pivot has a nonzero residual row; permutation required"
                )
    return ExactLDLT(
        tuple(tuple(row) for row in lower),
        tuple(diagonal),
    )


@dataclass(frozen=True)
class BinaryReflectedGramBlock:
    """One boundary-signature block with its exact SOS factorization."""

    signature_masks: tuple[int, ...]
    filling_words: tuple[FillingWord, ...]
    cut_vertex_bases: tuple[BinaryCutVertexBasis, ...]
    matrix: RationalMatrix
    ldlt: ExactLDLT

    def validates(self) -> bool:
        return (
            self.ldlt.reconstructs(self.matrix)
            and self.ldlt.is_psd
            and len(self.matrix) == 2 ** len(self.signature_masks)
            and all(basis.dimension in (1, 2) for basis in self.cut_vertex_bases)
        )


def _surface_matrix_value(
    surface_index: dict[int, int],
    matrix: RationalMatrix,
    left: int,
    right: int,
) -> Fraction:
    return matrix[surface_index[left]][surface_index[right]]


@cache
def binary_reflected_gram_blocks() -> tuple[
    tuple[BinaryReflectedGramBlock, ...],
    tuple[BinaryReflectedGramBlock, ...],
]:
    """Build every one- and two-strand binary reflection block exactly."""

    carrier = binary_reflection_cut_carrier()
    survey = build_surface_gram_survey()
    surface_index = {
        mask: index for index, mask in enumerate(survey.surface_masks)
    }
    vacuum = surface_index[0]

    single_blocks: list[BinaryReflectedGramBlock] = []
    for signature, states in zip(
        carrier.signatures,
        carrier.states_by_signature,
        strict=True,
    ):
        matrix = tuple(
            tuple(
                survey.matrix[vacuum][
                    surface_index[glue_binary_half_states(left, right)]
                ]
                for right in states
            )
            for left in states
        )
        single_blocks.append(
            BinaryReflectedGramBlock(
                (signature.face_mask,),
                ((0,), (1,)),
                binary_cut_vertex_bases((signature.face_mask,)),
                matrix,
                exact_ldlt(matrix),
            )
        )

    double_blocks: list[BinaryReflectedGramBlock] = []
    for left_position, left_signature in enumerate(carrier.signatures):
        left_states = carrier.states_by_signature[left_position]
        for right_position in range(left_position, len(carrier.signatures)):
            right_signature = carrier.signatures[right_position]
            right_states = carrier.states_by_signature[right_position]
            filling_words = tuple(
                (left.filling_bit, right.filling_bit)
                for left in left_states
                for right in right_states
            )
            state_lookup = {
                (left.filling_bit, right.filling_bit): (left, right)
                for left in left_states
                for right in right_states
            }
            rows: list[tuple[Fraction, ...]] = []
            for lower_word in filling_words:
                lower_pair = state_lookup[lower_word]
                row: list[Fraction] = []
                for reflected_word in filling_words:
                    reflected_pair = state_lookup[reflected_word]
                    first_surface = glue_binary_half_states(
                        lower_pair[0],
                        reflected_pair[0],
                    )
                    second_surface = glue_binary_half_states(
                        lower_pair[1],
                        reflected_pair[1],
                    )
                    row.append(
                        _surface_matrix_value(
                            surface_index,
                            survey.matrix,
                            first_surface,
                            second_surface,
                        )
                    )
                rows.append(tuple(row))
            matrix = tuple(rows)
            double_blocks.append(
                BinaryReflectedGramBlock(
                    (left_signature.face_mask, right_signature.face_mask),
                    filling_words,
                    binary_cut_vertex_bases(
                        (left_signature.face_mask, right_signature.face_mask)
                    ),
                    matrix,
                    exact_ldlt(matrix),
                )
            )
    return tuple(single_blocks), tuple(double_blocks)


@dataclass(frozen=True)
class BinaryReflectionCarrierCensus:
    """Pinned exhaustive census supporting the BF2.1 enlarged cone."""

    cut_signature_count: int
    half_state_count: int
    closed_surface_count: int
    gluing_is_bijective: bool
    signature_edge_count_census: tuple[tuple[int, int], ...]
    signature_loop_length_census: tuple[tuple[tuple[int, ...], int], ...]
    fillings_per_signature_census: tuple[tuple[int, int], ...]
    single_block_count: int
    single_rank_census: tuple[tuple[int, int], ...]
    two_strand_block_count: int
    two_strand_rank_census: tuple[tuple[int, int], ...]
    two_strand_invariant_dimension_census: tuple[tuple[int, int], ...]
    distinct_two_strand_matrices: int
    negative_block_count: int
    minimum_positive_pivot: Fraction

    def validates(self) -> bool:
        return (
            self.cut_signature_count == 32
            and self.half_state_count == 64
            and self.closed_surface_count == 128
            and self.gluing_is_bijective
            and self.signature_edge_count_census == ((0, 1), (4, 6), (6, 16), (8, 9))
            and self.signature_loop_length_census
            == (
                ((), 1),
                ((4,), 6),
                ((4, 4), 3),
                ((6,), 16),
                ((8,), 6),
            )
            and self.fillings_per_signature_census == ((2, 32),)
            and self.single_block_count == 32
            and self.single_rank_census == ((1, 32),)
            and self.two_strand_block_count == 528
            and self.two_strand_rank_census
            == ((1, 35), (2, 271), (3, 165), (4, 57))
            and self.two_strand_invariant_dimension_census
            == (
                (1, 35),
                (4, 36),
                (8, 48),
                (16, 156),
                (32, 48),
                (64, 160),
                (256, 45),
            )
            and self.distinct_two_strand_matrices == 124
            and self.negative_block_count == 0
            and self.minimum_positive_pivot == Fraction(25, 726073632)
        )


@cache
def binary_reflection_carrier_census() -> BinaryReflectionCarrierCensus:
    carrier = binary_reflection_cut_carrier()
    single_blocks, double_blocks = binary_reflected_gram_blocks()
    glued = tuple(
        glue_binary_half_states(lower, reflected)
        for states in carrier.states_by_signature
        for lower in states
        for reflected in states
    )
    survey = build_surface_gram_survey()

    invariant_dimensions: Counter[int] = Counter()
    for left_position, left in enumerate(carrier.signatures):
        left_vertices = set(left.active_vertices)
        for right in carrier.signatures[left_position:]:
            common_vertices = left_vertices & set(right.active_vertices)
            # Each common vertex carries four fundamental legs and hence
            # dim Inv(V_1^tensor4)=2.  Other active vertices are bivalent.
            invariant_dimensions[2 ** len(common_vertices)] += 1

    all_blocks = single_blocks + double_blocks
    positive_pivots = tuple(
        pivot
        for block in all_blocks
        for pivot in block.ldlt.diagonal
        if pivot > 0
    )
    return BinaryReflectionCarrierCensus(
        cut_signature_count=len(carrier.signatures),
        half_state_count=len(carrier.states),
        closed_surface_count=len(survey.surface_masks),
        gluing_is_bijective=(
            len(glued) == len(set(glued)) == len(survey.surface_masks)
            and set(glued) == set(survey.surface_masks)
        ),
        signature_edge_count_census=tuple(
            sorted(Counter(signature.edge_count for signature in carrier.signatures).items())
        ),
        signature_loop_length_census=tuple(
            sorted(Counter(signature.loop_lengths for signature in carrier.signatures).items())
        ),
        fillings_per_signature_census=tuple(
            sorted(Counter(len(states) for states in carrier.states_by_signature).items())
        ),
        single_block_count=len(single_blocks),
        single_rank_census=tuple(
            sorted(Counter(block.ldlt.rank for block in single_blocks).items())
        ),
        two_strand_block_count=len(double_blocks),
        two_strand_rank_census=tuple(
            sorted(Counter(block.ldlt.rank for block in double_blocks).items())
        ),
        two_strand_invariant_dimension_census=tuple(
            sorted(invariant_dimensions.items())
        ),
        distinct_two_strand_matrices=len({block.matrix for block in double_blocks}),
        negative_block_count=sum(not block.ldlt.is_psd for block in all_blocks),
        minimum_positive_pivot=min(positive_pivots),
    )


def diagonal_congruence(
    matrix: RationalMatrix,
    weights: Sequence[Fraction],
) -> RationalMatrix:
    """Apply a positive physical half-weight by exact Gram congruence."""

    if len(matrix) != len(weights) or any(len(row) != len(weights) for row in matrix):
        raise ValueError("one congruence weight is required per matrix row")
    if any(weight < 0 for weight in weights):
        raise ValueError("reflection-half weights must be nonnegative")
    return tuple(
        tuple(
            weights[row] * matrix[row][column] * weights[column]
            for column in range(len(weights))
        )
        for row in range(len(weights))
    )


def rational_quadratic_form(
    matrix: RationalMatrix,
    vector: Sequence[Fraction],
) -> Fraction:
    """Evaluate ``vector^T matrix vector`` exactly."""

    if len(matrix) != len(vector) or any(len(row) != len(vector) for row in matrix):
        raise ValueError("quadratic-form dimensions do not agree")
    return sum(
        (
            vector[row] * matrix[row][column] * vector[column]
            for row in range(len(vector))
            for column in range(len(vector))
        ),
        start=Fraction(0),
    )


def kraus_pushforward(
    matrix: RationalMatrix,
    kraus_operators: Sequence[RationalRectMatrix],
) -> RationalMatrix:
    """Return the exact completely positive image ``sum K A K^T``."""

    fine_size = len(matrix)
    if any(len(row) != fine_size for row in matrix):
        raise ValueError("the fine boundary kernel must be square")
    if not kraus_operators:
        raise ValueError("at least one Kraus operator is required")
    coarse_size = len(kraus_operators[0])
    if any(
        len(operator) != coarse_size
        or any(len(row) != fine_size for row in operator)
        for operator in kraus_operators
    ):
        raise ValueError("Kraus operators must have common coarse and fine dimensions")
    return tuple(
        tuple(
            sum(
                (
                    operator[row][fine_row]
                    * matrix[fine_row][fine_column]
                    * operator[column][fine_column]
                    for operator in kraus_operators
                    for fine_row in range(fine_size)
                    for fine_column in range(fine_size)
                ),
                start=Fraction(0),
            )
            for column in range(coarse_size)
        )
        for row in range(coarse_size)
    )


@dataclass(frozen=True)
class BF21Certificate:
    """Finite exact evidence and the selected general-carrier exit route."""

    binary_census: BinaryReflectionCarrierCensus
    heat_kernel_sos_carrier: str
    block_map_order: str
    finite_cutoff_rule: str
    entrywise_dp_status: str
    next_gate: str

    @property
    def exit_kind(self) -> str:
        return "general-reflected-gram-psd-cone"

    def validates(self) -> bool:
        return (
            self.binary_census.validates()
            and self.heat_kernel_sos_carrier == "positive-semidefinite-boundary-kernels"
            and self.block_map_order == "completely-positive-kraus-pushforward"
            and self.finite_cutoff_rule == "compress-do-not-truncate-physical-measure"
            and self.entrywise_dp_status == "open"
            and self.next_gate == "BF3.1-whole-corrected-slab-kraus-kernel"
        )


@cache
def bf21_certificate() -> BF21Certificate:
    return BF21Certificate(
        binary_census=binary_reflection_carrier_census(),
        heat_kernel_sos_carrier="positive-semidefinite-boundary-kernels",
        block_map_order="completely-positive-kraus-pushforward",
        finite_cutoff_rule="compress-do-not-truncate-physical-measure",
        entrywise_dp_status="open",
        next_gate="BF3.1-whole-corrected-slab-kraus-kernel",
    )
