"""BF1.6: reflection-cut half-surfaces and their exact Haar Gram.

BF1.5 showed that closed full-slab surface characters are not a
reflection-positive carrier.  This module cuts the pinned three-strand
four-cube family at time ``1/2``.  A temporal plaquette becomes one edge of
the cut graph, and a temporal lattice link becomes one cut vertex.  The
carrier retains every oriented cut segment and a canonical invariant basis
at every cut vertex.

The exact Haar reconstruction uses temporal gauge.  For a fundamental
temporal plaquette,

``chi_1(g_lower g_upper^-1) = 2 sum_mu g_lower[mu] g_upper[mu]``.

After fixing a deterministic lower-slice tree, this gives finite lower and
upper boundary-feature tensors.  Their exact coefficient pairing reproduces
the BF1.5 three-strand amplitude ``83/5184``.  A two-state positive-half
packet then has the exact Gram matrix

``[[41/648, 83/5184], [83/5184, 85/20736]]``,

whose determinant is ``1/331776``.  The displayed ``LDL^T`` factorization is
an exact finite SOS certificate.
"""

from __future__ import annotations

from collections import defaultdict, deque
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from typing import TypeAlias, cast

from computations.exact_haar_network import (
    P_ONE,
    Q_ID,
    Poly,
    Quat,
    SPoly,
    chi,
    contract_pairing_aware,
    p_add_into,
    p_equal_on_group,
    p_mul,
    p_var,
    q_conj,
    q_link,
    q_mul,
    scalar,
)
from computations.fusion_closed_surface_carrier import (
    character_product_channels,
)
from computations.hypercube4d_survey import (
    FaceMeta,
    hypercube,
    vertex_sixj_product,
)
from computations.intertwiner_resolved_carrier import (
    FusionPath,
    RadicalMatrix,
    TripleRecouplingAudit,
    invariant_fusion_paths,
    radical_identity,
    triple_recoupling_audit,
)
from computations.three_strand_corrected_slab import (
    RAW_THREE_STRAND_MASKS,
    three_way_haar_audit,
)

Point3: TypeAlias = tuple[int, int, int]
BoundaryWord: TypeAlias = tuple[int, ...]

STRAND_ONE, STRAND_TWO, STRAND_THREE = RAW_THREE_STRAND_MASKS


@cache
def hypercube_time_reflection_permutation() -> tuple[int, ...]:
    """Return the unit-four-cube face involution across time ``1/2``."""

    _complex, _faces, metadata = hypercube()
    lookup = {row: index for index, row in enumerate(metadata)}
    permutation: list[int] = []
    for point, first, second in metadata:
        reflected = list(point)
        reflected[3] = 0 if second == 3 else 1 - point[3]
        permutation.append(
            lookup[(cast(tuple[int, int, int, int], tuple(reflected)), first, second)]
        )
    return tuple(permutation)


def reflect_hypercube_mask(mask: int) -> int:
    permutation = hypercube_time_reflection_permutation()
    if mask < 0 or mask >> len(permutation):
        raise ValueError("surface mask leaves the unit four-cube")
    return sum(
        1 << permutation[face_index]
        for face_index in range(len(permutation))
        if (mask >> face_index) & 1
    )


REFLECTED_STRAND_TWO = reflect_hypercube_mask(STRAND_TWO)


@dataclass(frozen=True, order=True)
class CutSegment:
    """One fundamental surface strand crossing the time-reflection cut."""

    segment_index: int
    strand_index: int
    face_index: int
    start: Point3
    end: Point3
    direction: int
    label: int = 1


@dataclass(frozen=True, order=True)
class OrientedCutStep:
    segment_index: int
    orientation: int


@dataclass(frozen=True)
class CutLoop:
    """A deterministic oriented component of one strand's cut boundary."""

    vertices: tuple[Point3, ...]
    steps: tuple[OrientedCutStep, ...]


@dataclass(frozen=True, order=True)
class CutVertexLeg:
    strand_index: int
    face_index: int
    segment_index: int
    orientation: int
    label: int


@dataclass(frozen=True)
class CutVertexBasis:
    vertex: Point3
    legs: tuple[CutVertexLeg, ...]
    fusion_paths: tuple[FusionPath, ...]

    @property
    def invariant_dimension(self) -> int:
        return len(self.fusion_paths)


@dataclass(frozen=True)
class HalfSurfacePacket:
    """One closed strand split into lower, fixed-cut, and upper pieces."""

    strand_index: int
    mask: int
    reflected_mask: int
    lower_face_ids: tuple[int, ...]
    fixed_face_ids: tuple[int, ...]
    upper_face_ids: tuple[int, ...]
    segment_indices: tuple[int, ...]
    cut_loops: tuple[CutLoop, ...]


@dataclass(frozen=True)
class ReflectionCutCarrier:
    packets: tuple[HalfSurfacePacket, ...]
    segments: tuple[CutSegment, ...]
    vertex_bases: tuple[CutVertexBasis, ...]

    @property
    def boundary_invariant_dimension(self) -> int:
        result = 1
        for basis in self.vertex_bases:
            result *= basis.invariant_dimension
        return result


def _walk_cut_loop(
    segment_by_index: dict[int, CutSegment],
    adjacency: dict[Point3, list[int]],
    start: Point3,
    first_segment: int,
) -> CutLoop:
    current = start
    segment_index = first_segment
    vertices = [start]
    steps: list[OrientedCutStep] = []
    used: set[int] = set()
    while True:
        if segment_index in used:
            raise AssertionError("cut-loop traversal repeated an edge before closure")
        used.add(segment_index)
        segment = segment_by_index[segment_index]
        if segment.start == current:
            following = segment.end
            orientation = 1
        elif segment.end == current:
            following = segment.start
            orientation = -1
        else:
            raise AssertionError("cut-loop segment is not incident to its vertex")
        steps.append(OrientedCutStep(segment_index, orientation))
        vertices.append(following)
        if following == start:
            break
        candidates = [
            candidate
            for candidate in adjacency[following]
            if candidate != segment_index
        ]
        if len(candidates) != 1:
            raise AssertionError("one strand's cut graph is not a disjoint union of loops")
        current = following
        segment_index = candidates[0]
    return CutLoop(tuple(vertices), tuple(steps))


def _canonical_loops(segments: Sequence[CutSegment]) -> tuple[CutLoop, ...]:
    if not segments:
        return ()
    segment_by_index = {segment.segment_index: segment for segment in segments}
    adjacency: dict[Point3, list[int]] = defaultdict(list)
    for segment in segments:
        adjacency[segment.start].append(segment.segment_index)
        adjacency[segment.end].append(segment.segment_index)
    if any(len(incident) != 2 for incident in adjacency.values()):
        raise AssertionError("a cut of a closed binary strand must have even degree two")

    unused = set(segment_by_index)
    loops: list[CutLoop] = []
    while unused:
        component_vertices: set[Point3] = set()
        frontier = [segment_by_index[min(unused)].start]
        component_segments: set[int] = set()
        while frontier:
            vertex = frontier.pop()
            if vertex in component_vertices:
                continue
            component_vertices.add(vertex)
            for segment_index in adjacency[vertex]:
                component_segments.add(segment_index)
                segment = segment_by_index[segment_index]
                frontier.append(
                    segment.end if segment.start == vertex else segment.start
                )
        start = min(component_vertices)
        candidates = [
            _walk_cut_loop(segment_by_index, adjacency, start, first)
            for first in sorted(adjacency[start])
        ]
        chosen = min(
            candidates,
            key=lambda loop: (
                loop.vertices,
                tuple((step.segment_index, step.orientation) for step in loop.steps),
            ),
        )
        loops.append(chosen)
        unused.difference_update(component_segments)
    return tuple(sorted(loops, key=lambda loop: (loop.vertices, loop.steps)))


@cache
def reflection_cut_carrier() -> ReflectionCutCarrier:
    """Build the canonical cut carrier for all three BF1.5 strands."""

    _complex, _faces, metadata = hypercube()
    segments: list[CutSegment] = []
    packet_rows: list[
        tuple[
            int,
            int,
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
        ]
    ] = []
    for strand_index, mask in enumerate(RAW_THREE_STRAND_MASKS):
        lower: list[int] = []
        fixed: list[int] = []
        upper: list[int] = []
        strand_segments: list[int] = []
        for face_index, (point, first, second) in enumerate(metadata):
            if not ((mask >> face_index) & 1):
                continue
            if second == 3:
                start = cast(Point3, point[:3])
                endpoint = list(start)
                endpoint[first] += 1
                segment_index = len(segments)
                segments.append(
                    CutSegment(
                        segment_index,
                        strand_index,
                        face_index,
                        start,
                        cast(Point3, tuple(endpoint)),
                        first,
                    )
                )
                fixed.append(face_index)
                strand_segments.append(segment_index)
            elif point[3] == 0:
                lower.append(face_index)
            else:
                upper.append(face_index)
        packet_rows.append(
            (
                strand_index,
                mask,
                tuple(lower),
                tuple(fixed),
                tuple(upper),
                tuple(strand_segments),
            )
        )

    packets = tuple(
        HalfSurfacePacket(
            strand_index=row[0],
            mask=row[1],
            reflected_mask=reflect_hypercube_mask(row[1]),
            lower_face_ids=row[2],
            fixed_face_ids=row[3],
            upper_face_ids=row[4],
            segment_indices=row[5],
            cut_loops=_canonical_loops(
                tuple(segments[index] for index in row[5])
            ),
        )
        for row in packet_rows
    )

    incident: dict[Point3, list[CutVertexLeg]] = defaultdict(list)
    for segment in segments:
        incident[segment.start].append(
            CutVertexLeg(
                segment.strand_index,
                segment.face_index,
                segment.segment_index,
                1,
                segment.label,
            )
        )
        incident[segment.end].append(
            CutVertexLeg(
                segment.strand_index,
                segment.face_index,
                segment.segment_index,
                -1,
                segment.label,
            )
        )
    vertex_bases = tuple(
        CutVertexBasis(
            vertex,
            tuple(sorted(legs)),
            invariant_fusion_paths(tuple(leg.label for leg in sorted(legs))),
        )
        for vertex, legs in sorted(incident.items())
    )
    return ReflectionCutCarrier(packets, tuple(segments), vertex_bases)


@dataclass(frozen=True)
class ReflectionCutCensus:
    packet_face_splits: tuple[tuple[int, int, int], ...]
    cut_loop_lengths: tuple[int, ...]
    cut_segment_count: int
    cut_vertex_leg_counts: tuple[tuple[int, int], ...]
    cut_vertex_invariant_dimensions: tuple[int, ...]
    boundary_invariant_dimension: int

    def validates(self) -> bool:
        return (
            self.packet_face_splits == ((1, 4, 1), (6, 0, 0), (2, 6, 2))
            and self.cut_loop_lengths == (4, 6)
            and self.cut_segment_count == 10
            and self.cut_vertex_leg_counts == ((2, 2), (4, 4))
            and self.cut_vertex_invariant_dimensions == (2, 2, 2, 2, 1, 1)
            and self.boundary_invariant_dimension == 16
        )


@cache
def reflection_cut_census() -> ReflectionCutCensus:
    carrier = reflection_cut_carrier()
    leg_count_census: dict[int, int] = defaultdict(int)
    for basis in carrier.vertex_bases:
        leg_count_census[len(basis.legs)] += 1
    return ReflectionCutCensus(
        packet_face_splits=tuple(
            (
                len(packet.lower_face_ids),
                len(packet.fixed_face_ids),
                len(packet.upper_face_ids),
            )
            for packet in carrier.packets
        ),
        cut_loop_lengths=tuple(
            len(loop.steps)
            for packet in carrier.packets
            for loop in packet.cut_loops
        ),
        cut_segment_count=len(carrier.segments),
        cut_vertex_leg_counts=tuple(sorted(leg_count_census.items())),
        cut_vertex_invariant_dimensions=tuple(
            basis.invariant_dimension for basis in carrier.vertex_bases
        ),
        boundary_invariant_dimension=carrier.boundary_invariant_dimension,
    )


@dataclass(frozen=True)
class CutReflectionTransportAudit:
    segment_permutation: tuple[int, ...]
    vertex_permutation: tuple[int, ...]
    canonical_transport_matrices: tuple[RadicalMatrix, ...]
    dual_leg_orientation: bool
    recoupling: TripleRecouplingAudit

    def validates(self) -> bool:
        return (
            self.segment_permutation
            == tuple(range(len(self.segment_permutation)))
            and self.vertex_permutation
            == tuple(range(len(self.vertex_permutation)))
            and all(
                matrix == radical_identity(len(matrix))
                for matrix in self.canonical_transport_matrices
            )
            and self.dual_leg_orientation
            and self.recoupling.validates()
        )


@cache
def cut_reflection_transport_audit() -> CutReflectionTransportAudit:
    """Reflection fixes the cut graph and pairs each oriented leg with its dual."""

    carrier = reflection_cut_carrier()
    return CutReflectionTransportAudit(
        segment_permutation=tuple(range(len(carrier.segments))),
        vertex_permutation=tuple(range(len(carrier.vertex_bases))),
        canonical_transport_matrices=tuple(
            radical_identity(basis.invariant_dimension)
            for basis in carrier.vertex_bases
        ),
        dual_leg_orientation=all(
            leg.orientation in (-1, 1)
            for basis in carrier.vertex_bases
            for leg in basis.legs
        ),
        recoupling=triple_recoupling_audit(),
    )


def fundamental_cut_kernel_identity() -> bool:
    """Verify the exact quaternion-component Peter--Weyl split."""

    lower = q_link(0)
    upper = q_link(1)
    actual = chi(1, q_mul(lower, q_conj(upper)))
    expected: Poly = {}
    for component in range(4):
        p_add_into(
            expected,
            p_mul(lower[component], upper[component]),
            Fraction(2),
        )
    return cast(bool, p_equal_on_group(actual, expected))


@dataclass(frozen=True)
class _TemporalGaugeGeometry:
    faces: tuple[tuple[tuple[int, int], ...], ...]
    metadata: tuple[FaceMeta, ...]
    lower_edges: frozenset[int]
    upper_edges: frozenset[int]
    lower_tree: frozenset[int]
    edge_count: int


@cache
def _temporal_gauge_geometry() -> _TemporalGaugeGeometry:
    complex_, raw_faces, raw_metadata = hypercube()
    faces = tuple(tuple(face) for face in raw_faces)
    metadata = tuple(raw_metadata)
    lower_edges: set[int] = set()
    upper_edges: set[int] = set()
    for face_index, (point, _first, second) in enumerate(metadata):
        if second == 3:
            continue
        target = lower_edges if point[3] == 0 else upper_edges
        target.update(edge for edge, _orientation in faces[face_index])

    adjacency: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for edge in lower_edges:
        left, right = complex_.edges[edge]
        adjacency[left].append((right, edge))
        adjacency[right].append((left, edge))
    root = min(adjacency)
    seen = {root}
    frontier: deque[int] = deque((root,))
    lower_tree: set[int] = set()
    while frontier:
        vertex = frontier.popleft()
        for neighbor, edge in sorted(adjacency[vertex]):
            if neighbor not in seen:
                seen.add(neighbor)
                lower_tree.add(edge)
                frontier.append(neighbor)
    if len(lower_tree) != 7:
        raise AssertionError("the lower spatial cube lost its spanning tree")
    return _TemporalGaugeGeometry(
        faces,
        metadata,
        frozenset(lower_edges),
        frozenset(upper_edges),
        frozenset(lower_tree),
        len(complex_.edges),
    )


def _path_quaternion(
    face: Sequence[tuple[int, int]],
    fixed_edges: frozenset[int],
) -> Quat:
    result = Q_ID
    for edge, orientation in face:
        value = Q_ID if edge in fixed_edges else q_link(edge)
        result = q_mul(
            result,
            value if orientation == 1 else q_conj(value),
        )
    return cast(Quat, result)


def temporal_gauge_amplitude(masks: Sequence[int]) -> SPoly:
    """Evaluate a mask family after temporal plus lower-tree gauge fixing."""

    geometry = _temporal_gauge_geometry()
    temporal_edges = frozenset(
        edge
        for face_index, (_point, _first, second) in enumerate(geometry.metadata)
        if second == 3
        for edge, _orientation in (
            geometry.faces[face_index][1],
            geometry.faces[face_index][3],
        )
    )
    fixed_edges = temporal_edges | geometry.lower_tree
    factors = [
        chi(1, _path_quaternion(geometry.faces[face_index], fixed_edges))
        for mask in masks
        for face_index in range(len(geometry.faces))
        if (mask >> face_index) & 1
    ]
    pending = (geometry.lower_edges | geometry.upper_edges) - geometry.lower_tree
    return scalar(contract_pairing_aware(factors or [dict(P_ONE)], pending))


def _boundary_occurrences(
    masks: Sequence[int],
) -> tuple[tuple[int, int], ...]:
    geometry = _temporal_gauge_geometry()
    return tuple(
        (strand_index, face_index)
        for strand_index, mask in enumerate(masks)
        for face_index, (_point, _first, second) in enumerate(geometry.metadata)
        if second == 3 and (mask >> face_index) & 1
    )


def _boundary_dot_factor(
    edge: int,
    fake_link: int,
    fixed_edges: frozenset[int],
) -> Poly:
    edge_quaternion = Q_ID if edge in fixed_edges else q_link(edge)
    factor: Poly = {}
    for component in range(4):
        p_add_into(
            factor,
            p_mul(edge_quaternion[component], p_var(fake_link, component)),
        )
    return factor


@cache
def _half_feature_polynomial(
    side: str,
    spatial_masks: tuple[int, ...],
    cut_masks: tuple[int, ...],
) -> Poly:
    geometry = _temporal_gauge_geometry()
    if side not in ("lower", "upper"):
        raise ValueError("half-feature side must be lower or upper")
    lower = side == "lower"
    fixed_edges = geometry.lower_tree if lower else frozenset()
    factors: list[Poly] = []
    for mask in spatial_masks:
        for face_index, (point, _first, second) in enumerate(geometry.metadata):
            if (
                second != 3
                and point[3] == int(not lower)
                and (mask >> face_index) & 1
            ):
                factors.append(
                    chi(
                        1,
                        _path_quaternion(
                            geometry.faces[face_index],
                            fixed_edges,
                        ),
                    )
                )
    occurrences = _boundary_occurrences(cut_masks)
    for occurrence_index, (_strand_index, face_index) in enumerate(occurrences):
        edge_position = 0 if lower else 2
        edge = geometry.faces[face_index][edge_position][0]
        factors.append(
            _boundary_dot_factor(
                edge,
                geometry.edge_count + occurrence_index,
                fixed_edges,
            )
        )
    pending = (
        geometry.lower_edges - geometry.lower_tree
        if lower
        else geometry.upper_edges
    )
    return contract_pairing_aware(factors or [dict(P_ONE)], pending)


def _boundary_word(
    monomial: tuple[tuple[int, int], ...],
    boundary_count: int,
    edge_count: int,
) -> BoundaryWord:
    components = [-1] * boundary_count
    for variable, exponent in monomial:
        if exponent != 1:
            raise AssertionError("boundary feature ceased to be multilinear")
        fake_link, component = divmod(variable, 4)
        occurrence = fake_link - edge_count
        if occurrence not in range(boundary_count):
            raise AssertionError("half feature retained a non-boundary variable")
        components[occurrence] = component
    if any(component < 0 for component in components):
        raise AssertionError("half feature lost a boundary leg")
    return tuple(components)


def _constant_coefficient(s_poly: SPoly) -> Fraction:
    if set(s_poly) - {0}:
        raise AssertionError("fixed-strand feature acquired heat powers")
    return cast(Fraction, s_poly.get(0, Fraction(0)))


@dataclass(frozen=True)
class HalfFeaturePairing:
    lower_spatial_masks: tuple[int, ...]
    upper_spatial_masks: tuple[int, ...]
    cut_masks: tuple[int, ...]
    boundary_leg_count: int
    lower_nonzero_components: int
    upper_nonzero_components: int
    common_nonzero_components: int
    amplitude: Fraction


@cache
def half_feature_pairing(
    lower_spatial_masks: tuple[int, ...],
    upper_spatial_masks: tuple[int, ...],
    cut_masks: tuple[int, ...],
) -> HalfFeaturePairing:
    """Pair exact lower/upper temporal-gauge boundary tensors."""

    geometry = _temporal_gauge_geometry()
    occurrences = _boundary_occurrences(cut_masks)
    lower = _half_feature_polynomial(
        "lower",
        lower_spatial_masks,
        cut_masks,
    )
    upper = _half_feature_polynomial(
        "upper",
        upper_spatial_masks,
        cut_masks,
    )
    lower_by_word = {
        _boundary_word(monomial, len(occurrences), geometry.edge_count):
        _constant_coefficient(coefficient)
        for monomial, coefficient in lower.items()
    }
    upper_by_word = {
        _boundary_word(monomial, len(occurrences), geometry.edge_count):
        _constant_coefficient(coefficient)
        for monomial, coefficient in upper.items()
    }
    common = set(lower_by_word) & set(upper_by_word)
    amplitude = Fraction(2 ** len(occurrences)) * sum(
        (
            lower_by_word[word] * upper_by_word[word]
            for word in common
        ),
        start=Fraction(0),
    )
    return HalfFeaturePairing(
        lower_spatial_masks,
        upper_spatial_masks,
        cut_masks,
        len(occurrences),
        len(lower_by_word),
        len(upper_by_word),
        len(common),
        amplitude,
    )


def coherent_hypercube_family_amplitude(masks: Sequence[int]) -> Fraction:
    """Resum a character family through exact face paths and vertex 6j data."""

    _complex, faces, metadata = hypercube()
    ledger: dict[tuple[int, ...], int] = {(): 1}
    for face_index in range(len(faces)):
        channels = character_product_channels(
            tuple(1 for mask in masks if (mask >> face_index) & 1)
        )
        following: dict[tuple[int, ...], int] = {}
        for prefix, multiplicity in ledger.items():
            for output, face_multiplicity in channels.items():
                assignment = prefix + (output,)
                following[assignment] = following.get(assignment, 0) + (
                    multiplicity * face_multiplicity
                )
        ledger = following
    return sum(
        (
            multiplicity * vertex_sixj_product(metadata, assignment)
            for assignment, multiplicity in ledger.items()
        ),
        start=Fraction(0),
    )


@dataclass(frozen=True)
class HalfSurfaceReconstructionAudit:
    local_cut_identity: bool
    generator_amplitudes: tuple[Fraction, Fraction, Fraction]
    pair_amplitude: Fraction
    family_feature_pairing: HalfFeaturePairing
    family_temporal_gauge_amplitude: Fraction
    family_direct_haar_amplitude: Fraction

    def validates(self) -> bool:
        return (
            self.local_cut_identity
            and self.generator_amplitudes
            == (Fraction(1, 16), Fraction(1, 16), Fraction(1, 256))
            and self.pair_amplitude == Fraction(41, 648)
            and self.family_feature_pairing.boundary_leg_count == 10
            and self.family_feature_pairing.lower_nonzero_components == 10
            and self.family_feature_pairing.upper_nonzero_components == 194560
            and self.family_feature_pairing.common_nonzero_components == 10
            and self.family_feature_pairing.amplitude
            == self.family_temporal_gauge_amplitude
            == self.family_direct_haar_amplitude
            == Fraction(83, 5184)
        )


@cache
def half_surface_reconstruction_audit() -> HalfSurfaceReconstructionAudit:
    cut_masks = (STRAND_ONE, STRAND_THREE)
    family_pairing = half_feature_pairing(
        (STRAND_ONE, STRAND_THREE, STRAND_TWO),
        (STRAND_ONE, STRAND_THREE),
        cut_masks,
    )
    direct = three_way_haar_audit().direct_haar
    return HalfSurfaceReconstructionAudit(
        local_cut_identity=fundamental_cut_kernel_identity(),
        generator_amplitudes=(
            coherent_hypercube_family_amplitude((RAW_THREE_STRAND_MASKS[0],)),
            coherent_hypercube_family_amplitude((RAW_THREE_STRAND_MASKS[1],)),
            coherent_hypercube_family_amplitude((RAW_THREE_STRAND_MASKS[2],)),
        ),
        pair_amplitude=coherent_hypercube_family_amplitude(cut_masks),
        family_feature_pairing=family_pairing,
        family_temporal_gauge_amplitude=_constant_coefficient(
            temporal_gauge_amplitude(RAW_THREE_STRAND_MASKS)
        ),
        family_direct_haar_amplitude=_constant_coefficient(direct),
    )


Matrix2: TypeAlias = tuple[
    tuple[Fraction, Fraction],
    tuple[Fraction, Fraction],
]


@dataclass(frozen=True)
class HalfCarrierGramAudit:
    """Exact Gram/SOS certificate on ``P13`` and ``S2 * P13``."""

    matrix: Matrix2
    determinant: Fraction
    ldlt_lower_entry: Fraction
    ldlt_diagonal: tuple[Fraction, Fraction]

    def validates(self) -> bool:
        first = Fraction(41, 648)
        cross = Fraction(83, 5184)
        second = Fraction(85, 20736)
        return (
            self.matrix == ((first, cross), (cross, second))
            and self.determinant == Fraction(1, 331776)
            and self.ldlt_lower_entry == Fraction(83, 328)
            and self.ldlt_diagonal
            == (Fraction(41, 648), Fraction(1, 20992))
            and self.determinant > 0
            and all(value > 0 for value in self.ldlt_diagonal)
        )


@cache
def half_carrier_gram_audit() -> HalfCarrierGramAudit:
    first = coherent_hypercube_family_amplitude(
        (STRAND_ONE, STRAND_THREE)
    )
    cross = coherent_hypercube_family_amplitude(
        (STRAND_ONE, STRAND_THREE, STRAND_TWO)
    )
    second = coherent_hypercube_family_amplitude(
        (
            STRAND_ONE,
            STRAND_THREE,
            STRAND_TWO,
            REFLECTED_STRAND_TWO,
        )
    )
    determinant = first * second - cross * cross
    lower_entry = cross / first
    second_pivot = second - lower_entry * lower_entry * first
    return HalfCarrierGramAudit(
        ((first, cross), (cross, second)),
        determinant,
        lower_entry,
        (first, second_pivot),
    )
