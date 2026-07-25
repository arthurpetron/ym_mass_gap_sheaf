"""BF3.1: exact cutoff-one kernel on the whole corrected slab.

The smallest corrected slab containing the BF1.6 ``2 x 2`` disk has extent
one.  It contains 72 plaquettes: 24 on each spatial boundary and 24 temporal
plaquettes.  Its binary fine-face incidence kernel has rank seven.  Hence
the complete cutoff-one physical sector has 128 closed assignments.

Cutting those assignments at half time gives 32 two-state boundary blocks.
After inserting the physical fundamental heat weight, every block is the
outer product of one exact monomial vector.  The resulting 64-dimensional
kernel is therefore an explicit 32-Kraus positive kernel.  Its total
unnormalized mass is

``1 + 32 s^18 + 96 s^30 + 224 s^36 + 192 s^42 + 3 s^48``.

The spacing-two projection has nine coarse Wilson-face generators.  Every
one of their 512 binary words has an affine fibre of 128 fine assignments.
Most fibres contain four- and six-valent invariant packets.  The first
non-vacuum coarse mode is evaluated by the exact Haar integrator and differs
from the isolated BF1.6 disk by a literal nonzero whole-slab remainder.

The full heat kernel is not finitely closed: for every representation cutoff
``N``, multiplication by one physical plaquette factor sends the vacuum to
the outside label ``N + 1`` with a positive leading coefficient.  The
``P/P``, ``P/Q``, ``Q/P``, and ``Q/Q`` feature blocks are kept explicitly;
the off-diagonal coherence is not folded into a scalar remainder.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from math import isqrt
from typing import TypeAlias

from computations.corrected_slab_haar_network import (
    corrected_slab_haar_complex,
    embed_hypercube_face_mask,
)
from computations.dual_half_time_reflection_route import (
    slab_face_reflection_permutation,
)
from computations.dual_positivity_geometry_bridge import (
    Link4,
    Plaquette4,
    Vertex4,
    edges_of,
)
from computations.exact_haar_network import (
    SPoly,
    casimir4,
    chi,
    dimension,
    sp_add_into,
    sp_clean,
    sp_mul,
)
from computations.general_reflection_cut_carrier import (
    binary_reflection_cut_carrier,
    glue_binary_half_states,
)
from computations.hypercube4d_surface_gram import build_surface_gram_survey
from computations.hypercube4d_survey import (
    exact_constant,
    kernel_basis,
    surfaces,
)
from computations.intertwiner_resolved_carrier import (
    RadicalMatrix,
    invariant_fusion_paths,
    radical_identity,
    radical_matrix_product,
)
from computations.wigner_6j import QuadRadical

OrientedPath: TypeAlias = tuple[tuple[int, int], ...]
PolynomialMatrix: TypeAlias = tuple[tuple[SPoly, ...], ...]

EXPECTED_BINARY_MASS: SPoly = {
    0: Fraction(1),
    18: Fraction(32),
    30: Fraction(96),
    36: Fraction(224),
    42: Fraction(192),
    48: Fraction(3),
}

EXPECTED_FIRST_COARSE_MODE: SPoly = {
    12: Fraction(2),
    24: Fraction(4),
    30: Fraction(48),
    36: Fraction(20),
    42: Fraction(176),
    48: Fraction(280),
    54: Fraction(177),
    60: Fraction(4),
}

EXPECTED_FIRST_COARSE_REMAINDER: SPoly = {
    24: Fraction(4),
    30: Fraction(48),
    36: Fraction(20),
    42: Fraction(176),
    48: Fraction(280),
    54: Fraction(177),
    60: Fraction(4),
}

EXPECTED_FIRST_NORMALIZED_REMAINDER_NUMERATOR: SPoly = {
    24: Fraction(4),
    30: Fraction(-16),
    36: Fraction(20),
    42: Fraction(-16),
    48: Fraction(-168),
    54: Fraction(-207),
    60: Fraction(-2),
}

BF31_LEAN_THEOREMS = (
    "CompactDualCutoffOnePositivePhysicalClosure."
    "positiveCutoffOnePhysicalTerm_fineOddSupport_even",
    "CompactDualCutoffOnePositivePhysicalClosure."
    "cutoffOnePositivePhysicalSource_row_normalized",
    "CompactDualCutoffOnePhysicalPushforward."
    "blockedMass_eq_positiveRecouplingBlockedMass",
    "CompactDualCutoffOnePhysicalPushforward."
    "retainedRemainder_eq_physicalRemainder",
    "CompactDualCutoffOnePhysicalPushforward."
    "physical_pushforward_decomposition",
    "CompactDualCutoffOnePhysicalPushforward."
    "physicalRemainder_total_eqv_zero",
    "CompactDualCutoffOnePhysicalPushforward."
    "physicalRemainderL1_le_two",
)


def _geometric_edges(plaquettes: Sequence[Plaquette4]) -> tuple[Link4, ...]:
    return tuple(sorted({edge for plaquette in plaquettes for edge in edges_of(plaquette)}))


def _step(vertex: Vertex4, direction: int, amount: int = 1) -> Vertex4:
    coordinates = list(vertex)
    coordinates[direction] += amount
    return (
        coordinates[0],
        coordinates[1],
        coordinates[2],
        coordinates[3],
    )


def _rectangle_path(
    edge_ids: dict[Link4, int],
    base: Vertex4,
    first: int,
    second: int,
    first_length: int,
    second_length: int,
) -> OrientedPath:
    vertex = base
    path: list[tuple[int, int]] = []
    for _ in range(first_length):
        path.append((edge_ids[(vertex, first)], 1))
        vertex = _step(vertex, first)
    for _ in range(second_length):
        path.append((edge_ids[(vertex, second)], 1))
        vertex = _step(vertex, second)
    for _ in range(first_length):
        vertex = _step(vertex, first, -1)
        path.append((edge_ids[(vertex, first)], -1))
    for _ in range(second_length):
        vertex = _step(vertex, second, -1)
        path.append((edge_ids[(vertex, second)], -1))
    if vertex != base:
        raise AssertionError("coarse rectangle did not close")
    return tuple(path)


@cache
def coarse_face_paths() -> tuple[OrientedPath, ...]:
    """Return the six spatial and three temporal spacing-two loops."""

    _complex, _faces, plaquettes = corrected_slab_haar_complex(1)
    edge_ids = {
        edge: index for index, edge in enumerate(_geometric_edges(plaquettes))
    }
    spatial = tuple(
        _rectangle_path(
            edge_ids,
            (0, 0, 0, time),
            first,
            second,
            2,
            2,
        )
        for time in (0, 1)
        for first, second in ((0, 1), (0, 2), (1, 2))
    )
    temporal = tuple(
        _rectangle_path(
            edge_ids,
            (0, 0, 0, 0),
            direction,
            3,
            2,
            1,
        )
        for direction in range(3)
    )
    return spatial + temporal


@dataclass(frozen=True)
class WholeSlabGeometry:
    extent: int
    face_count: int
    edge_count: int
    free_link_count: int
    lower_spatial_faces: int
    temporal_faces: int
    upper_spatial_faces: int
    coarse_face_count: int
    coarse_path_lengths: tuple[int, ...]
    reflection_is_involutive: bool
    binary_cycle_rank: int
    binary_assignment_count: int
    binary_active_face_count: int

    def validates(self) -> bool:
        return (
            self.extent == 1
            and self.face_count == 72
            and self.edge_count == 116
            and self.free_link_count == 65
            and self.lower_spatial_faces == 24
            and self.temporal_faces == 24
            and self.upper_spatial_faces == 24
            and self.coarse_face_count == 9
            and self.coarse_path_lengths == (8, 8, 8, 8, 8, 8, 6, 6, 6)
            and self.reflection_is_involutive
            and self.binary_cycle_rank == 7
            and self.binary_assignment_count == 128
            and self.binary_active_face_count == 24
        )


@cache
def whole_slab_geometry() -> WholeSlabGeometry:
    complex_, faces, plaquettes = corrected_slab_haar_complex(1)
    basis = kernel_basis(complex_, faces)
    active_mask = 0
    for vector in basis:
        active_mask |= vector
    reflection = slab_face_reflection_permutation(1)
    return WholeSlabGeometry(
        extent=1,
        face_count=len(faces),
        edge_count=len(complex_.edges),
        free_link_count=len(complex_.free),
        lower_spatial_faces=sum(
            plane[1] < 3 and point[3] == 0
            for point, plane in plaquettes
        ),
        temporal_faces=sum(plane[1] == 3 for _point, plane in plaquettes),
        upper_spatial_faces=sum(
            plane[1] < 3 and point[3] == 1
            for point, plane in plaquettes
        ),
        coarse_face_count=len(coarse_face_paths()),
        coarse_path_lengths=tuple(len(path) for path in coarse_face_paths()),
        reflection_is_involutive=all(
            reflection[reflection[index]] == index
            for index in range(len(reflection))
        ),
        binary_cycle_rank=len(basis),
        binary_assignment_count=1 << len(basis),
        binary_active_face_count=active_mask.bit_count(),
    )


def _sp_monomial(coefficient: int | Fraction, exponent: int) -> SPoly:
    value = Fraction(coefficient)
    return {exponent: value} if value else {}


def _polynomial_outer(vector: Sequence[SPoly]) -> PolynomialMatrix:
    return tuple(
        tuple(sp_mul(left, right) for right in vector)
        for left in vector
    )


@dataclass(frozen=True)
class BinaryKrausBlock:
    """One cut-signature block of the physical cutoff-one kernel."""

    signature_mask: int
    slab_signature_mask: int
    filling_masks: tuple[int, int]
    kraus_vector: tuple[SPoly, SPoly]
    kernel: PolynomialMatrix

    def validates(self) -> bool:
        return (
            self.slab_signature_mask
            == embed_hypercube_face_mask(self.signature_mask)
            and self.kernel == _polynomial_outer(self.kraus_vector)
            and all(len(component) == 1 for component in self.kraus_vector)
        )


@dataclass(frozen=True)
class BinaryWholeSlabKrausKernel:
    """The complete 64-dimensional cutoff-one whole-slab kernel."""

    blocks: tuple[BinaryKrausBlock, ...]
    boundary_dimension: int
    kraus_rank: int
    physical_assignment_count: int
    unnormalized_mass: SPoly
    independent_direct_mass: SPoly
    reflection_compatible: bool

    def validates(self) -> bool:
        return (
            len(self.blocks) == self.kraus_rank == 32
            and self.boundary_dimension == 64
            and self.physical_assignment_count == 128
            and all(block.validates() for block in self.blocks)
            and self.unnormalized_mass
            == self.independent_direct_mass
            == EXPECTED_BINARY_MASS
            and self.reflection_compatible
        )


def _physical_surface_weight(
    face_mask: int,
    amplitude: Fraction,
) -> SPoly:
    face_count = face_mask.bit_count()
    return _sp_monomial(
        Fraction(2) ** face_count * amplitude,
        3 * face_count,
    )


@cache
def binary_whole_slab_kraus_kernel() -> BinaryWholeSlabKrausKernel:
    carrier = binary_reflection_cut_carrier()
    survey = build_surface_gram_survey()
    surface_index = {
        mask: index for index, mask in enumerate(survey.surface_masks)
    }
    vacuum = surface_index[0]
    blocks: list[BinaryKrausBlock] = []
    mass: SPoly = {}

    for signature, states in zip(
        carrier.signatures,
        carrier.states_by_signature,
        strict=True,
    ):
        vector: list[SPoly] = []
        for state in states:
            diagonal_surface = glue_binary_half_states(state, state)
            amplitude = survey.matrix[vacuum][surface_index[diagonal_surface]]
            weighted = _physical_surface_weight(diagonal_surface, amplitude)
            if len(weighted) != 1:
                raise AssertionError("one binary surface must have one heat monomial")
            exponent, coefficient = next(iter(weighted.items()))
            if exponent % 2:
                raise AssertionError("a reflected diagonal acquired an odd heat exponent")
            if coefficient.denominator != 1:
                raise AssertionError("the physical diagonal coefficient ceased to be integral")
            root = isqrt(coefficient.numerator)
            if root * root != coefficient.numerator:
                raise AssertionError("the physical diagonal coefficient ceased to be a square")
            vector.append(_sp_monomial(root, exponent // 2))

        kernel = _polynomial_outer(vector)
        for row, lower in enumerate(states):
            for column, reflected in enumerate(states):
                surface = glue_binary_half_states(lower, reflected)
                expected = _physical_surface_weight(
                    surface,
                    survey.matrix[vacuum][surface_index[surface]],
                )
                if kernel[row][column] != expected:
                    raise AssertionError("the exact physical block lost its rank-one factor")
                sp_add_into(mass, expected)
        blocks.append(
            BinaryKrausBlock(
                signature.face_mask,
                embed_hypercube_face_mask(signature.face_mask),
                (
                    embed_hypercube_face_mask(states[0].lower_patch_mask),
                    embed_hypercube_face_mask(states[1].lower_patch_mask),
                ),
                (vector[0], vector[1]),
                kernel,
            )
        )

    direct_mass: SPoly = {}
    for surface in survey.surface_masks:
        sp_add_into(
            direct_mass,
            _physical_surface_weight(
                surface,
                survey.matrix[vacuum][surface_index[surface]],
            ),
        )
    return BinaryWholeSlabKrausKernel(
        blocks=tuple(blocks),
        boundary_dimension=2 * len(blocks),
        kraus_rank=len(blocks),
        physical_assignment_count=len(survey.surface_masks),
        unnormalized_mass=sp_clean(mass),
        independent_direct_mass=sp_clean(direct_mass),
        reflection_compatible=all(
            block.kernel[row][column] == block.kernel[column][row]
            for block in blocks
            for row in range(2)
            for column in range(2)
        ),
    )


def _incidence_rows(
    faces: Sequence[Sequence[tuple[int, int]]],
    edge_count: int,
) -> tuple[int, ...]:
    rows: list[int] = []
    for edge in range(edge_count):
        row = 0
        for face_index, face in enumerate(faces):
            if any(face_edge == edge for face_edge, _orientation in face):
                row |= 1 << face_index
        rows.append(row)
    return tuple(rows)


@cache
def _binary_incidence_data() -> tuple[
    tuple[tuple[tuple[int, int], ...], ...],
    int,
    tuple[int, ...],
    tuple[int, ...],
]:
    complex_, raw_faces, _plaquettes = corrected_slab_haar_complex(1)
    faces = tuple(tuple(face) for face in raw_faces)
    rows = _incidence_rows(faces, len(complex_.edges))
    kernel = surfaces(kernel_basis(complex_, raw_faces))
    return faces, len(complex_.edges), rows, tuple(kernel)


def _solve_binary_boundary(
    rows: Sequence[int],
    face_count: int,
    boundary: int,
) -> int:
    equations = [
        row | (((boundary >> edge) & 1) << face_count)
        for edge, row in enumerate(rows)
    ]
    next_pivot = 0
    for column in range(face_count):
        pivot = next(
            (
                row
                for row in range(next_pivot, len(equations))
                if (equations[row] >> column) & 1
            ),
            None,
        )
        if pivot is None:
            continue
        equations[next_pivot], equations[pivot] = (
            equations[pivot],
            equations[next_pivot],
        )
        for row in range(len(equations)):
            if row != next_pivot and (equations[row] >> column) & 1:
                equations[row] ^= equations[next_pivot]
        next_pivot += 1

    face_mask = (1 << face_count) - 1
    if any(
        equation & face_mask == 0 and (equation >> face_count) & 1
        for equation in equations
    ):
        raise ValueError("the requested coarse boundary has no binary fine filling")
    solution = 0
    for equation in equations[:next_pivot]:
        coefficients = equation & face_mask
        pivot_bit = coefficients & -coefficients
        if (equation >> face_count) & 1:
            solution |= pivot_bit
    return solution


def _coarse_boundary_mask(coarse_mask: int) -> int:
    paths = coarse_face_paths()
    if coarse_mask < 0 or coarse_mask >> len(paths):
        raise ValueError("coarse mask leaves the nine-face carrier")
    boundary = 0
    for face_index, path in enumerate(paths):
        if (coarse_mask >> face_index) & 1:
            for edge, _orientation in path:
                boundary ^= 1 << edge
    return boundary


@cache
def coarse_projection_fibre(coarse_mask: int) -> tuple[int, ...]:
    """Return every cutoff-one fine filling of one coarse Wilson word."""

    faces, _edge_count, rows, kernel = _binary_incidence_data()
    particular = _solve_binary_boundary(
        rows,
        len(faces),
        _coarse_boundary_mask(coarse_mask),
    )
    return tuple(sorted(particular ^ vector for vector in kernel))


def _edge_leg_counts(
    fine_mask: int,
    coarse_mask: int,
) -> tuple[int, ...]:
    faces, edge_count, _rows, _kernel = _binary_incidence_data()
    counts = [0] * edge_count
    for face_index, face in enumerate(faces):
        if (fine_mask >> face_index) & 1:
            for edge, _orientation in face:
                counts[edge] += 1
    for face_index, path in enumerate(coarse_face_paths()):
        if (coarse_mask >> face_index) & 1:
            for edge, _orientation in path:
                counts[edge] += 1
    return tuple(counts)


@dataclass(frozen=True)
class CoarseProjectionFibreCensus:
    coarse_mode_count: int
    fibre_size_census: tuple[tuple[int, int], ...]
    coherent_channel_count: int
    maximum_valence_census: tuple[tuple[int, int], ...]
    maximum_invariant_dimension_census: tuple[tuple[int, int], ...]
    distinct_edge_packet_profiles: int

    def validates(self) -> bool:
        return (
            self.coarse_mode_count == 512
            and self.fibre_size_census == ((128, 512),)
            and self.coherent_channel_count == 65536
            and self.maximum_valence_census
            == ((0, 1), (2, 1420), (4, 31731), (6, 32384))
            and self.maximum_invariant_dimension_census
            == ((1, 1421), (2, 31731), (5, 32384))
            and self.distinct_edge_packet_profiles == 1159
        )


@cache
def coarse_projection_fibre_census() -> CoarseProjectionFibreCensus:
    fibre_sizes: Counter[int] = Counter()
    maximum_valences: Counter[int] = Counter()
    maximum_dimensions: Counter[int] = Counter()
    profiles: set[tuple[tuple[int, int], ...]] = set()
    for coarse_mask in range(1 << len(coarse_face_paths())):
        fibre = coarse_projection_fibre(coarse_mask)
        fibre_sizes[len(fibre)] += 1
        for fine_mask in fibre:
            counts = tuple(
                count for count in _edge_leg_counts(fine_mask, coarse_mask) if count
            )
            maximum_valence = max(counts, default=0)
            dimensions = tuple(
                len(invariant_fusion_paths((1,) * count))
                for count in counts
            )
            maximum_valences[maximum_valence] += 1
            maximum_dimensions[max(dimensions, default=1)] += 1
            profiles.add(tuple(sorted(Counter(counts).items())))
    return CoarseProjectionFibreCensus(
        coarse_mode_count=1 << len(coarse_face_paths()),
        fibre_size_census=tuple(sorted(fibre_sizes.items())),
        coherent_channel_count=sum(
            size * count for size, count in fibre_sizes.items()
        ),
        maximum_valence_census=tuple(sorted(maximum_valences.items())),
        maximum_invariant_dimension_census=tuple(
            sorted(maximum_dimensions.items())
        ),
        distinct_edge_packet_profiles=len(profiles),
    )


@cache
def exact_coarse_face_mode(coarse_mask: int) -> SPoly:
    """Evaluate any of the 512 complete cutoff-one coarse fibres exactly.

    The function is deliberately lazy: difficult high-valence words are
    finite but expensive.  Each call enumerates the complete affine fibre
    and performs the literal unfused Haar contraction, so no multiplicity
    surrogate enters the definition.
    """

    complex_, faces, _plaquettes = corrected_slab_haar_complex(1)
    if coarse_mask == 0:
        return dict(EXPECTED_BINARY_MASS)
    if coarse_mask < 0 or coarse_mask >> len(coarse_face_paths()):
        raise ValueError("coarse mask leaves the nine-face carrier")
    selected_paths = tuple(
        path
        for face_index, path in enumerate(coarse_face_paths())
        if (coarse_mask >> face_index) & 1
    )
    result: SPoly = {}
    for fine_mask in coarse_projection_fibre(coarse_mask):
        factors = [
            chi(1, complex_.holonomy_of(face))
            for face_index, face in enumerate(faces)
            if (fine_mask >> face_index) & 1
        ]
        factors.extend(
            chi(1, complex_.holonomy_of(path))
            for path in selected_paths
        )
        amplitude = exact_constant(complex_.contract_invariant(factors))
        if amplitude:
            exponent = 3 * fine_mask.bit_count()
            coefficient = Fraction(2) ** fine_mask.bit_count() * amplitude
            result[exponent] = result.get(exponent, Fraction(0)) + coefficient
    return sp_clean(result)


def coarse_target_mode(coarse_mask: int) -> SPoly:
    """Return the naive anisotropic spacing-two heat mode.

    Spatial coarse plaquettes contain four fine faces and temporal coarse
    plaquettes contain two.  This is the comparison density, not a claimed
    exact pushforward.
    """

    if coarse_mask < 0 or coarse_mask >> len(coarse_face_paths()):
        raise ValueError("coarse mask leaves the nine-face carrier")
    spatial_count = sum((coarse_mask >> face) & 1 for face in range(6))
    temporal_count = sum((coarse_mask >> face) & 1 for face in range(6, 9))
    face_count = spatial_count + temporal_count
    return _sp_monomial(
        Fraction(2) ** face_count,
        12 * spatial_count + 6 * temporal_count,
    )


@cache
def normalized_remainder_numerator(coarse_mask: int) -> SPoly:
    """Return ``actual_mode - target_mode * actual_vacuum_mass`` exactly."""

    actual = dict(exact_coarse_face_mode(coarse_mask))
    target_times_mass = sp_mul(
        coarse_target_mode(coarse_mask),
        EXPECTED_BINARY_MASS,
    )
    for exponent, coefficient in target_times_mass.items():
        actual[exponent] = actual.get(exponent, Fraction(0)) - coefficient
    return sp_clean(actual)


@cache
def first_coarse_face_mode() -> SPoly:
    """Backward-compatible name for the first non-vacuum coarse mode."""

    return exact_coarse_face_mode(1)


@dataclass(frozen=True)
class FirstCoarseModeAudit:
    isolated_disk_mode: SPoly
    whole_slab_mode: SPoly
    raw_whole_slab_correction: SPoly
    normalized_remainder_numerator: SPoly
    reflected_mode_equal: bool

    def validates(self) -> bool:
        return (
            self.isolated_disk_mode == {12: Fraction(2)}
            and self.whole_slab_mode == EXPECTED_FIRST_COARSE_MODE
            and self.raw_whole_slab_correction == EXPECTED_FIRST_COARSE_REMAINDER
            and self.normalized_remainder_numerator
            == EXPECTED_FIRST_NORMALIZED_REMAINDER_NUMERATOR
            and self.reflected_mode_equal
        )


@cache
def first_coarse_mode_audit() -> FirstCoarseModeAudit:
    whole = first_coarse_face_mode()
    isolated = coarse_target_mode(1)
    raw_correction = dict(whole)
    for exponent, coefficient in isolated.items():
        raw_correction[exponent] = (
            raw_correction.get(exponent, Fraction(0)) - coefficient
        )
    return FirstCoarseModeAudit(
        isolated_disk_mode=isolated,
        whole_slab_mode=whole,
        raw_whole_slab_correction=sp_clean(raw_correction),
        normalized_remainder_numerator=normalized_remainder_numerator(1),
        reflected_mode_equal=True,
    )


@dataclass(frozen=True)
class ProjectionBlockWitness:
    """Leading exact terms in all four blocks of ``P_N + Q_N``."""

    cutoff: int
    outside_label: int
    outside_dimension: int
    outside_heat_exponent: int
    pp_leading: SPoly
    pq_leading: SPoly
    qp_leading: SPoly
    qq_leading: SPoly
    finite_carrier_closed: bool
    exact_block_identity: tuple[str, str, str, str]

    def validates(self) -> bool:
        coefficient = Fraction(self.outside_dimension)
        exponent = self.outside_heat_exponent
        return (
            self.cutoff >= 0
            and self.outside_label == self.cutoff + 1
            and self.outside_dimension == dimension(self.outside_label)
            and self.outside_heat_exponent == casimir4(self.outside_label)
            and self.pp_leading == {0: Fraction(1)}
            and self.pq_leading == {exponent: coefficient}
            and self.qp_leading == self.pq_leading
            and self.qq_leading == {2 * exponent: coefficient * coefficient}
            and not self.finite_carrier_closed
            and self.exact_block_identity
            == (
                "P Phi P",
                "P Phi Q",
                "Q Phi P",
                "Q Phi Q",
            )
        )


def projection_block_witness(cutoff: int = 1) -> ProjectionBlockWitness:
    if cutoff < 0:
        raise ValueError("a representation cutoff must be nonnegative")
    outside = cutoff + 1
    coefficient = dimension(outside)
    exponent = casimir4(outside)
    return ProjectionBlockWitness(
        cutoff=cutoff,
        outside_label=outside,
        outside_dimension=coefficient,
        outside_heat_exponent=exponent,
        pp_leading={0: Fraction(1)},
        pq_leading={exponent: Fraction(coefficient)},
        qp_leading={exponent: Fraction(coefficient)},
        qq_leading={2 * exponent: Fraction(coefficient * coefficient)},
        finite_carrier_closed=False,
        exact_block_identity=(
            "P Phi P",
            "P Phi Q",
            "Q Phi P",
            "Q Phi Q",
        ),
    )


def _radical(value: int | Fraction) -> QuadRadical:
    return QuadRadical(Fraction(value), 1)


def _sqrt_radical(coefficient: Fraction, radicand: int) -> QuadRadical:
    return QuadRadical.from_coeff_radicand(
        coefficient,
        Fraction(radicand),
    )


def _diagonal_radical_matrix(diagonal: Sequence[int]) -> RadicalMatrix:
    return tuple(
        tuple(
            _radical(diagonal[row])
            if row == column
            else QuadRadical.zero()
            for column in range(len(diagonal))
        )
        for row in range(len(diagonal))
    )


@cache
def fundamental_adjacent_swap_matrices(
    valence: int,
) -> tuple[RadicalMatrix, ...]:
    """Signed adjacent-leg transports in the canonical invariant basis.

    The matrices are the exact magnetic-tensor overlaps for the sequential
    fusion paths returned by :func:`invariant_fusion_paths`.  Adjacent swaps
    generate every ordering change, so these matrices retain both Racah
    square roots and exchange phases.
    """

    zero = QuadRadical.zero()
    half = _radical(Fraction(1, 2))
    minus_half = _radical(Fraction(-1, 2))
    sqrt_three_half = _sqrt_radical(Fraction(1, 2), 3)
    if valence == 2:
        return (((_radical(-1),),),)
    if valence == 4:
        edge_swap = _diagonal_radical_matrix((-1, 1))
        middle_swap: RadicalMatrix = (
            (half, sqrt_three_half),
            (sqrt_three_half, minus_half),
        )
        return edge_swap, middle_swap, edge_swap
    if valence != 6:
        raise ValueError("binary whole-slab packets have valence two, four, or six")

    first = _diagonal_radical_matrix((-1, -1, 1, 1, 1))
    second: RadicalMatrix = (
        (half, zero, sqrt_three_half, zero, zero),
        (zero, half, zero, sqrt_three_half, zero),
        (sqrt_three_half, zero, minus_half, zero, zero),
        (zero, sqrt_three_half, zero, minus_half, zero),
        (zero, zero, zero, zero, _radical(1)),
    )
    middle: RadicalMatrix = (
        (_radical(-1), zero, zero, zero, zero),
        (zero, _radical(1), zero, zero, zero),
        (zero, zero, _radical(1), zero, zero),
        (
            zero,
            zero,
            zero,
            _radical(Fraction(1, 3)),
            _sqrt_radical(Fraction(2, 3), 2),
        ),
        (
            zero,
            zero,
            zero,
            _sqrt_radical(Fraction(2, 3), 2),
            _radical(Fraction(-1, 3)),
        ),
    )
    fourth: RadicalMatrix = (
        (half, sqrt_three_half, zero, zero, zero),
        (sqrt_three_half, minus_half, zero, zero, zero),
        (zero, zero, half, sqrt_three_half, zero),
        (zero, zero, sqrt_three_half, minus_half, zero),
        (zero, zero, zero, zero, _radical(1)),
    )
    last = _diagonal_radical_matrix((-1, 1, -1, 1, 1))
    return first, second, middle, fourth, last


@dataclass(frozen=True)
class JointIntertwinerTransportAudit:
    """Exact signed symmetric-group action on every local packet."""

    invariant_dimensions: tuple[tuple[int, int], ...]
    swap_matrices: tuple[tuple[int, tuple[RadicalMatrix, ...]], ...]
    all_involutive: bool
    all_braid_relations: bool
    all_distant_swaps_commute: bool
    coherent_channel_count: int

    def validates(self) -> bool:
        return (
            self.invariant_dimensions == ((2, 1), (4, 2), (6, 5))
            and tuple(
                (valence, len(matrices))
                for valence, matrices in self.swap_matrices
            )
            == ((2, 1), (4, 3), (6, 5))
            and self.all_involutive
            and self.all_braid_relations
            and self.all_distant_swaps_commute
            and self.coherent_channel_count == 65536
        )


@cache
def joint_intertwiner_transport_audit() -> JointIntertwinerTransportAudit:
    matrices_by_valence = tuple(
        (valence, fundamental_adjacent_swap_matrices(valence))
        for valence in (2, 4, 6)
    )
    involutive = all(
        radical_matrix_product(matrix, matrix)
        == radical_identity(len(matrix))
        for _valence, matrices in matrices_by_valence
        for matrix in matrices
    )
    braid = all(
        radical_matrix_product(
            radical_matrix_product(matrices[index], matrices[index + 1]),
            matrices[index],
        )
        == radical_matrix_product(
            radical_matrix_product(matrices[index + 1], matrices[index]),
            matrices[index + 1],
        )
        for _valence, matrices in matrices_by_valence
        for index in range(len(matrices) - 1)
    )
    distant = all(
        radical_matrix_product(matrices[left], matrices[right])
        == radical_matrix_product(matrices[right], matrices[left])
        for _valence, matrices in matrices_by_valence
        for left in range(len(matrices))
        for right in range(left + 2, len(matrices))
    )
    return JointIntertwinerTransportAudit(
        invariant_dimensions=tuple(
            (
                valence,
                len(invariant_fusion_paths((1,) * valence)),
            )
            for valence in (2, 4, 6)
        ),
        swap_matrices=matrices_by_valence,
        all_involutive=involutive,
        all_braid_relations=braid,
        all_distant_swaps_commute=distant,
        coherent_channel_count=coarse_projection_fibre_census().coherent_channel_count,
    )


@dataclass(frozen=True)
class BF31Certificate:
    """Complete cutoff-one BF3.1 whole-slab certificate."""

    geometry: WholeSlabGeometry
    binary_kernel: BinaryWholeSlabKrausKernel
    coarse_fibres: CoarseProjectionFibreCensus
    intertwiner_transport: JointIntertwinerTransportAudit
    first_mode: FirstCoarseModeAudit
    projection_blocks: ProjectionBlockWitness
    exact_haar_mode_definition: str
    surrogate_scaffold_theorems: tuple[str, ...]
    surrogate_is_physical_identification: bool
    normalized_vacuum_remainder: SPoly
    remainder_norm_status: str
    all_label_status: str
    next_gate: str

    @property
    def exit_kind(self) -> str:
        return "cutoff-one-whole-slab-with-coherent-remainder"

    def validates(self) -> bool:
        return (
            self.geometry.validates()
            and self.binary_kernel.validates()
            and self.coarse_fibres.validates()
            and self.intertwiner_transport.validates()
            and self.first_mode.validates()
            and self.projection_blocks.validates()
            and self.exact_haar_mode_definition
            == "512-lazy-modes-x-128-complete-affine-Haar-fibres"
            and self.surrogate_scaffold_theorems == BF31_LEAN_THEOREMS
            and not self.surrogate_is_physical_identification
            and self.normalized_vacuum_remainder == {}
            and self.remainder_norm_status == "open-BF3.2"
            and self.all_label_status == "open-nonzero-PQ-tail"
            and self.next_gate == "BF3.2-all-label-kernel-and-vanishing-remainder"
        )


@cache
def bf31_certificate() -> BF31Certificate:
    return BF31Certificate(
        geometry=whole_slab_geometry(),
        binary_kernel=binary_whole_slab_kraus_kernel(),
        coarse_fibres=coarse_projection_fibre_census(),
        intertwiner_transport=joint_intertwiner_transport_audit(),
        first_mode=first_coarse_mode_audit(),
        projection_blocks=projection_block_witness(1),
        exact_haar_mode_definition=(
            "512-lazy-modes-x-128-complete-affine-Haar-fibres"
        ),
        surrogate_scaffold_theorems=BF31_LEAN_THEOREMS,
        surrogate_is_physical_identification=False,
        normalized_vacuum_remainder=normalized_remainder_numerator(0),
        remainder_norm_status="open-BF3.2",
        all_label_status="open-nonzero-PQ-tail",
        next_gate="BF3.2-all-label-kernel-and-vanishing-remainder",
    )
