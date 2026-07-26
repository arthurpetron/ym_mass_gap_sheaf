"""Open-index cutoff-one spin network for the BF4 transverse carrier.

This module keeps the 15-face transverse component as a tensor network rather
than flattening its 10673 boundary fusion paths.  Every gauge-fixed face word
is a cyclic magnetic-index wire.  The five unprotected links are rank-one
Haar projectors built from normalized oriented trivalent invariants, while
the nine protected links are left open in complete Clebsch--Gordan output
channels.

The protected outputs are also matched to the selected heat corridors.  At a
core protected link, two residual faces and two selected faces share one pair
fusion output ``k``; the normalized Haar projector contributes ``1/(k+1)``.
The all-fundamental packet has channels ``k = 0, 2`` and therefore requires a
signed two-dimensional Racah transport when the grouped pair order is changed
to canonical face order.  At a decoration link, the selected pair output must
equal the single residual face label.

All local magnetic coefficients are exact quadratic radicals in the
Condon--Shortley convention.  Negative link orientations are preserved and
converted with the standard SU(2) self-duality map.  Its fundamental
Frobenius--Schur sign is explicit: ``J^2 = -1``.  Thus the finite local network
is Choi/Kraus-ready, but a physical global Choi operator is not claimed until
the selected-corridor source indices are contracted in the same pivotal
convention.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import product
from typing import TypeAlias, cast

from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.exact_haar_network import fusion_labels, invariant_multiplicity
from computations.transverse_cutoff_one_loop_tensor import (
    CONNECTED_CORE_FACE_IDS,
    CORRIDOR_FACE_IDS,
    cutoff_one_core_geometry,
)
from computations.transverse_cutoff_one_residual_tensor import (
    DECORATION_FACE_IDS,
    cutoff_one_decoration_geometry,
)
from computations.wigner_6j import QuadRadical

CornerIndex: TypeAlias = tuple[int, int]
RadicalMatrix: TypeAlias = tuple[tuple[QuadRadical, ...], ...]
MatrixSignature: TypeAlias = tuple[
    tuple[tuple[Fraction, int], ...],
    ...,
]
PairLabels: TypeAlias = tuple[int, int]

R_ZERO = QuadRadical.zero()
R_ONE = QuadRadical(Fraction(1), 1)


def magnetic_indices(label: int) -> tuple[int, ...]:
    """Return doubled magnetic indices for one doubled-spin label."""

    if label < 0:
        raise ValueError("a doubled-spin label must be nonnegative")
    return tuple(range(-label, label + 1, 2))


def _sqrt_fraction(value: Fraction) -> QuadRadical:
    return QuadRadical.from_coeff_radicand(Fraction(1), value)


def _sum_radicals(values: tuple[QuadRadical, ...]) -> QuadRadical:
    """Sum a cutoff-one expression known to remain one quadratic radical."""

    by_radical: dict[int, Fraction] = {}
    for value in values:
        by_radical[value.rad] = (
            by_radical.get(value.rad, Fraction(0)) + value.coeff
        )
    nonzero = tuple(
        (radical, coefficient)
        for radical, coefficient in by_radical.items()
        if coefficient
    )
    if not nonzero:
        return R_ZERO
    if len(nonzero) != 1:
        raise AssertionError("the cutoff-one coefficient left one radical field")
    radical, coefficient = nonzero[0]
    return QuadRadical(coefficient, radical)


def cutoff_one_cg_coefficient(
    left_label: int,
    left_magnetic: int,
    right_label: int,
    right_magnetic: int,
    output_label: int,
    output_magnetic: int,
) -> QuadRadical:
    """Exact Condon--Shortley CG coefficient for inputs in ``{0, 1}``."""

    if left_label not in (0, 1) or right_label not in (0, 1):
        raise ValueError("the cutoff-one CG inputs must have labels zero or one")
    if left_magnetic not in magnetic_indices(left_label):
        raise ValueError("the left magnetic index leaves its representation")
    if right_magnetic not in magnetic_indices(right_label):
        raise ValueError("the right magnetic index leaves its representation")
    if output_label < 0:
        raise ValueError("the output label must be nonnegative")
    if output_magnetic not in magnetic_indices(output_label):
        raise ValueError("the output magnetic index leaves its representation")
    if (
        output_label not in fusion_labels(left_label, right_label)
        or left_magnetic + right_magnetic != output_magnetic
    ):
        return R_ZERO
    if left_label == 0:
        return R_ONE
    if right_label == 0:
        return R_ONE
    if output_label == 0:
        sign = 1 if left_magnetic == 1 else -1
        return sign * _sqrt_fraction(Fraction(1, 2))
    if output_label != 2:
        return R_ZERO
    if left_magnetic == right_magnetic:
        return R_ONE
    return _sqrt_fraction(Fraction(1, 2))


def duality_coefficient(
    label: int,
    source_magnetic: int,
    target_magnetic: int,
) -> int:
    """Matrix coefficient of ``J : conjugate(V_j) -> V_j``.

    The convention is
    ``J |j,m>* = (-1)^(j-m) |j,-m>``.  For the fundamental representation
    this gives ``J^2 = -I``.
    """

    if label not in (0, 1):
        raise ValueError("the open-index pilot only dualizes labels zero and one")
    if source_magnetic not in magnetic_indices(label):
        raise ValueError("the source magnetic index leaves its representation")
    if target_magnetic not in magnetic_indices(label):
        raise ValueError("the target magnetic index leaves its representation")
    if target_magnetic != -source_magnetic:
        return 0
    exponent = (label - source_magnetic) // 2
    return 1 if exponent % 2 == 0 else -1


def _orient_magnetic(
    label: int,
    raw_magnetic: int,
    orientation: int,
) -> tuple[int, int]:
    if orientation == 1:
        return raw_magnetic, 1
    if orientation != -1:
        raise ValueError("an oriented tensor leg must have sign +1 or -1")
    canonical = -raw_magnetic
    return (
        canonical,
        duality_coefficient(label, raw_magnetic, canonical),
    )


def oriented_cutoff_one_cg_coefficient(
    left_label: int,
    left_magnetic: int,
    left_orientation: int,
    right_label: int,
    right_magnetic: int,
    right_orientation: int,
    output_label: int,
    output_magnetic: int,
) -> QuadRadical:
    """CG coefficient after explicit dualization of negative raw legs."""

    canonical_left, left_phase = _orient_magnetic(
        left_label,
        left_magnetic,
        left_orientation,
    )
    canonical_right, right_phase = _orient_magnetic(
        right_label,
        right_magnetic,
        right_orientation,
    )
    return (
        left_phase
        * right_phase
        * cutoff_one_cg_coefficient(
            left_label,
            canonical_left,
            right_label,
            canonical_right,
            output_label,
            output_magnetic,
        )
    )


def cutoff_one_three_j_coefficient(
    labels: tuple[int, int, int],
    magnetics: tuple[int, int, int],
) -> QuadRadical:
    """Normalized invariant tensor in ordered Condon--Shortley convention."""

    if any(label not in (0, 1) for label in labels):
        raise ValueError("the trivalent cutoff-one labels must be zero or one")
    if any(
        magnetic not in magnetic_indices(label)
        for label, magnetic in zip(labels, magnetics, strict=True)
    ):
        raise ValueError("a trivalent magnetic index leaves its representation")
    if invariant_multiplicity(labels) != 1:
        return R_ZERO
    first, second, third = labels
    first_magnetic, second_magnetic, third_magnetic = magnetics
    phase_exponent = (first - second - third_magnetic) // 2
    phase = 1 if phase_exponent % 2 == 0 else -1
    normalization = _sqrt_fraction(Fraction(1, third + 1))
    return (
        phase
        * normalization
        * cutoff_one_cg_coefficient(
            first,
            first_magnetic,
            second,
            second_magnetic,
            third,
            -third_magnetic,
        )
    )


def oriented_cutoff_one_three_j_coefficient(
    labels: tuple[int, int, int],
    raw_magnetics: tuple[int, int, int],
    orientations: tuple[int, int, int],
) -> QuadRadical:
    """Oriented trivalent invariant with every negative leg dualized."""

    canonical: list[int] = []
    phase = 1
    for label, magnetic, orientation in zip(
        labels,
        raw_magnetics,
        orientations,
        strict=True,
    ):
        following, following_phase = _orient_magnetic(
            label,
            magnetic,
            orientation,
        )
        canonical.append(following)
        phase *= following_phase
    return phase * cutoff_one_three_j_coefficient(
        labels,
        tuple(canonical),  # type: ignore[arg-type]
    )


def pair_pair_invariant_coefficient(
    labels: tuple[int, int, int, int],
    magnetics: tuple[int, int, int, int],
    channel: int,
) -> QuadRadical:
    """Normalized four-leg invariant in the ``(12)(34) -> channel`` basis."""

    if any(label not in (0, 1) for label in labels):
        raise ValueError("the pair carrier is restricted to cutoff one")
    if channel not in (
        set(fusion_labels(labels[0], labels[1]))
        & set(fusion_labels(labels[2], labels[3]))
    ):
        return R_ZERO
    terms: list[QuadRadical] = []
    normalization = _sqrt_fraction(Fraction(1, channel + 1))
    for output_magnetic in magnetic_indices(channel):
        cap_phase = (-1) ** ((channel - output_magnetic) // 2)
        terms.append(
            cap_phase
            * normalization
            * cutoff_one_cg_coefficient(
                labels[0],
                magnetics[0],
                labels[1],
                magnetics[1],
                channel,
                output_magnetic,
            )
            * cutoff_one_cg_coefficient(
                labels[2],
                magnetics[2],
                labels[3],
                magnetics[3],
                channel,
                -output_magnetic,
            )
        )
    return _sum_radicals(tuple(terms))


def oriented_pair_pair_invariant_coefficient(
    labels: tuple[int, int, int, int],
    raw_magnetics: tuple[int, int, int, int],
    orientations: tuple[int, int, int, int],
    channel: int,
) -> QuadRadical:
    """Four-leg invariant with the four raw orientation signs retained."""

    canonical: list[int] = []
    phase = 1
    for label, magnetic, orientation in zip(
        labels,
        raw_magnetics,
        orientations,
        strict=True,
    ):
        following, following_phase = _orient_magnetic(
            label,
            magnetic,
            orientation,
        )
        canonical.append(following)
        phase *= following_phase
    return phase * pair_pair_invariant_coefficient(
        labels,
        tuple(canonical),  # type: ignore[arg-type]
        channel,
    )


def _pair_channels(labels: tuple[int, int, int, int]) -> tuple[int, ...]:
    return tuple(
        sorted(
            set(fusion_labels(labels[0], labels[1]))
            & set(fusion_labels(labels[2], labels[3]))
        )
    )


def _shared_channel_records() -> tuple[
    tuple[PairLabels, PairLabels, int, Fraction],
    ...,
]:
    records: list[tuple[PairLabels, PairLabels, int, Fraction]] = []
    for residual_raw in product(range(2), repeat=2):
        residual = cast(PairLabels, residual_raw)
        for selected_raw in product(range(2), repeat=2):
            selected = cast(PairLabels, selected_raw)
            for output in sorted(
                set(fusion_labels(*residual))
                & set(fusion_labels(*selected))
            ):
                records.append(
                    (
                        residual,
                        selected,
                        output,
                        Fraction(1, output + 1),
                    )
                )
    return tuple(records)


def _matrix_transpose(matrix: RadicalMatrix) -> RadicalMatrix:
    return tuple(
        tuple(row[index] for row in matrix)
        for index in range(len(matrix[0]))
    )


def _matrix_product(
    left: RadicalMatrix,
    right: RadicalMatrix,
) -> RadicalMatrix:
    if not left or not right or len(left[0]) != len(right):
        raise ValueError("incompatible radical matrix dimensions")
    return tuple(
        tuple(
            _sum_radicals(
                tuple(
                    left[row][middle] * right[middle][column]
                    for middle in range(len(right))
                )
            )
            for column in range(len(right[0]))
        )
        for row in range(len(left))
    )


def _radical_identity(size: int) -> RadicalMatrix:
    return tuple(
        tuple(R_ONE if row == column else R_ZERO for column in range(size))
        for row in range(size)
    )


def _matrix_signature(matrix: RadicalMatrix) -> MatrixSignature:
    return tuple(
        tuple((value.coeff, value.rad) for value in row)
        for row in matrix
    )


def _pairing_transport_matrix(
    grouped_faces: tuple[int, int, int, int],
    canonical_faces: tuple[int, int, int, int],
    grouped_labels: tuple[int, int, int, int],
) -> tuple[tuple[int, ...], tuple[int, ...], RadicalMatrix]:
    """Exact overlap from grouped pair basis to canonical pair basis."""

    canonical_labels = cast(
        tuple[int, int, int, int],
        tuple(
            grouped_labels[grouped_faces.index(face)]
            for face in canonical_faces
        ),
    )
    grouped_channels = _pair_channels(grouped_labels)
    canonical_channels = _pair_channels(canonical_labels)
    rows: list[tuple[QuadRadical, ...]] = []
    for canonical_channel in canonical_channels:
        row: list[QuadRadical] = []
        for grouped_channel in grouped_channels:
            terms: list[QuadRadical] = []
            for canonical_magnetics_raw in product(
                *(magnetic_indices(label) for label in canonical_labels)
            ):
                canonical_magnetics = cast(
                    tuple[int, int, int, int],
                    canonical_magnetics_raw,
                )
                grouped_magnetics = cast(
                    tuple[int, int, int, int],
                    tuple(
                        canonical_magnetics[canonical_faces.index(face)]
                        for face in grouped_faces
                    ),
                )
                terms.append(
                    pair_pair_invariant_coefficient(
                        canonical_labels,
                        canonical_magnetics,
                        canonical_channel,
                    )
                    * pair_pair_invariant_coefficient(
                        grouped_labels,
                        grouped_magnetics,
                        grouped_channel,
                    )
                )
            row.append(_sum_radicals(tuple(terms)))
        rows.append(tuple(row))
    return canonical_channels, grouped_channels, tuple(rows)


def _trivalent_transport_phase(
    grouped_faces: tuple[int, int, int],
    canonical_faces: tuple[int, int, int],
    grouped_labels: tuple[int, int, int],
) -> QuadRadical:
    canonical_labels = cast(
        tuple[int, int, int],
        tuple(
            grouped_labels[grouped_faces.index(face)]
            for face in canonical_faces
        ),
    )
    terms: list[QuadRadical] = []
    for canonical_magnetics_raw in product(
        *(magnetic_indices(label) for label in canonical_labels)
    ):
        canonical_magnetics = cast(
            tuple[int, int, int],
            canonical_magnetics_raw,
        )
        grouped_magnetics = cast(
            tuple[int, int, int],
            tuple(
                canonical_magnetics[canonical_faces.index(face)]
                for face in grouped_faces
            ),
        )
        terms.append(
            cutoff_one_three_j_coefficient(
                canonical_labels,
                canonical_magnetics,
            )
            * cutoff_one_three_j_coefficient(
                grouped_labels,
                grouped_magnetics,
            )
        )
    return _sum_radicals(tuple(terms))


@dataclass(frozen=True, order=True)
class OrientedMatrixIncidence:
    """One raw matrix occurrence and its ket/bra contraction ports."""

    face_position: int
    face_id: int
    word_position: int
    word_length: int
    link: int
    orientation: int
    row_corner: CornerIndex
    column_corner: CornerIndex
    ket_corner: CornerIndex
    bra_corner: CornerIndex
    duality_required: bool

    def validates(self) -> bool:
        if (
            self.orientation not in (-1, 1)
            or self.word_length <= 0
            or self.word_position not in range(self.word_length)
        ):
            return False
        expected_row = (self.face_position, self.word_position)
        expected_column = (
            self.face_position,
            (self.word_position + 1) % self.word_length,
        )
        return (
            self.face_id == CONNECTED_CORE_FACE_IDS[self.face_position]
            and self.row_corner == expected_row
            and self.column_corner == expected_column
            and self.ket_corner
            == (expected_row if self.orientation == 1 else expected_column)
            and self.bra_corner
            == (expected_column if self.orientation == 1 else expected_row)
            and self.duality_required == (self.orientation == -1)
        )


@dataclass(frozen=True)
class FaceMagneticCycle:
    """Cyclic trace wire for one gauge-fixed residual face."""

    face_position: int
    face_id: int
    label_domain: tuple[int, ...]
    incidences: tuple[OrientedMatrixIncidence, ...]

    def validates(self) -> bool:
        return (
            self.face_id == CONNECTED_CORE_FACE_IDS[self.face_position]
            and self.label_domain == (0, 1)
            and len(self.incidences) > 0
            and all(item.validates() for item in self.incidences)
            and tuple(item.word_position for item in self.incidences)
            == tuple(range(len(self.incidences)))
            and all(
                item.face_position == self.face_position
                and item.word_length == len(self.incidences)
                for item in self.incidences
            )
        )


@dataclass(frozen=True)
class InternalTrivalentHaarNode:
    """Rank-one ket/bra Haar projector at one internal link."""

    link: int
    legs: tuple[
        OrientedMatrixIncidence,
        OrientedMatrixIncidence,
        OrientedMatrixIncidence,
    ]
    label_channels: tuple[tuple[int, int, int], ...]
    kraus_rank_per_channel: int

    def validates(self) -> bool:
        return (
            len(self.legs) == 3
            and tuple(sorted(self.legs)) == self.legs
            and all(leg.link == self.link for leg in self.legs)
            and self.label_channels
            == ((0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0))
            and all(
                invariant_multiplicity(labels) == 1
                for labels in self.label_channels
            )
            and self.kraus_rank_per_channel == 1
        )


@dataclass(frozen=True)
class ProtectedBoundaryCGNode:
    """Two residual legs fused to one open protected-link representation."""

    link: int
    legs: tuple[OrientedMatrixIncidence, OrientedMatrixIncidence]
    label_channels: tuple[tuple[int, int, int], ...]
    open_output_has_ket_and_bra_magnetic_indices: bool

    def validates(self) -> bool:
        return (
            len(self.legs) == 2
            and tuple(sorted(self.legs)) == self.legs
            and all(leg.link == self.link for leg in self.legs)
            and self.label_channels
            == (
                (0, 0, 0),
                (0, 1, 1),
                (1, 0, 1),
                (1, 1, 0),
                (1, 1, 2),
            )
            and all(
                output in fusion_labels(left, right)
                for left, right, output in self.label_channels
            )
            and self.open_output_has_ket_and_bra_magnetic_indices
        )


@dataclass(frozen=True, order=True)
class ExternalOrientedLeg:
    face_id: int
    orientation: int

    def validates(self) -> bool:
        return self.face_id >= 0 and self.orientation in (-1, 1)


@dataclass(frozen=True)
class PairingTransportBlock:
    """One exact local F/R block for a protected four-leg label assignment."""

    grouped_labels: tuple[int, int, int, int]
    canonical_labels: tuple[int, int, int, int]
    grouped_channels: tuple[int, ...]
    canonical_channels: tuple[int, ...]
    matrix: RadicalMatrix

    def validates(self) -> bool:
        return (
            all(label in (0, 1) for label in self.grouped_labels)
            and self.grouped_channels == _pair_channels(self.grouped_labels)
            and self.canonical_channels == _pair_channels(self.canonical_labels)
            and len(self.matrix) == len(self.canonical_channels)
            and all(
                len(row) == len(self.grouped_channels)
                for row in self.matrix
            )
            and len(self.grouped_channels) == len(self.canonical_channels)
            and _matrix_product(
                _matrix_transpose(self.matrix),
                self.matrix,
            )
            == _radical_identity(len(self.grouped_channels))
        )


@dataclass(frozen=True)
class CoreProtectedSharedChannelInterface:
    """Diagonal shared-``k`` gluing of residual and selected face pairs."""

    link: int
    residual_legs: tuple[ExternalOrientedLeg, ExternalOrientedLeg]
    selected_legs: tuple[ExternalOrientedLeg, ExternalOrientedLeg]
    grouped_face_order: tuple[int, int, int, int]
    canonical_face_order: tuple[int, int, int, int]
    shared_channel_records: tuple[
        tuple[tuple[int, int], tuple[int, int], int, Fraction],
        ...,
    ]
    transport_blocks: tuple[PairingTransportBlock, ...]

    def validates(self) -> bool:
        expected_records = _shared_channel_records()
        return (
            all(leg.validates() for leg in self.residual_legs)
            and all(leg.validates() for leg in self.selected_legs)
            and self.grouped_face_order
            == tuple(
                leg.face_id
                for leg in self.residual_legs + self.selected_legs
            )
            and self.canonical_face_order
            == tuple(sorted(self.grouped_face_order))
            and self.shared_channel_records == expected_records
            and len(self.transport_blocks) == 8
            and all(block.validates() for block in self.transport_blocks)
            and sum(
                len(block.grouped_channels)
                for block in self.transport_blocks
            )
            == 9
        )


@dataclass(frozen=True)
class DecorationSharedChannelInterface:
    """Selected pair fused to the label of one decoration face."""

    link: int
    selected_legs: tuple[ExternalOrientedLeg, ExternalOrientedLeg]
    residual_leg: ExternalOrientedLeg
    grouped_face_order: tuple[int, int, int]
    canonical_face_order: tuple[int, int, int]
    channel_records: tuple[
        tuple[tuple[int, int], int, Fraction, QuadRadical],
        ...,
    ]

    def validates(self) -> bool:
        return (
            all(leg.validates() for leg in self.selected_legs)
            and self.residual_leg.validates()
            and self.grouped_face_order
            == tuple(
                leg.face_id
                for leg in self.selected_legs + (self.residual_leg,)
            )
            and self.canonical_face_order
            == tuple(sorted(self.grouped_face_order))
            and len(self.channel_records) == 4
            and all(
                residual in fusion_labels(*selected)
                and weight == Fraction(1, residual + 1)
                and phase.square == 1
                for selected, residual, weight, phase in self.channel_records
            )
        )


def _selected_legs_at_link(
    link: int,
) -> tuple[ExternalOrientedLeg, ExternalOrientedLeg]:
    _complex, faces, _plaquettes = corrected_slab_haar_complex(1)
    selected_faces = tuple(
        sorted(
            face_id
            for corridor in CORRIDOR_FACE_IDS
            for face_id in corridor
        )
    )
    legs = tuple(
        ExternalOrientedLeg(face_id, orientation)
        for face_id in selected_faces
        for word_link, orientation in faces[face_id]
        if word_link == link
    )
    if len(legs) != 2:
        raise AssertionError("a protected link lost its two selected corridor legs")
    return legs


def _transport_blocks(
    grouped_faces: tuple[int, int, int, int],
    canonical_faces: tuple[int, int, int, int],
) -> tuple[PairingTransportBlock, ...]:
    blocks: list[PairingTransportBlock] = []
    for grouped_labels_raw in product(range(2), repeat=4):
        grouped_labels = cast(
            tuple[int, int, int, int],
            grouped_labels_raw,
        )
        if not _pair_channels(grouped_labels):
            continue
        canonical_labels = cast(
            tuple[int, int, int, int],
            tuple(
                grouped_labels[grouped_faces.index(face)]
                for face in canonical_faces
            ),
        )
        canonical_channels, grouped_channels, matrix = (
            _pairing_transport_matrix(
                grouped_faces,
                canonical_faces,
                grouped_labels,
            )
        )
        blocks.append(
            PairingTransportBlock(
                grouped_labels=grouped_labels,
                canonical_labels=canonical_labels,
                grouped_channels=grouped_channels,
                canonical_channels=canonical_channels,
                matrix=matrix,
            )
        )
    return tuple(blocks)


@dataclass(frozen=True)
class CutoffOneOpenIndexNetwork:
    """Structured global carrier with local tensors and open boundary indices."""

    representation_cutoff: int
    face_cycles: tuple[FaceMagneticCycle, ...]
    internal_nodes: tuple[InternalTrivalentHaarNode, ...]
    boundary_nodes: tuple[ProtectedBoundaryCGNode, ...]
    core_shared_interfaces: tuple[CoreProtectedSharedChannelInterface, ...]
    decoration_shared_interfaces: tuple[DecorationSharedChannelInterface, ...]
    magnetic_corner_count: int
    every_corner_has_degree_two: bool
    internal_orientation_signature_census: tuple[
        tuple[tuple[int, ...], int],
        ...,
    ]
    residual_boundary_orientation_signature_census: tuple[
        tuple[tuple[int, ...], int],
        ...,
    ]
    fixed_face_label_variables: int
    local_internal_channel_records: int
    local_boundary_channel_records: int
    complete_internal_assignment_count: int
    complete_boundary_channel_path_count: int
    rank_one_haar_kraus_factorization_pinned: bool
    open_boundary_cg_isometries_pinned: bool
    shared_channel_dimension_factors_pinned: bool
    signed_f_r_transport_pinned_at_cutoff_one: bool
    fundamental_frobenius_schur_indicator: int
    flat_global_path_table_materialized: bool
    physical_source_indexed_choi_contracted: bool
    cp_order_domination_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        incidences = tuple(
            incidence
            for cycle in self.face_cycles
            for incidence in cycle.incidences
        )
        return (
            self.representation_cutoff == 1
            and len(self.face_cycles) == 15
            and all(cycle.validates() for cycle in self.face_cycles)
            and len(incidences) == 33
            and len(self.internal_nodes) == 5
            and all(node.validates() for node in self.internal_nodes)
            and len(self.boundary_nodes) == 9
            and all(node.validates() for node in self.boundary_nodes)
            and len(self.core_shared_interfaces) == 9
            and all(
                interface.validates()
                for interface in self.core_shared_interfaces
            )
            and len(self.decoration_shared_interfaces) == 9
            and all(
                interface.validates()
                for interface in self.decoration_shared_interfaces
            )
            and self.magnetic_corner_count == 33
            and self.every_corner_has_degree_two
            and self.internal_orientation_signature_census
            == (
                ((-1, -1, -1), 1),
                ((-1, -1, 1), 1),
                ((1, -1, -1), 1),
                ((1, -1, 1), 1),
                ((1, 1, -1), 1),
            )
            and self.residual_boundary_orientation_signature_census
            == (((-1, -1), 3), ((-1, 1), 4), ((1, 1), 2))
            and self.fixed_face_label_variables == 15
            and self.local_internal_channel_records == 20
            and self.local_boundary_channel_records == 45
            and self.complete_internal_assignment_count == 1024
            and self.complete_boundary_channel_path_count == 10673
            and self.rank_one_haar_kraus_factorization_pinned
            and self.open_boundary_cg_isometries_pinned
            and self.shared_channel_dimension_factors_pinned
            and self.signed_f_r_transport_pinned_at_cutoff_one
            and self.fundamental_frobenius_schur_indicator == -1
            and not self.flat_global_path_table_materialized
            and not self.physical_source_indexed_choi_contracted
            and not self.cp_order_domination_proved
            and self.first_open_obligation
            == "contract-selected-and-residual-open-indices-in-one-pivotal-convention"
        )


def _build_face_cycles() -> tuple[FaceMagneticCycle, ...]:
    geometry = cutoff_one_core_geometry()
    cycles: list[FaceMagneticCycle] = []
    for face_position, (face_id, word) in enumerate(
        zip(CONNECTED_CORE_FACE_IDS, geometry.face_words, strict=True)
    ):
        word_length = len(word)
        incidences = tuple(
            OrientedMatrixIncidence(
                face_position=face_position,
                face_id=face_id,
                word_position=word_position,
                word_length=word_length,
                link=link,
                orientation=orientation,
                row_corner=(face_position, word_position),
                column_corner=(
                    face_position,
                    (word_position + 1) % word_length,
                ),
                ket_corner=(
                    (face_position, word_position)
                    if orientation == 1
                    else (
                        face_position,
                        (word_position + 1) % word_length,
                    )
                ),
                bra_corner=(
                    (
                        face_position,
                        (word_position + 1) % word_length,
                    )
                    if orientation == 1
                    else (face_position, word_position)
                ),
                duality_required=orientation == -1,
            )
            for word_position, (link, orientation) in enumerate(word)
        )
        cycles.append(
            FaceMagneticCycle(
                face_position=face_position,
                face_id=face_id,
                label_domain=(0, 1),
                incidences=incidences,
            )
        )
    return tuple(cycles)


def _incidences_by_link(
    cycles: tuple[FaceMagneticCycle, ...],
) -> dict[int, tuple[OrientedMatrixIncidence, ...]]:
    grouped: dict[int, list[OrientedMatrixIncidence]] = {}
    for cycle in cycles:
        for incidence in cycle.incidences:
            grouped.setdefault(incidence.link, []).append(incidence)
    return {
        link: tuple(sorted(incidences))
        for link, incidences in grouped.items()
    }


def _core_shared_interfaces() -> tuple[CoreProtectedSharedChannelInterface, ...]:
    geometry = cutoff_one_core_geometry()
    interfaces: list[CoreProtectedSharedChannelInterface] = []
    for link in geometry.protected_links:
        residual_legs = cast(
            tuple[ExternalOrientedLeg, ExternalOrientedLeg],
            tuple(
                ExternalOrientedLeg(
                    CONNECTED_CORE_FACE_IDS[position],
                    orientation,
                )
                for position, word in enumerate(geometry.face_words)
                for word_link, orientation in word
                if word_link == link
            ),
        )
        if len(residual_legs) != 2:
            raise AssertionError("a core protected link lost residual bivalence")
        selected_legs = _selected_legs_at_link(link)
        grouped_faces = cast(
            tuple[int, int, int, int],
            tuple(
                leg.face_id
                for leg in residual_legs + selected_legs
            ),
        )
        canonical_faces = cast(
            tuple[int, int, int, int],
            tuple(sorted(grouped_faces)),
        )
        interfaces.append(
            CoreProtectedSharedChannelInterface(
                link=link,
                residual_legs=residual_legs,
                selected_legs=selected_legs,
                grouped_face_order=grouped_faces,
                canonical_face_order=canonical_faces,
                shared_channel_records=_shared_channel_records(),
                transport_blocks=_transport_blocks(
                    grouped_faces,
                    canonical_faces,
                ),
            )
        )
    return tuple(interfaces)


def _decoration_shared_interfaces() -> (
    tuple[DecorationSharedChannelInterface, ...]
):
    geometry = cutoff_one_decoration_geometry()
    interfaces: list[DecorationSharedChannelInterface] = []
    for face_id, word in zip(
        DECORATION_FACE_IDS,
        geometry.face_words,
        strict=True,
    ):
        for link, residual_orientation in word:
            selected_legs = _selected_legs_at_link(link)
            residual_leg = ExternalOrientedLeg(
                face_id,
                residual_orientation,
            )
            grouped_faces = cast(
                tuple[int, int, int],
                tuple(
                    leg.face_id
                    for leg in selected_legs + (residual_leg,)
                ),
            )
            canonical_faces = cast(
                tuple[int, int, int],
                tuple(sorted(grouped_faces)),
            )
            records: list[
                tuple[
                    tuple[int, int],
                    int,
                    Fraction,
                    QuadRadical,
                ]
            ] = []
            for selected_raw in product(range(2), repeat=2):
                selected = cast(PairLabels, selected_raw)
                for residual in range(2):
                    labels = selected + (residual,)
                    if invariant_multiplicity(labels) != 1:
                        continue
                    records.append(
                        (
                            selected,
                            residual,
                            Fraction(1, residual + 1),
                            _trivalent_transport_phase(
                                grouped_faces,
                                canonical_faces,
                                labels,
                            ),
                        )
                    )
            interfaces.append(
                DecorationSharedChannelInterface(
                    link=link,
                    selected_legs=selected_legs,
                    residual_leg=residual_leg,
                    grouped_face_order=grouped_faces,
                    canonical_face_order=canonical_faces,
                    channel_records=tuple(records),
                )
            )
    return tuple(sorted(interfaces, key=lambda item: item.link))


def _local_coefficient_audit(
    internal_nodes: tuple[InternalTrivalentHaarNode, ...],
    boundary_nodes: tuple[ProtectedBoundaryCGNode, ...],
) -> tuple[bool, bool]:
    internal_normalized = True
    for internal_node in internal_nodes:
        orientations = cast(
            tuple[int, int, int],
            tuple(leg.orientation for leg in internal_node.legs),
        )
        for labels in internal_node.label_channels:
            squared_norm = sum(
                oriented_cutoff_one_three_j_coefficient(
                    labels,
                    cast(tuple[int, int, int], magnetics),
                    orientations,
                ).square
                for magnetics in product(
                    *(magnetic_indices(label) for label in labels)
                )
            )
            internal_normalized = internal_normalized and squared_norm == 1

    boundary_isometric = True
    for boundary_node in boundary_nodes:
        left_orientation, right_orientation = (
            leg.orientation for leg in boundary_node.legs
        )
        for left_label, right_label in product(range(2), repeat=2):
            inputs = tuple(
                product(
                    magnetic_indices(left_label),
                    magnetic_indices(right_label),
                )
            )
            for first in inputs:
                for second in inputs:
                    overlap_terms: list[QuadRadical] = []
                    for output in fusion_labels(left_label, right_label):
                        for output_magnetic in magnetic_indices(output):
                            overlap_terms.append(
                                oriented_cutoff_one_cg_coefficient(
                                    left_label,
                                    first[0],
                                    left_orientation,
                                    right_label,
                                    first[1],
                                    right_orientation,
                                    output,
                                    output_magnetic,
                                )
                                * oriented_cutoff_one_cg_coefficient(
                                    left_label,
                                    second[0],
                                    left_orientation,
                                    right_label,
                                    second[1],
                                    right_orientation,
                                    output,
                                    output_magnetic,
                                )
                            )
                    overlap = _sum_radicals(tuple(overlap_terms))
                    expected = R_ONE if first == second else R_ZERO
                    boundary_isometric = (
                        boundary_isometric and overlap == expected
                    )
    return internal_normalized, boundary_isometric


@cache
def cutoff_one_open_index_network() -> CutoffOneOpenIndexNetwork:
    """Build the exact structured magnetic-index contraction plan."""

    cycles = _build_face_cycles()
    by_link = _incidences_by_link(cycles)
    geometry = cutoff_one_core_geometry()
    internal_nodes = tuple(
        InternalTrivalentHaarNode(
            link=link,
            legs=by_link[link],  # type: ignore[arg-type]
            label_channels=(
                (0, 0, 0),
                (0, 1, 1),
                (1, 0, 1),
                (1, 1, 0),
            ),
            kraus_rank_per_channel=1,
        )
        for link in geometry.internal_links
    )
    boundary_nodes = tuple(
        ProtectedBoundaryCGNode(
            link=link,
            legs=by_link[link],  # type: ignore[arg-type]
            label_channels=(
                (0, 0, 0),
                (0, 1, 1),
                (1, 0, 1),
                (1, 1, 0),
                (1, 1, 2),
            ),
            open_output_has_ket_and_bra_magnetic_indices=True,
        )
        for link in geometry.protected_links
    )
    corner_degrees: Counter[CornerIndex] = Counter(
        corner
        for cycle in cycles
        for incidence in cycle.incidences
        for corner in (incidence.ket_corner, incidence.bra_corner)
    )
    internal_normalized, boundary_isometric = _local_coefficient_audit(
        internal_nodes,
        boundary_nodes,
    )
    core_interfaces = _core_shared_interfaces()
    decoration_interfaces = _decoration_shared_interfaces()
    network = CutoffOneOpenIndexNetwork(
        representation_cutoff=1,
        face_cycles=cycles,
        internal_nodes=internal_nodes,
        boundary_nodes=boundary_nodes,
        core_shared_interfaces=core_interfaces,
        decoration_shared_interfaces=decoration_interfaces,
        magnetic_corner_count=len(corner_degrees),
        every_corner_has_degree_two=(
            set(corner_degrees.values()) == {2}
        ),
        internal_orientation_signature_census=tuple(
            sorted(
                Counter(
                    tuple(leg.orientation for leg in node.legs)
                    for node in internal_nodes
                ).items()
            )
        ),
        residual_boundary_orientation_signature_census=tuple(
            sorted(
                Counter(
                    tuple(leg.orientation for leg in node.legs)
                    for node in boundary_nodes
                ).items()
            )
        ),
        fixed_face_label_variables=15,
        local_internal_channel_records=sum(
            len(node.label_channels)
            for node in internal_nodes
        ),
        local_boundary_channel_records=sum(
            len(node.label_channels)
            for node in boundary_nodes
        ),
        complete_internal_assignment_count=1024,
        complete_boundary_channel_path_count=10673,
        rank_one_haar_kraus_factorization_pinned=internal_normalized,
        open_boundary_cg_isometries_pinned=boundary_isometric,
        shared_channel_dimension_factors_pinned=all(
            record[3] == Fraction(1, record[2] + 1)
            for interface in core_interfaces
            for record in interface.shared_channel_records
        )
        and all(
            record[2] == Fraction(1, record[1] + 1)
            for interface in decoration_interfaces
            for record in interface.channel_records
        ),
        signed_f_r_transport_pinned_at_cutoff_one=all(
            block.validates()
            for interface in core_interfaces
            for block in interface.transport_blocks
        )
        and all(
            phase.square == 1
            for interface in decoration_interfaces
            for _selected, _residual, _weight, phase in interface.channel_records
        ),
        fundamental_frobenius_schur_indicator=sum(
            duality_coefficient(1, 1, middle)
            * duality_coefficient(1, middle, 1)
            for middle in magnetic_indices(1)
        ),
        flat_global_path_table_materialized=False,
        physical_source_indexed_choi_contracted=False,
        cp_order_domination_proved=False,
        first_open_obligation=(
            "contract-selected-and-residual-open-indices-in-one-pivotal-convention"
        ),
    )
    if not network.validates():
        raise AssertionError("the cutoff-one open-index network drifted")
    return network


def four_fundamental_transport_census() -> tuple[
    tuple[MatrixSignature, int],
    ...,
]:
    """Return the exact nine-interface census of the two-channel F/R block."""

    counter = Counter(
        _matrix_signature(
            next(
                block.matrix
                for block in interface.transport_blocks
                if block.grouped_labels == (1, 1, 1, 1)
            )
        )
        for interface in cutoff_one_open_index_network().core_shared_interfaces
    )
    return tuple(sorted(counter.items(), key=lambda item: repr(item[0])))
