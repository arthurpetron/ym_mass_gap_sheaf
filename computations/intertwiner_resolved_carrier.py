"""Intertwiner-resolved carrier data for corrected-slab surface families.

The older :mod:`computations.fusion_closed_surface_carrier` records only the
number of fusion paths ending in each face-spin assignment.  That is enough
to resum characters, but it is not enough to define a block map: distinct
paths can end in the same representation and are related by signed Racah
transport.

This module makes those paths first-class finite data.  It records

* a deterministic oriented ordering of the strand legs at every slab edge;
* every left- or right-associated face fusion path;
* every sequential invariant path at every edge; and
* the exact signed ``F`` matrix for three fundamental strands.

All representation labels are doubled spins.  No positivity claim is built
into the carrier.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Literal

from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.exact_haar_network import fusion_labels, invariant_multiplicity
from computations.fusion_closed_surface_carrier import (
    FusionClosedSurfaceFamily,
    FusionLedger,
    SpinAssignment,
    complete_fusion_ledger,
    face_strand_labels,
)
from computations.wigner_6j import QuadRadical, sixj_squared

Association = Literal["left", "right"]
RadicalMatrix = tuple[tuple[QuadRadical, ...], ...]


@dataclass(frozen=True, order=True)
class BoundaryLeg:
    """One canonically ordered oriented strand incidence at a slab edge."""

    strand_index: int
    face_index: int
    orientation: int
    label: int


@dataclass(frozen=True, order=True)
class FusionPath:
    """One sequential path through a multiplicity-free SU(2) fusion tree.

    ``intermediates[k]`` is the output after the first ``k + 2`` tensor
    factors.  Thus the final entry is the physical output label whenever the
    path contains at least two inputs.
    """

    labels: tuple[int, ...]
    output: int
    intermediates: tuple[int, ...]
    association: Association


@dataclass(frozen=True)
class FaceIntertwinerBasis:
    """Canonical fusion basis on one corrected-slab face."""

    face_index: int
    labels: tuple[int, ...]
    paths: tuple[FusionPath, ...]


@dataclass(frozen=True)
class EdgeIntertwinerBasis:
    """Canonical invariant basis for all strand legs incident at one edge."""

    edge_index: int
    legs: tuple[BoundaryLeg, ...]
    paths: tuple[FusionPath, ...]


@dataclass(frozen=True)
class ResolvedPathAssignment:
    """One basis choice on every face, before multiplicities are forgotten."""

    face_paths: tuple[FusionPath, ...]

    @property
    def outputs(self) -> SpinAssignment:
        return tuple(path.output for path in self.face_paths)


def sequential_fusion_paths(
    labels: Sequence[int],
    *,
    association: Association = "left",
    output: int | None = None,
) -> tuple[FusionPath, ...]:
    """Enumerate an exact sequential SU(2) fusion basis.

    A right-associated basis is represented by running the same deterministic
    recursion from the right.  The original label tuple remains attached to
    the path, so the association is explicit rather than inferred.
    """

    labels_tuple = tuple(labels)
    if any(label < 0 for label in labels_tuple):
        raise ValueError("doubled SU(2) labels must be nonnegative")
    if association not in ("left", "right"):
        raise ValueError("association must be 'left' or 'right'")
    ordered = labels_tuple if association == "left" else tuple(reversed(labels_tuple))
    paths: tuple[FusionPath, ...]
    if not ordered:
        paths = (FusionPath(labels_tuple, 0, (), association),)
    elif len(ordered) == 1:
        paths = (FusionPath(labels_tuple, ordered[0], (), association),)
    else:
        packet: list[tuple[int, tuple[int, ...]]] = [(ordered[0], ())]
        for label in ordered[1:]:
            following: list[tuple[int, tuple[int, ...]]] = []
            for intermediate, history in packet:
                for following_label in fusion_labels(intermediate, label):
                    following.append(
                        (following_label, history + (following_label,))
                    )
            packet = following
        paths = tuple(
            FusionPath(labels_tuple, final, history, association)
            for final, history in packet
        )
    if output is not None:
        paths = tuple(path for path in paths if path.output == output)
    return tuple(sorted(paths))


def invariant_fusion_paths(labels: Sequence[int]) -> tuple[FusionPath, ...]:
    """Return the canonical sequential basis of the invariant subspace."""

    return sequential_fusion_paths(labels, output=0)


def _edge_legs(
    family: FusionClosedSurfaceFamily,
) -> tuple[tuple[BoundaryLeg, ...], ...]:
    complex_, faces, _plaquettes = corrected_slab_haar_complex(family.extent)
    edge_legs: list[list[BoundaryLeg]] = [[] for _edge in complex_.edges]
    for strand_index, strand in enumerate(family.strands):
        for face_index, face in enumerate(faces):
            if not ((strand.mask >> face_index) & 1):
                continue
            for edge_index, orientation in face:
                edge_legs[edge_index].append(
                    BoundaryLeg(
                        strand_index,
                        face_index,
                        orientation,
                        strand.label,
                    )
                )
    return tuple(tuple(sorted(legs)) for legs in edge_legs)


@dataclass(frozen=True)
class IntertwinerResolvedFamily:
    """A surface family together with canonical face and edge bases."""

    family: FusionClosedSurfaceFamily
    face_bases: tuple[FaceIntertwinerBasis, ...]
    edge_bases: tuple[EdgeIntertwinerBasis, ...]

    @classmethod
    def build(
        cls,
        family: FusionClosedSurfaceFamily,
        *,
        association: Association = "left",
    ) -> IntertwinerResolvedFamily:
        labels_by_face = face_strand_labels(family)
        face_bases = tuple(
            FaceIntertwinerBasis(
                face_index,
                labels,
                sequential_fusion_paths(labels, association=association),
            )
            for face_index, labels in enumerate(labels_by_face)
        )
        edge_bases = tuple(
            EdgeIntertwinerBasis(
                edge_index,
                legs,
                invariant_fusion_paths(tuple(leg.label for leg in legs)),
            )
            for edge_index, legs in enumerate(_edge_legs(family))
        )
        resolved = cls(family, face_bases, edge_bases)
        resolved.validate()
        return resolved

    def validate(self) -> None:
        """Check that the resolved bases forget exactly to the old ledger."""

        if self.path_ledger() != complete_fusion_ledger(self.family):
            raise AssertionError("resolved paths do not forget to the fusion ledger")
        for basis in self.edge_bases:
            labels = tuple(leg.label for leg in basis.legs)
            if len(basis.paths) != invariant_multiplicity(labels):
                raise AssertionError(
                    f"edge {basis.edge_index} invariant basis has wrong dimension"
                )

    def path_assignments(self) -> tuple[ResolvedPathAssignment, ...]:
        """Enumerate all explicit face fusion paths in the selected family."""

        return tuple(
            ResolvedPathAssignment(tuple(paths))
            for paths in product(*(basis.paths for basis in self.face_bases))
        )

    def path_ledger(self) -> FusionLedger:
        """Forget path indices while retaining their exact multiplicities."""

        ledger: FusionLedger = {}
        for resolved in self.path_assignments():
            ledger[resolved.outputs] = ledger.get(resolved.outputs, 0) + 1
        return ledger

    @property
    def fusion_path_count(self) -> int:
        count = 1
        for basis in self.face_bases:
            count *= len(basis.paths)
        return count

    @property
    def edge_invariant_dimensions(self) -> tuple[int, ...]:
        return tuple(len(basis.paths) for basis in self.edge_bases)


def fundamental_exchange_phase(channel: int) -> int:
    """Classical SU(2) swap phase on ``1/2 tensor 1/2``.

    The singlet is antisymmetric and the triplet is symmetric.  This is the
    ``q -> 1`` ordering datum used by the carrier; it is not a braided
    finite-level ``R`` symbol.
    """

    if channel == 0:
        return -1
    if channel == 2:
        return 1
    raise ValueError("two fundamental strands fuse only through labels 0 or 2")


def triple_fundamental_f_matrix(total_label: int) -> RadicalMatrix:
    """Exact signed Racah transport for three fundamental representations.

    Rows are left channels and columns are right channels.  For total doubled
    spin one the channel order is ``(0, 2)``; for total doubled spin three it
    is ``(2,)``.  The convention is

    ``F[e,f] = (-1)^(j1+j2+j3+J) sqrt((2e+1)(2f+1)) {j1 j2 e; j3 J f}``.
    """

    if total_label not in (1, 3):
        raise ValueError("three fundamentals have total doubled label 1 or 3")
    channels = (0, 2) if total_label == 1 else (2,)
    phase_exponent = Fraction(3 + total_label, 2)
    if phase_exponent.denominator != 1:
        raise AssertionError("Racah phase must have an integral exponent")
    phase = (-1) ** int(phase_exponent)
    rows: list[tuple[QuadRadical, ...]] = []
    for left_channel in channels:
        row: list[QuadRadical] = []
        for right_channel in channels:
            symbol = sixj_squared(
                Fraction(1, 2),
                Fraction(1, 2),
                Fraction(left_channel, 2),
                Fraction(1, 2),
                Fraction(total_label, 2),
                Fraction(right_channel, 2),
            )
            row.append(
                QuadRadical.from_coeff_radicand(
                    Fraction(phase * symbol.sign),
                    symbol.square
                    * (left_channel + 1)
                    * (right_channel + 1),
                )
            )
        rows.append(tuple(row))
    return tuple(rows)


def radical_matrix_transpose(matrix: RadicalMatrix) -> RadicalMatrix:
    return tuple(tuple(row[index] for row in matrix) for index in range(len(matrix)))


def radical_matrix_product(
    left: RadicalMatrix,
    right: RadicalMatrix,
) -> RadicalMatrix:
    if not left or not right or len(left[0]) != len(right):
        raise ValueError("incompatible radical matrix dimensions")
    return tuple(
        tuple(
            sum(
                (left[row][middle] * right[middle][column]
                 for middle in range(len(right))),
                start=QuadRadical.zero(),
            )
            for column in range(len(right[0]))
        )
        for row in range(len(left))
    )


def radical_identity(size: int) -> RadicalMatrix:
    return tuple(
        tuple(
            QuadRadical(Fraction(1), 1)
            if row == column
            else QuadRadical.zero()
            for column in range(size)
        )
        for row in range(size)
    )


@dataclass(frozen=True)
class TripleRecouplingAudit:
    """Exact coherence certificate for the first multiplicity-bearing face."""

    total_one_matrix: RadicalMatrix
    total_three_matrix: RadicalMatrix
    singlet_exchange_phase: int
    triplet_exchange_phase: int

    def validates(self) -> bool:
        return (
            radical_matrix_product(
                self.total_one_matrix,
                radical_matrix_transpose(self.total_one_matrix),
            )
            == radical_identity(2)
            and radical_matrix_product(
                self.total_three_matrix,
                radical_matrix_transpose(self.total_three_matrix),
            )
            == radical_identity(1)
            and self.singlet_exchange_phase == -1
            and self.triplet_exchange_phase == 1
        )


def triple_recoupling_audit() -> TripleRecouplingAudit:
    return TripleRecouplingAudit(
        total_one_matrix=triple_fundamental_f_matrix(1),
        total_three_matrix=triple_fundamental_f_matrix(3),
        singlet_exchange_phase=fundamental_exchange_phase(0),
        triplet_exchange_phase=fundamental_exchange_phase(2),
    )
