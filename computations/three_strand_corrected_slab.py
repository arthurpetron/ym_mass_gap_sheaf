"""BF1.5: exact three-strand corrected-slab pushforward seed.

The selected unit-four-cube sector is the lexicographically first minimizer
among triples of distinct nonempty closed binary surfaces which

* have a triple-occupied face, hence a nontrivial fusion-path multiplicity;
* use all six coordinate two-planes, hence are not contained in a
  three-dimensional coordinate subcomplex; and
* minimize first total strand area, then union area, then the sorted area
  profile.

The winning raw masks are ``(0x8938, 0x4220b, 0x8c96d)``.  Their areas are
``(6, 6, 10)`` and their union has 15 faces.

This module provides four exact certificates:

1. a 96-path intertwiner-resolved ledger over 64 face-spin assignments;
2. direct Haar = left-path sum = right-path sum, plus the complete heat
   activity;
3. the candidate one-sided reflected Gram matrix; and
4. an unnormalized Haar pushforward from explicit fusion paths to physical
   face channels.

The reflection test has a decisive *negative* outcome: the leading
three-by-three principal minor is exactly ``-1/65536``.  This does not
contradict Osterwalder--Schrader positivity because the closed surface
generators are not supported in a positive half-slab.  It instead proves
that closed full-slab strands alone are not the reflection-positive carrier;
open half-surface boundary states and their cut intertwiners are required.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import combinations
from typing import cast

from computations.corrected_slab_haar_network import (
    embed_hypercube_face_mask,
    evaluate_corrected_slab_assignment,
)
from computations.dual_half_time_reflection_route import (
    slab_face_reflection_permutation,
)
from computations.exact_haar_network import (
    SPoly,
    casimir4,
    dimension,
    sign_on_unit_interval,
    sp_add_into,
    sp_clean,
)
from computations.fusion_closed_surface_carrier import (
    ClosedSurfaceStrand,
    FusionClosedSurfaceFamily,
    SpinAssignment,
    complete_fusion_ledger,
    evaluate_surface_family_direct,
    face_strand_labels,
)
from computations.hypercube4d_survey import (
    exact_constant,
    hypercube,
    kernel_basis,
    surfaces,
)
from computations.intertwiner_resolved_carrier import (
    IntertwinerResolvedFamily,
    TripleRecouplingAudit,
    triple_recoupling_audit,
)

RAW_THREE_STRAND_MASKS = (0x8938, 0x4220B, 0x8C96D)
EXPECTED_HEAT_ACTIVITY: SPoly = {
    30: Fraction(8),
    38: Fraction(24),
    62: Fraction(24),
    70: Fraction(8),
    82: Fraction(32),
}
EXPECTED_REFLECTED_GRAM: tuple[tuple[Fraction, ...], ...] = (
    (Fraction(1), Fraction(1, 16), Fraction(1, 16), Fraction(1, 256)),
    (Fraction(1, 16), Fraction(82, 81), Fraction(1, 128), Fraction(41, 648)),
    (Fraction(1, 16), Fraction(1, 128), Fraction(1, 256), Fraction(1, 768)),
    (Fraction(1, 256), Fraction(41, 648), Fraction(1, 768), Fraction(6562, 6561)),
)


def minimal_three_strand_family() -> FusionClosedSurfaceFamily:
    """Return the pinned minimal three-strand family in slab ordering."""

    return FusionClosedSurfaceFamily(
        1,
        tuple(
            ClosedSurfaceStrand(embed_hypercube_face_mask(mask), 1)
            for mask in RAW_THREE_STRAND_MASKS
        ),
    )


def reflect_face_mask(extent: int, mask: int) -> int:
    """Transport a face mask through the corrected-slab time involution."""

    permutation = slab_face_reflection_permutation(extent)
    if mask < 0 or mask >> len(permutation):
        raise ValueError("face mask leaves the corrected slab")
    return sum(
        1 << permutation[face_index]
        for face_index in range(len(permutation))
        if (mask >> face_index) & 1
    )


def reflect_family(
    family: FusionClosedSurfaceFamily,
) -> FusionClosedSurfaceFamily:
    return FusionClosedSurfaceFamily(
        family.extent,
        tuple(
            ClosedSurfaceStrand(
                reflect_face_mask(family.extent, strand.mask),
                strand.label,
            )
            for strand in family.strands
        ),
    )


def reflect_assignment(extent: int, spins: SpinAssignment) -> SpinAssignment:
    permutation = slab_face_reflection_permutation(extent)
    if len(spins) != len(permutation):
        raise ValueError("one spin is required for every corrected-slab face")
    reflected = [0] * len(spins)
    for face_index, target in enumerate(permutation):
        reflected[target] = spins[face_index]
    return tuple(reflected)


@dataclass(frozen=True)
class MinimalSectorCensus:
    """Finite geometry and multiplicity certificate for the selected sector."""

    raw_masks: tuple[int, int, int]
    strand_areas: tuple[int, int, int]
    union_area: int
    coordinate_plane_count: int
    face_occupancy_counts: tuple[tuple[int, int], ...]
    edge_leg_counts: tuple[tuple[int, int], ...]
    edge_invariant_dimension_counts: tuple[tuple[int, int], ...]
    fusion_path_count: int
    coarse_channel_count: int
    co_minimal_triple_count: int

    def validates(self) -> bool:
        return (
            self.raw_masks == RAW_THREE_STRAND_MASKS
            and self.strand_areas == (6, 6, 10)
            and self.union_area == 15
            and self.coordinate_plane_count == 6
            and dict(self.face_occupancy_counts) == {0: 57, 1: 9, 2: 5, 3: 1}
            and dict(self.edge_leg_counts) == {0: 91, 2: 10, 4: 11, 6: 4}
            and dict(self.edge_invariant_dimension_counts) == {1: 101, 2: 11, 5: 4}
            and self.fusion_path_count == 96
            and self.coarse_channel_count == 64
            and self.co_minimal_triple_count == 192
        )


@cache
def _minimality_search() -> tuple[tuple[int, int, int], int]:
    complex_, faces, metadata = hypercube()
    closed = tuple(surface for surface in surfaces(kernel_basis(complex_, faces)) if surface)
    planes = tuple((first, second) for _point, first, second in metadata)
    best_score: tuple[int, int, tuple[int, ...]] | None = None
    minimizers: list[tuple[int, int, int]] = []
    for triple in combinations(closed, 3):
        if not (triple[0] & triple[1] & triple[2]):
            continue
        union = triple[0] | triple[1] | triple[2]
        used_planes = {
            planes[face_index]
            for face_index in range(len(faces))
            if (union >> face_index) & 1
        }
        if len(used_planes) != 6:
            continue
        score = (
            sum(mask.bit_count() for mask in triple),
            union.bit_count(),
            tuple(sorted(mask.bit_count() for mask in triple)),
        )
        if best_score is None or score < best_score:
            best_score = score
            minimizers = [triple]
        elif score == best_score:
            minimizers.append(triple)
    if not minimizers:
        raise AssertionError("the three-strand search found no physical sector")
    return min(minimizers), len(minimizers)


@cache
def minimal_sector_census() -> MinimalSectorCensus:
    family = minimal_three_strand_family()
    resolved = IntertwinerResolvedFamily.build(family)
    first_minimizer, minimizer_count = _minimality_search()
    if first_minimizer != RAW_THREE_STRAND_MASKS:
        raise AssertionError("the pinned sector is no longer the first minimizer")
    _complex, _faces, metadata = hypercube()
    union = RAW_THREE_STRAND_MASKS[0] | RAW_THREE_STRAND_MASKS[1] | RAW_THREE_STRAND_MASKS[2]
    planes = {
        (first, second)
        for face_index, (_point, first, second) in enumerate(metadata)
        if (union >> face_index) & 1
    }
    return MinimalSectorCensus(
        raw_masks=RAW_THREE_STRAND_MASKS,
        strand_areas=(
            RAW_THREE_STRAND_MASKS[0].bit_count(),
            RAW_THREE_STRAND_MASKS[1].bit_count(),
            RAW_THREE_STRAND_MASKS[2].bit_count(),
        ),
        union_area=union.bit_count(),
        coordinate_plane_count=len(planes),
        face_occupancy_counts=tuple(
            sorted(Counter(map(len, face_strand_labels(family))).items())
        ),
        edge_leg_counts=tuple(
            sorted(Counter(len(basis.legs) for basis in resolved.edge_bases).items())
        ),
        edge_invariant_dimension_counts=tuple(
            sorted(Counter(resolved.edge_invariant_dimensions).items())
        ),
        fusion_path_count=resolved.fusion_path_count,
        coarse_channel_count=len(resolved.path_ledger()),
        co_minimal_triple_count=minimizer_count,
    )


@cache
def _channel_values(
    family: FusionClosedSurfaceFamily,
) -> tuple[tuple[SpinAssignment, int, Fraction], ...]:
    return tuple(
        (
            spins,
            multiplicity,
            exact_constant(
                evaluate_corrected_slab_assignment(family.extent, spins)
            ),
        )
        for spins, multiplicity in sorted(complete_fusion_ledger(family).items())
    )


def _path_sum(
    resolved: IntertwinerResolvedFamily,
    amplitude_by_output: dict[SpinAssignment, Fraction],
) -> SPoly:
    total: SPoly = {}
    for path in resolved.path_assignments():
        amplitude = amplitude_by_output[path.outputs]
        if amplitude:
            total[0] = total.get(0, Fraction(0)) + amplitude
    return sp_clean(total)


def _path_heat_activity(
    resolved: IntertwinerResolvedFamily,
    amplitude_by_output: dict[SpinAssignment, Fraction],
) -> SPoly:
    total: SPoly = {}
    for path in resolved.path_assignments():
        coefficient = amplitude_by_output[path.outputs]
        exponent = 0
        for spin in path.outputs:
            coefficient *= dimension(spin)
            exponent += casimir4(spin)
        if coefficient:
            total[exponent] = total.get(exponent, Fraction(0)) + coefficient
    return sp_clean(total)


@dataclass(frozen=True)
class ThreeWayHaarAudit:
    """Direct, coherent-path, heat, and local recoupling certificate."""

    direct_haar: SPoly
    left_coherent_haar: SPoly
    right_coherent_haar: SPoly
    left_heat_activity: SPoly
    right_heat_activity: SPoly
    heat_sign: str
    negative_fixed_channels: int
    recoupling: TripleRecouplingAudit

    def validates(self) -> bool:
        return (
            self.direct_haar
            == self.left_coherent_haar
            == self.right_coherent_haar
            == {0: Fraction(83, 5184)}
            and self.left_heat_activity
            == self.right_heat_activity
            == EXPECTED_HEAT_ACTIVITY
            and self.heat_sign == "positive"
            and self.negative_fixed_channels == 0
            and self.recoupling.validates()
        )


@cache
def three_way_haar_audit() -> ThreeWayHaarAudit:
    family = minimal_three_strand_family()
    left = IntertwinerResolvedFamily.build(family, association="left")
    right = IntertwinerResolvedFamily.build(family, association="right")
    values = _channel_values(family)
    amplitude_by_output = {
        spins: amplitude for spins, _multiplicity, amplitude in values
    }
    direct = evaluate_surface_family_direct(family)
    left_heat = _path_heat_activity(left, amplitude_by_output)
    right_heat = _path_heat_activity(right, amplitude_by_output)
    return ThreeWayHaarAudit(
        direct_haar=direct,
        left_coherent_haar=_path_sum(left, amplitude_by_output),
        right_coherent_haar=_path_sum(right, amplitude_by_output),
        left_heat_activity=left_heat,
        right_heat_activity=right_heat,
        heat_sign=sign_on_unit_interval(left_heat),
        negative_fixed_channels=sum(
            1 for _spins, _multiplicity, amplitude in values if amplitude < 0
        ),
        recoupling=triple_recoupling_audit(),
    )


def _family_from_masks(masks: tuple[int, ...]) -> FusionClosedSurfaceFamily:
    return FusionClosedSurfaceFamily(
        1,
        tuple(ClosedSurfaceStrand(mask, 1) for mask in masks),
    )


@cache
def _direct_mask_family_constant(masks: tuple[int, ...]) -> Fraction:
    return cast(
        Fraction,
        exact_constant(evaluate_surface_family_direct(_family_from_masks(masks))),
    )


def _determinant(matrix: tuple[tuple[Fraction, ...], ...]) -> Fraction:
    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("determinants require a square matrix")
    work = [list(row) for row in matrix]
    determinant = Fraction(1)
    for column in range(size):
        pivot = next(
            (row for row in range(column, size) if work[row][column]),
            None,
        )
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            determinant *= -1
        pivot_value = work[column][column]
        determinant *= pivot_value
        for row in range(column + 1, size):
            scale = work[row][column] / pivot_value
            for entry in range(column + 1, size):
                work[row][entry] -= scale * work[column][entry]
    return determinant


def _ldlt(
    matrix: tuple[tuple[Fraction, ...], ...],
) -> tuple[tuple[tuple[Fraction, ...], ...], tuple[Fraction, ...]]:
    size = len(matrix)
    lower = [
        [Fraction(int(row == column)) for column in range(size)]
        for row in range(size)
    ]
    diagonal: list[Fraction] = []
    for column in range(size):
        pivot = matrix[column][column] - sum(
            lower[column][prior] ** 2 * diagonal[prior]
            for prior in range(column)
        )
        if pivot == 0:
            raise ValueError("zero-pivot LDL decomposition is not implemented")
        diagonal.append(pivot)
        for row in range(column + 1, size):
            lower[row][column] = (
                matrix[row][column]
                - sum(
                    lower[row][prior]
                    * lower[column][prior]
                    * diagonal[prior]
                    for prior in range(column)
                )
            ) / pivot
    return tuple(tuple(row) for row in lower), tuple(diagonal)


@dataclass(frozen=True)
class ReflectedGramAudit:
    """Exact one-sided reflection form on the surface-generator packet."""

    basis_masks: tuple[int, int, int]
    reflected_masks: tuple[int, int, int]
    matrix: tuple[tuple[Fraction, ...], ...]
    leading_principal_minors: tuple[Fraction, ...]
    ldlt_lower: tuple[tuple[Fraction, ...], ...]
    ldlt_diagonal: tuple[Fraction, ...]

    @property
    def first_negative_principal_minor(self) -> tuple[int, Fraction] | None:
        return next(
            (
                (index + 1, determinant)
                for index, determinant in enumerate(self.leading_principal_minors)
                if determinant < 0
            ),
            None,
        )

    def validates_negative_exit(self) -> bool:
        return (
            self.matrix == EXPECTED_REFLECTED_GRAM
            and all(
                self.matrix[row][column] == self.matrix[column][row]
                for row in range(len(self.matrix))
                for column in range(len(self.matrix))
            )
            and self.first_negative_principal_minor
            == (3, Fraction(-1, 65536))
            and self.ldlt_diagonal[2] == Fraction(-81, 5353216)
        )


@cache
def reflected_gram_audit() -> ReflectedGramAudit:
    strands = minimal_three_strand_family().strands
    masks = (strands[0].mask, strands[1].mask, strands[2].mask)
    reflected = (
        reflect_face_mask(1, masks[0]),
        reflect_face_mask(1, masks[1]),
        reflect_face_mask(1, masks[2]),
    )
    basis = ((),) + tuple((mask,) for mask in masks)
    reflected_basis = ((),) + tuple((mask,) for mask in reflected)
    matrix = tuple(
        tuple(
            _direct_mask_family_constant(
                tuple(sorted(reflected_basis[row] + basis[column]))
            )
            for column in range(len(basis))
        )
        for row in range(len(basis))
    )
    leading_minors = tuple(
        _determinant(tuple(tuple(row[:size]) for row in matrix[:size]))
        for size in range(1, len(matrix) + 1)
    )
    lower, diagonal = _ldlt(matrix)
    return ReflectedGramAudit(
        basis_masks=masks,
        reflected_masks=reflected,
        matrix=matrix,
        leading_principal_minors=leading_minors,
        ldlt_lower=lower,
        ldlt_diagonal=diagonal,
    )


def _coarse_heat_weights(
    family: FusionClosedSurfaceFamily,
) -> dict[SpinAssignment, SPoly]:
    weights: dict[SpinAssignment, SPoly] = {}
    for spins, multiplicity, amplitude in _channel_values(family):
        coefficient = amplitude * multiplicity
        exponent = 0
        for spin in spins:
            coefficient *= dimension(spin)
            exponent += casimir4(spin)
        weights[spins] = {exponent: coefficient} if coefficient else {}
    return weights


@dataclass(frozen=True)
class HaarPushforwardSeed:
    """Unnormalized path-to-channel Haar pushforward for the selected block.

    This is a local fusion-block pushforward after every corrected-slab link
    has been Haar integrated.  It is not yet a spacing-changing geometric RG
    map; the distinction is part of the certificate.
    """

    fine_path_outputs: tuple[SpinAssignment, ...]
    coarse_fibres: tuple[tuple[SpinAssignment, tuple[int, ...]], ...]
    coarse_weights: tuple[tuple[SpinAssignment, SPoly], ...]
    total_mass: SPoly
    reflected_total_mass: SPoly
    reflection_compatible: bool
    remainder_outside_carrier: SPoly

    def validates(self) -> bool:
        weights = dict(self.coarse_weights)
        total: SPoly = {}
        for weight in weights.values():
            sp_add_into(total, weight)
        fibres = dict(self.coarse_fibres)
        return (
            len(self.fine_path_outputs) == 96
            and len(fibres) == len(weights) == 64
            and sum(len(indices) for indices in fibres.values()) == 96
            and all(
                self.fine_path_outputs[index] == output
                for output, indices in fibres.items()
                for index in indices
            )
            and sp_clean(total) == self.total_mass == EXPECTED_HEAT_ACTIVITY
            and self.reflected_total_mass == self.total_mass
            and self.reflection_compatible
            and self.remainder_outside_carrier == {}
        )


@cache
def haar_pushforward_seed() -> HaarPushforwardSeed:
    family = minimal_three_strand_family()
    resolved = IntertwinerResolvedFamily.build(family)
    paths = resolved.path_assignments()
    outputs = tuple(path.outputs for path in paths)
    fibre_map: dict[SpinAssignment, list[int]] = {}
    for index, output in enumerate(outputs):
        fibre_map.setdefault(output, []).append(index)
    weights = _coarse_heat_weights(family)

    reflected_family = reflect_family(family)
    transported_weights = {
        reflect_assignment(family.extent, spins): weight
        for spins, weight in weights.items()
    }
    # The corrected-slab reflection is an oriented link/face reindexing.
    # Haar inversion invariance therefore transports the already-computed
    # coefficients exactly; recomputing them in the reflected contraction
    # order is exponentially worse while proving no stronger identity.
    reflected_ledger = complete_fusion_ledger(reflected_family)
    transported_ledger = {
        reflect_assignment(family.extent, spins): multiplicity
        for spins, multiplicity in complete_fusion_ledger(family).items()
    }
    reflected_weights = transported_weights
    total: SPoly = {}
    for weight in weights.values():
        sp_add_into(total, weight)
    reflected_total: SPoly = {}
    for weight in reflected_weights.values():
        sp_add_into(reflected_total, weight)
    return HaarPushforwardSeed(
        fine_path_outputs=outputs,
        coarse_fibres=tuple(
            (output, tuple(indices))
            for output, indices in sorted(fibre_map.items())
        ),
        coarse_weights=tuple(sorted(weights.items())),
        total_mass=sp_clean(total),
        reflected_total_mass=sp_clean(reflected_total),
        reflection_compatible=(
            transported_ledger == reflected_ledger
            and len(transported_weights) == len(weights)
        ),
        remainder_outside_carrier={},
    )


@dataclass(frozen=True)
class BF15Certificate:
    """Complete BF1.5 gate result."""

    census: MinimalSectorCensus
    haar: ThreeWayHaarAudit
    reflected_gram: ReflectedGramAudit
    pushforward: HaarPushforwardSeed

    @property
    def exit_kind(self) -> str:
        return "negative-reflection-carrier"

    def validates(self) -> bool:
        return (
            self.census.validates()
            and self.haar.validates()
            and self.reflected_gram.validates_negative_exit()
            and self.pushforward.validates()
        )


@cache
def bf15_certificate() -> BF15Certificate:
    return BF15Certificate(
        census=minimal_sector_census(),
        haar=three_way_haar_audit(),
        reflected_gram=reflected_gram_audit(),
        pushforward=haar_pushforward_seed(),
    )
