"""BF4: the dimension-free reference-order cone and its physical frontier.

The positive trace-class cone found in BF2 is the correct *order carrier*,
but it is too large to be the quantitative Birkhoff cone at infinite
representation cutoff.  In trace norm that cone has empty interior: the
eigenvalues of every positive trace-class reference tend to zero, so an
arbitrarily small rank-one subtraction eventually leaves the cone.

The quantitative replacement is a reference-order (Doeblin) cone.  Fix a
faithful positive reference kernel ``R`` of trace one.  If every normalized
output ``X`` of a physical block satisfies

    alpha R <= X <= beta R,

then any two outputs obey

    (alpha / beta) Y <= X <= (beta / alpha) Y.

Their Hilbert projective distance is at most
``2 log(beta / alpha)``, and Birkhoff--Hopf gives the dimension-free rate

    q <= (beta - alpha) / (beta + alpha).

This module checks the Loewner inequalities in exact rational arithmetic for
finite witness families and records the theorem's fail-closed physical
frontier.  It does not assert the missing universal minorization for the
all-label Yang--Mills block.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from typing import TypeAlias

from computations.all_label_whole_slab_tail import (
    WHOLE_SLAB_FACE_COUNT,
    bf32_all_label_frontier,
    heat_character_sup_term,
    jacobi_heat_kernel_floor,
    single_plaquette_all_label_tail,
)
from computations.bf3_3_birkhoff_handoff import (
    whole_slab_density_handoff_audit,
)
from computations.general_reflection_cut_carrier import exact_ldlt

RationalMatrix: TypeAlias = tuple[tuple[Fraction, ...], ...]


def _matrix(values: tuple[tuple[int | Fraction, ...], ...]) -> RationalMatrix:
    matrix = tuple(tuple(Fraction(value) for value in row) for row in values)
    if not matrix or any(len(row) != len(matrix) for row in matrix):
        raise ValueError("a Loewner-order witness must be a nonempty square matrix")
    if any(
        matrix[row][column] != matrix[column][row]
        for row in range(len(matrix))
        for column in range(len(matrix))
    ):
        raise ValueError("a Loewner-order witness must be symmetric")
    return matrix


def _trace(matrix: RationalMatrix) -> Fraction:
    return sum(
        (matrix[index][index] for index in range(len(matrix))),
        start=Fraction(0),
    )


def _scale(scale: Fraction, matrix: RationalMatrix) -> RationalMatrix:
    return tuple(
        tuple(scale * value for value in row)
        for row in matrix
    )


def _subtract(left: RationalMatrix, right: RationalMatrix) -> RationalMatrix:
    if len(left) != len(right):
        raise ValueError("matrix dimensions do not match")
    return tuple(
        tuple(
            left[row][column] - right[row][column]
            for column in range(len(left))
        )
        for row in range(len(left))
    )


def _is_psd(matrix: RationalMatrix) -> bool:
    return exact_ldlt(matrix).is_psd


def _is_positive_definite(matrix: RationalMatrix) -> bool:
    factor = exact_ldlt(matrix)
    return all(pivot > 0 for pivot in factor.diagonal)


def _normalized(matrix: RationalMatrix) -> RationalMatrix:
    mass = _trace(matrix)
    if mass <= 0:
        raise ValueError("a normalized positive output must have positive trace")
    return _scale(Fraction(1, 1) / mass, matrix)


@dataclass(frozen=True)
class ReferenceOrderEnvelope:
    """Exact finite-family witness for a dimension-free Doeblin envelope."""

    reference: RationalMatrix
    outputs: tuple[RationalMatrix, ...]
    lower: Fraction
    upper: Fraction
    projective_spread: Fraction
    birkhoff_rate_bound: Fraction
    dimension_free_formula: bool
    scope: str

    def validates(self) -> bool:
        try:
            reference = _matrix(self.reference)
            outputs = tuple(_matrix(output) for output in self.outputs)
            normalized = tuple(_normalized(output) for output in outputs)
        except (ValueError, ArithmeticError):
            return False
        if (
            not outputs
            or any(len(output) != len(reference) for output in outputs)
            or _trace(reference) != 1
            or not _is_positive_definite(reference)
            or not all(_is_psd(output) for output in outputs)
            or not 0 < self.lower <= 1 <= self.upper
        ):
            return False

        lower_reference = _scale(self.lower, reference)
        upper_reference = _scale(self.upper, reference)
        if not all(
            _is_psd(_subtract(output, lower_reference))
            and _is_psd(_subtract(upper_reference, output))
            for output in normalized
        ):
            return False

        spread = self.upper / self.lower
        pair_lower = self.lower / self.upper
        if not all(
            _is_psd(_subtract(first, _scale(pair_lower, second)))
            and _is_psd(_subtract(_scale(spread, second), first))
            for first in normalized
            for second in normalized
        ):
            return False
        return (
            self.projective_spread == spread
            and self.birkhoff_rate_bound
            == (spread - 1) / (spread + 1)
            == (self.upper - self.lower) / (self.upper + self.lower)
            and 0 <= self.birkhoff_rate_bound < 1
            and self.dimension_free_formula
            and self.scope == "finite-output-family-not-universal-physical-map"
        )


def reference_order_envelope(
    reference: tuple[tuple[int | Fraction, ...], ...],
    outputs: tuple[tuple[tuple[int | Fraction, ...], ...], ...],
    lower: Fraction,
    upper: Fraction,
) -> ReferenceOrderEnvelope:
    """Check a finite family against one exact reference-order envelope."""

    rational_reference = _matrix(reference)
    rational_outputs = tuple(_matrix(output) for output in outputs)
    if lower <= 0:
        raise ValueError("the reference lower constant must be positive")
    spread = upper / lower
    certificate = ReferenceOrderEnvelope(
        reference=rational_reference,
        outputs=rational_outputs,
        lower=lower,
        upper=upper,
        projective_spread=spread,
        birkhoff_rate_bound=(spread - 1) / (spread + 1),
        dimension_free_formula=True,
        scope="finite-output-family-not-universal-physical-map",
    )
    if not certificate.validates():
        raise ValueError("the proposed reference-order envelope does not hold")
    return certificate


@dataclass(frozen=True)
class CenteredReferenceRemainder:
    """Exact bridge from a relative-order remainder to a Birkhoff rate."""

    reference: RationalMatrix
    outputs: tuple[RationalMatrix, ...]
    relative_order_bound: Fraction
    envelope: ReferenceOrderEnvelope
    centered_remainders: tuple[RationalMatrix, ...]
    mass_preserving: bool
    universal_physical_input_bound: bool

    def validates(self) -> bool:
        try:
            reference = _matrix(self.reference)
            outputs = tuple(_matrix(output) for output in self.outputs)
            normalized = tuple(_normalized(output) for output in outputs)
        except (ValueError, ArithmeticError):
            return False
        if (
            not 0 <= self.relative_order_bound < 1
            or _trace(reference) != 1
            or not _is_positive_definite(reference)
            or not outputs
        ):
            return False
        remainders = tuple(
            _subtract(output, reference)
            for output in normalized
        )
        cap = _scale(self.relative_order_bound, reference)
        if not all(
            _trace(remainder) == 0
            and _is_psd(_subtract(cap, remainder))
            and _is_psd(_subtract(cap, _scale(Fraction(-1), remainder)))
            for remainder in remainders
        ):
            return False
        return (
            self.centered_remainders == remainders
            and self.mass_preserving
            and self.envelope.validates()
            and self.envelope.reference == reference
            and self.envelope.outputs == outputs
            and self.envelope.lower == 1 - self.relative_order_bound
            and self.envelope.upper == 1 + self.relative_order_bound
            and self.envelope.birkhoff_rate_bound
            == self.relative_order_bound
            and not self.universal_physical_input_bound
        )


def centered_reference_remainder(
    reference: tuple[tuple[int | Fraction, ...], ...],
    outputs: tuple[tuple[tuple[int | Fraction, ...], ...], ...],
    relative_order_bound: Fraction,
) -> CenteredReferenceRemainder:
    """Certify ``-delta R <= X/Tr(X)-R <= delta R`` exactly."""

    if not 0 <= relative_order_bound < 1:
        raise ValueError("a strict relative-order remainder must lie in [0, 1)")
    rational_reference = _matrix(reference)
    rational_outputs = tuple(_matrix(output) for output in outputs)
    envelope = reference_order_envelope(
        rational_reference,
        rational_outputs,
        1 - relative_order_bound,
        1 + relative_order_bound,
    )
    remainders = tuple(
        _subtract(_normalized(output), rational_reference)
        for output in rational_outputs
    )
    certificate = CenteredReferenceRemainder(
        reference=rational_reference,
        outputs=rational_outputs,
        relative_order_bound=relative_order_bound,
        envelope=envelope,
        centered_remainders=remainders,
        mass_preserving=all(
            _trace(remainder) == 0 for remainder in remainders
        ),
        universal_physical_input_bound=False,
    )
    if not certificate.validates():
        raise ValueError("the centered relative-order bound does not hold")
    return certificate


@dataclass(frozen=True)
class TraceConeInteriorCollapse:
    """Finite spectral witness for collapse of trace-norm interior radii."""

    coupling: Fraction
    cutoff: int
    normalized_spectrum: tuple[Fraction, ...]
    smallest_index: int
    smallest_eigenvalue: Fraction
    rank_one_subtraction: Fraction
    trace_distance_to_nonpositive: Fraction
    perturbed_eigenvalue: Fraction

    def validates(self) -> bool:
        if (
            not 0 < self.coupling < 1
            or self.cutoff < 0
            or len(self.normalized_spectrum) != self.cutoff + 1
            or any(value <= 0 for value in self.normalized_spectrum)
            or sum(self.normalized_spectrum, start=Fraction(0)) != 1
        ):
            return False
        minimum = min(self.normalized_spectrum)
        index = self.normalized_spectrum.index(minimum)
        subtraction = 2 * minimum
        return (
            self.smallest_index == index
            and self.smallest_eigenvalue == minimum
            and self.rank_one_subtraction == subtraction
            and self.trace_distance_to_nonpositive == subtraction
            and self.perturbed_eigenvalue == -minimum < 0
        )


def heat_trace_cone_interior_collapse(
    coupling: Fraction,
    cutoff: int,
) -> TraceConeInteriorCollapse:
    """Use the normalized heat spectrum as an exact interior-collapse witness."""

    if cutoff < 0:
        raise ValueError("the cutoff must be nonnegative")
    weights = tuple(
        heat_character_sup_term(coupling, label)
        for label in range(cutoff + 1)
    )
    total = sum(weights, start=Fraction(0))
    spectrum = tuple(weight / total for weight in weights)
    minimum = min(spectrum)
    index = spectrum.index(minimum)
    witness = TraceConeInteriorCollapse(
        coupling=coupling,
        cutoff=cutoff,
        normalized_spectrum=spectrum,
        smallest_index=index,
        smallest_eigenvalue=minimum,
        rank_one_subtraction=2 * minimum,
        trace_distance_to_nonpositive=2 * minimum,
        perturbed_eigenvalue=-minimum,
    )
    if not witness.validates():
        raise AssertionError("the trace-cone interior witness drifted")
    return witness


@dataclass(frozen=True)
class TraceSmallOrderLargeWitness:
    """A vanishing trace error whose relative heat-order error remains one."""

    coupling: Fraction
    cutoff: int
    reference_spectrum: tuple[Fraction, ...]
    centered_remainder: tuple[Fraction, ...]
    trace_norm: Fraction
    relative_order_norm: Fraction
    output_spectrum: tuple[Fraction, ...]

    def validates(self) -> bool:
        if (
            self.cutoff < 1
            or len(self.reference_spectrum) != self.cutoff + 1
            or len(self.centered_remainder) != self.cutoff + 1
            or len(self.output_spectrum) != self.cutoff + 1
            or any(value <= 0 for value in self.reference_spectrum)
            or sum(self.reference_spectrum, start=Fraction(0)) != 1
        ):
            return False
        minimum = min(self.reference_spectrum)
        min_index = self.reference_spectrum.index(minimum)
        max_index = self.reference_spectrum.index(max(self.reference_spectrum))
        expected = tuple(
            minimum
            if index == min_index
            else -minimum
            if index == max_index
            else Fraction(0)
            for index in range(len(self.reference_spectrum))
        )
        ratios = tuple(
            abs(error) / reference
            for error, reference in zip(
                self.centered_remainder,
                self.reference_spectrum,
                strict=True,
            )
        )
        return (
            self.centered_remainder == expected
            and sum(self.centered_remainder, start=Fraction(0)) == 0
            and self.trace_norm
            == sum(
                (abs(value) for value in self.centered_remainder),
                start=Fraction(0),
            )
            == 2 * minimum
            and self.relative_order_norm == max(ratios) == 1
            and self.output_spectrum
            == tuple(
                reference + error
                for reference, error in zip(
                    self.reference_spectrum,
                    self.centered_remainder,
                    strict=True,
                )
            )
            and all(value > 0 for value in self.output_spectrum)
            and sum(self.output_spectrum, start=Fraction(0)) == 1
        )


def trace_small_order_large_witness(
    coupling: Fraction,
    cutoff: int,
) -> TraceSmallOrderLargeWitness:
    """Construct the exact trace-norm-versus-relative-order separation."""

    if cutoff < 1:
        raise ValueError("the centered witness needs at least two channels")
    collapse = heat_trace_cone_interior_collapse(coupling, cutoff)
    spectrum = collapse.normalized_spectrum
    minimum = min(spectrum)
    min_index = spectrum.index(minimum)
    max_index = spectrum.index(max(spectrum))
    remainder = tuple(
        minimum
        if index == min_index
        else -minimum
        if index == max_index
        else Fraction(0)
        for index in range(len(spectrum))
    )
    output = tuple(
        reference + error
        for reference, error in zip(spectrum, remainder, strict=True)
    )
    witness = TraceSmallOrderLargeWitness(
        coupling=coupling,
        cutoff=cutoff,
        reference_spectrum=spectrum,
        centered_remainder=remainder,
        trace_norm=2 * minimum,
        relative_order_norm=Fraction(1),
        output_spectrum=output,
    )
    if not witness.validates():
        raise AssertionError("the trace/order separation witness drifted")
    return witness


@dataclass(frozen=True)
class PhysicalConditionalDoeblin:
    """All-label physical minorization from pointwise heat-kernel bounds."""

    coupling: Fraction
    majorant_cutoff: int
    active_plaquettes: int
    plaquette_lower: Fraction
    plaquette_upper: Fraction
    normalized_density_lower: Fraction
    normalized_density_upper: Fraction
    projective_spread: Fraction
    birkhoff_rate_bound: Fraction
    boundary_holonomy_uniform: bool
    ambient_volume_independent: bool
    representation_cutoff_independent: bool
    deterministic_pushforward_preserves_bounds: bool
    complete_physical_conditional_family: bool
    spacing_uniform_physical_rate: bool

    def validates(self) -> bool:
        try:
            floor = jacobi_heat_kernel_floor(self.coupling)
            majorant = single_plaquette_all_label_tail(
                self.coupling,
                self.majorant_cutoff,
            )
        except ValueError:
            return False
        lower = floor.heat_kernel_floor
        upper = majorant.total_upper_bound
        density_lower = (lower / upper) ** self.active_plaquettes
        density_upper = (upper / lower) ** self.active_plaquettes
        spread = density_upper / density_lower
        return (
            self.active_plaquettes == WHOLE_SLAB_FACE_COUNT
            and self.plaquette_lower == lower > 0
            and self.plaquette_upper == upper >= lower
            and self.normalized_density_lower == density_lower > 0
            and self.normalized_density_upper == density_upper
            and self.normalized_density_lower
            * self.normalized_density_upper
            == 1
            and self.projective_spread == spread
            and self.birkhoff_rate_bound
            == (spread - 1) / (spread + 1)
            == (
                self.normalized_density_upper
                - self.normalized_density_lower
            ) / (
                self.normalized_density_upper
                + self.normalized_density_lower
            )
            and 0 <= self.birkhoff_rate_bound < 1
            and self.boundary_holonomy_uniform
            and self.ambient_volume_independent
            and self.representation_cutoff_independent
            and self.deterministic_pushforward_preserves_bounds
            and self.complete_physical_conditional_family
            and not self.spacing_uniform_physical_rate
        )


def physical_conditional_doeblin(
    coupling: Fraction,
    majorant_cutoff: int,
) -> PhysicalConditionalDoeblin:
    """Construct the fixed-coupling all-label physical Doeblin envelope."""

    floor = jacobi_heat_kernel_floor(coupling)
    majorant = single_plaquette_all_label_tail(coupling, majorant_cutoff)
    lower = floor.heat_kernel_floor
    upper = majorant.total_upper_bound
    density_lower = (lower / upper) ** WHOLE_SLAB_FACE_COUNT
    density_upper = (upper / lower) ** WHOLE_SLAB_FACE_COUNT
    spread = density_upper / density_lower
    certificate = PhysicalConditionalDoeblin(
        coupling=coupling,
        majorant_cutoff=majorant_cutoff,
        active_plaquettes=WHOLE_SLAB_FACE_COUNT,
        plaquette_lower=lower,
        plaquette_upper=upper,
        normalized_density_lower=density_lower,
        normalized_density_upper=density_upper,
        projective_spread=spread,
        birkhoff_rate_bound=(spread - 1) / (spread + 1),
        boundary_holonomy_uniform=True,
        ambient_volume_independent=True,
        representation_cutoff_independent=True,
        deterministic_pushforward_preserves_bounds=True,
        complete_physical_conditional_family=True,
        spacing_uniform_physical_rate=False,
    )
    if not certificate.validates():
        raise AssertionError("the physical conditional Doeblin bound drifted")
    return certificate


def _sample_envelope() -> ReferenceOrderEnvelope:
    return reference_order_envelope(
        (
            (Fraction(1, 2), 0),
            (0, Fraction(1, 2)),
        ),
        (
            (
                (Fraction(2, 3), 0),
                (0, Fraction(1, 3)),
            ),
            (
                (Fraction(1, 3), 0),
                (0, Fraction(2, 3)),
            ),
        ),
        Fraction(2, 3),
        Fraction(4, 3),
    )


@dataclass(frozen=True)
class BF4ReferenceConeFrontier:
    """Fail-closed BF3.2-to-BF4 cone correction."""

    bf2_order_carrier_id: str
    full_trace_cone_has_trace_norm_interior: bool
    reference_order_cone_required: bool
    dimension_free_envelope_theorem: bool
    bf31_map_positive_improving: bool
    all_label_reference_minorization_proved: bool
    fixed_coupling_local_diameter_proved: bool
    fixed_distance_grouped_diameter_proved: bool
    spacing_uniform_physical_rate_proved: bool
    trace_tail_implies_relative_order_tail: bool
    physical_relative_order_remainder_proved: bool
    bf32_ready_for_handoff: bool
    bf4_ready: bool
    first_open_obligation: str

    def validates(self) -> bool:
        bf31 = whole_slab_density_handoff_audit()
        bf32 = bf32_all_label_frontier()
        sample = _sample_envelope()
        collapse = heat_trace_cone_interior_collapse(Fraction(1, 2), 6)
        separation = trace_small_order_large_witness(Fraction(1, 2), 6)
        physical = physical_conditional_doeblin(Fraction(1, 2), 2)
        return (
            self.bf2_order_carrier_id
            == "BF2.1-complete-reflected-PSD-trace-class-kernel"
            and not self.full_trace_cone_has_trace_norm_interior
            and self.reference_order_cone_required
            and self.dimension_free_envelope_theorem
            and sample.validates()
            and sample.birkhoff_rate_bound == Fraction(1, 3)
            and collapse.validates()
            and separation.validates()
            and separation.relative_order_norm == 1
            and not self.trace_tail_implies_relative_order_tail
            and not self.bf31_map_positive_improving
            and not bf31.cut_signature_mixing
            and bf31.every_component_rank_one
            and self.all_label_reference_minorization_proved
            and physical.validates()
            and self.fixed_coupling_local_diameter_proved
            and not physical.spacing_uniform_physical_rate
            and not self.fixed_distance_grouped_diameter_proved
            and not self.spacing_uniform_physical_rate_proved
            and not self.physical_relative_order_remainder_proved
            and self.bf32_ready_for_handoff
            and bf32.bf32_closed
            and not self.bf4_ready
            and self.first_open_obligation
            == "sharpen-Doeblin-rate-to-fixed-physical-distance-scaling"
        )


@cache
def bf4_reference_cone_frontier() -> BF4ReferenceConeFrontier:
    """Return the corrected BF4 cone target and its present open field."""

    frontier = BF4ReferenceConeFrontier(
        bf2_order_carrier_id=(
            "BF2.1-complete-reflected-PSD-trace-class-kernel"
        ),
        full_trace_cone_has_trace_norm_interior=False,
        reference_order_cone_required=True,
        dimension_free_envelope_theorem=True,
        bf31_map_positive_improving=False,
        all_label_reference_minorization_proved=True,
        fixed_coupling_local_diameter_proved=True,
        fixed_distance_grouped_diameter_proved=False,
        spacing_uniform_physical_rate_proved=False,
        trace_tail_implies_relative_order_tail=False,
        physical_relative_order_remainder_proved=False,
        bf32_ready_for_handoff=True,
        bf4_ready=False,
        first_open_obligation=(
            "sharpen-Doeblin-rate-to-fixed-physical-distance-scaling"
        ),
    )
    if not frontier.validates():
        raise AssertionError("the BF4 reference-cone frontier drifted")
    return frontier
