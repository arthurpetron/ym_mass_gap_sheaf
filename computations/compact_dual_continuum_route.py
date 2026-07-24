"""Fail-closed certificate spine for compact-dual continuum gap survival.

The exact dual sign computations are finite structural evidence.  They do not
construct a physical block map, a cutoff-uniform norm, an RG contraction, a
landing witness, a summable distortion modulus, or a continuum gap floor.
This module makes that separation executable.

Every analytic gate is represented by witness-bearing exact-rational data.
The route closes only when the gates compose in dependency order and the
total certified loss is strictly smaller than the fixed-spacing gap anchor.
In particular, :func:`current_dual_route` intentionally stops at CD-2.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from typing import TypeAlias

RationalVector: TypeAlias = tuple[Fraction, ...]
RationalMatrix: TypeAlias = tuple[RationalVector, ...]


class ClosureGate(Enum):
    """The irreducible gates between finite dual evidence and the Clay claim."""

    CD2_PHYSICAL_BLOCK = "CD-2 physical block and overlap remainder"
    CD3_UNIFORM_REMAINDER = "CD-3 cutoff/volume-uniform remainder norm"
    RG_I7_CONTRACTION = "CD-4 / RG-I7 preserved-domain contraction"
    RG_I8_LANDING = "CD-5 / RG-I8 constructive physical landing"
    RG_I9_DISTORTION = "RG-I9 summable dynamic/interface distortion"
    SPACING_UNIFORM_GAP = "spacing/volume-uniform continuum gap survival"


@dataclass(frozen=True)
class GateResult:
    """One fail-closed route decision with its mathematical implication."""

    gate: ClosureGate
    closed: bool
    detail: str


@dataclass(frozen=True)
class FiniteDualEvidence:
    """Pinned finite evidence that is deliberately not an analytic certificate."""

    four_cube_pair_orbits: int
    six_valent_pair_orbits: int
    first_branching_defect_orbits: int
    all_tested_complete_sums_nonnegative: bool
    local_sign_law_identified: bool

    @property
    def analytic_gates_discharged(self) -> int:
        """Finite sign evidence never discharges a continuum analytic gate."""

        return 0


@dataclass(frozen=True)
class GeometricTailEnvelope:
    """Constructive infinite-tail bound ``amplitude * ratio^n``."""

    amplitude: Fraction
    ratio: Fraction

    def __post_init__(self) -> None:
        if self.amplitude < 0:
            raise ValueError("a tail amplitude must be nonnegative")
        if not 0 <= self.ratio < 1:
            raise ValueError("a geometric tail ratio must lie in [0, 1)")

    def term_bound(self, index: int) -> Fraction:
        """Return the exact envelope for term ``index``."""

        if index < 0:
            raise ValueError("a tail index must be nonnegative")
        return self.amplitude * self.ratio**index

    def tail_bound(self, start: int) -> Fraction:
        """Return an exact modulus for the sum from ``start`` onward."""

        if start < 0:
            raise ValueError("a tail start must be nonnegative")
        return self.term_bound(start) / (1 - self.ratio)


@dataclass(frozen=True)
class CumulativeContractionEnvelope:
    """Bound an accumulated Lipschitz product by ``prefactor * ratio^n``."""

    prefactor: Fraction
    ratio: Fraction

    def __post_init__(self) -> None:
        if self.prefactor <= 0:
            raise ValueError("a contraction prefactor must be positive")
        if not 0 <= self.ratio < 1:
            raise ValueError("a contraction ratio must lie in [0, 1)")

    def product_bound(self, steps: int) -> Fraction:
        """Return the exact accumulated contraction cap after ``steps``."""

        if steps < 0:
            raise ValueError("a step count must be nonnegative")
        return self.prefactor * self.ratio**steps


@dataclass(frozen=True)
class PhysicalBlockRemainderCertificate:
    """Exact CD-2 pushforward and retained overlap remainder.

    Rows of ``kernel`` are indexed by the pinned fine states and columns by
    the pinned coarse states.  The remainder is computed, never supplied:

    ``R(y) = sum_x fine(x) K(x,y) - coarse(y)``.

    The semantic fields must be produced by the physical geometry/integrator
    bridge.  They prevent an abstract stochastic matrix from being mistaken
    for the Yang--Mills block.
    """

    physical_data_id: str
    fine_state_ids: tuple[str, ...]
    coarse_state_ids: tuple[str, ...]
    fine_weights: RationalVector
    coarse_weights: RationalVector
    kernel: RationalMatrix
    geometry_pinned: bool
    integrator_semantics_proved: bool
    coupling_coordinate_pinned: bool
    complete_boundary_channels: bool
    physical_kernel_identified: bool
    target_support_proved: bool
    reflection_intertwines: bool

    def __post_init__(self) -> None:
        if not self.physical_data_id:
            raise ValueError("the physical data identifier must be nonempty")
        if not self.fine_state_ids or not self.coarse_state_ids:
            raise ValueError("fine and coarse physical state lists must be nonempty")
        if len(self.fine_state_ids) != len(self.fine_weights):
            raise ValueError("fine state identifiers and weights have different lengths")
        if len(self.coarse_state_ids) != len(self.coarse_weights):
            raise ValueError("coarse state identifiers and weights have different lengths")
        if len(self.kernel) != len(self.fine_weights):
            raise ValueError("the kernel must have one row per fine state")
        if any(len(row) != len(self.coarse_weights) for row in self.kernel):
            raise ValueError("every kernel row must have one entry per coarse state")
        if len(set(self.fine_state_ids)) != len(self.fine_state_ids):
            raise ValueError("fine state identifiers must be unique")
        if len(set(self.coarse_state_ids)) != len(self.coarse_state_ids):
            raise ValueError("coarse state identifiers must be unique")

    def pushforward(self) -> RationalVector:
        """Compute the exact coarse pushforward of the fine weights."""

        return tuple(
            sum(
                (
                    self.fine_weights[source] * self.kernel[source][target]
                    for source in range(len(self.fine_weights))
                ),
                start=Fraction(0),
            )
            for target in range(len(self.coarse_weights))
        )

    def remainder(self) -> RationalVector:
        """Compute the signed overlap remainder exactly."""

        return tuple(
            pushed - coarse
            for pushed, coarse in zip(
                self.pushforward(), self.coarse_weights, strict=True
            )
        )

    def remainder_l1_norm(self) -> Fraction:
        """Return the exact finite weighted-coordinate L1 norm."""

        return sum((abs(value) for value in self.remainder()), start=Fraction(0))

    def kernel_is_stochastic(self) -> bool:
        """Check pointwise positivity and exact row normalization."""

        return all(
            all(entry >= 0 for entry in row)
            and sum(row, start=Fraction(0)) == 1
            for row in self.kernel
        )

    def weights_are_nonnegative(self) -> bool:
        """Check that both finite physical measures are nonnegative."""

        return all(value >= 0 for value in self.fine_weights) and all(
            value >= 0 for value in self.coarse_weights
        )

    def remainder_has_zero_mass(self) -> bool:
        """Check the exact total-mass cancellation required by CD-2."""

        return sum(self.remainder(), start=Fraction(0)) == 0

    def is_closed(self) -> bool:
        """Decide the complete algebraic and semantic CD-2 gate."""

        semantic_bridge = (
            self.geometry_pinned
            and self.integrator_semantics_proved
            and self.coupling_coordinate_pinned
            and self.complete_boundary_channels
            and self.physical_kernel_identified
            and self.target_support_proved
            and self.reflection_intertwines
        )
        return (
            semantic_bridge
            and self.kernel_is_stochastic()
            and self.weights_are_nonnegative()
            and self.remainder_has_zero_mass()
        )


@dataclass(frozen=True)
class UniformRemainderNormCertificate:
    """CD-3 norm bound with explicit cutoff-tail modulus."""

    observed_norm: Fraction
    defect_coordinate: Fraction
    quadratic_constant: Fraction
    cutoff_tail: GeometricTailEnvelope
    weighted_norm_matches_block: bool
    constant_is_cutoff_independent: bool
    volume_uniform: bool

    def __post_init__(self) -> None:
        if self.observed_norm < 0:
            raise ValueError("an observed norm must be nonnegative")
        if self.defect_coordinate < 0:
            raise ValueError("a defect coordinate must be nonnegative")
        if self.quadratic_constant < 0:
            raise ValueError("a quadratic constant must be nonnegative")

    def quadratic_cap(self) -> Fraction:
        """Return the initial target ``c * defect^2``."""

        return self.quadratic_constant * self.defect_coordinate**2

    def is_closed_for(self, block: PhysicalBlockRemainderCertificate) -> bool:
        """Check that this norm certificate measures the actual CD-2 remainder."""

        return (
            block.is_closed()
            and self.weighted_norm_matches_block
            and self.constant_is_cutoff_independent
            and self.volume_uniform
            and self.observed_norm == block.remainder_l1_norm()
            and self.observed_norm <= self.quadratic_cap()
        )


@dataclass(frozen=True)
class LanfordEnclosureCertificate:
    """CD-4 / RG-I7 contraction on one pinned preserved physical domain."""

    domain_id: str
    self_mapping: bool
    reflection_cone_preserved: bool
    physical_norm_pinned: bool
    uniform_ratio: Fraction | None = None
    cumulative_contraction: CumulativeContractionEnvelope | None = None

    def __post_init__(self) -> None:
        if not self.domain_id:
            raise ValueError("the Lanford domain identifier must be nonempty")
        if self.uniform_ratio is not None and not 0 <= self.uniform_ratio < 1:
            raise ValueError("a uniform contraction ratio must lie in [0, 1)")

    def has_quantitative_contraction(self) -> bool:
        """Accept either a uniform one-step ratio or accumulated contraction."""

        return self.uniform_ratio is not None or self.cumulative_contraction is not None

    def is_closed(self) -> bool:
        """Decide the preserved-domain contraction gate."""

        return (
            self.self_mapping
            and self.reflection_cone_preserved
            and self.physical_norm_pinned
            and self.has_quantitative_contraction()
        )


@dataclass(frozen=True)
class ConstructiveLandingCertificate:
    """CD-5 / RG-I8 witness for entry of the physical trajectory."""

    scale: int
    state_id: str
    physical_trajectory_pinned: bool
    state_computed: bool
    state_in_enclosure: bool

    def __post_init__(self) -> None:
        if self.scale < 0:
            raise ValueError("a landing scale must be nonnegative")
        if not self.state_id:
            raise ValueError("the landing state identifier must be nonempty")

    def is_closed_for(self, enclosure: LanfordEnclosureCertificate) -> bool:
        """Check constructive entry into the exact certified domain."""

        return (
            enclosure.is_closed()
            and self.physical_trajectory_pinned
            and self.state_computed
            and self.state_in_enclosure
        )


@dataclass(frozen=True)
class SummableDistortionCertificate:
    """RG-I9 dynamic, interface, and retained-block error ledgers."""

    block_remainder: GeometricTailEnvelope
    dynamic: GeometricTailEnvelope
    interface: GeometricTailEnvelope
    physical_comparison_pinned: bool
    scale_uniform: bool
    computable_modulus: bool

    def total_tail_bound(self, start: int) -> Fraction:
        """Return the exact total RG distortion after ``start``."""

        return (
            self.block_remainder.tail_bound(start)
            + self.dynamic.tail_bound(start)
            + self.interface.tail_bound(start)
        )

    def is_closed(self) -> bool:
        """Decide whether the three infinite ledgers are physically usable."""

        return (
            self.physical_comparison_pinned
            and self.scale_uniform
            and self.computable_modulus
        )


@dataclass(frozen=True)
class ContinuumGapSurvivalCertificate:
    """Physical readout and quantitative spacing/volume continuum margin."""

    fixed_spacing_gap: Fraction
    continuum_start: int
    volume_error: GeometricTailEnvelope
    spacing_error: GeometricTailEnvelope
    wilson_readout_pinned: bool
    volume_modulus_uniform: bool
    spacing_conversion_proved: bool
    os_reconstruction_bound: bool

    def __post_init__(self) -> None:
        if self.fixed_spacing_gap <= 0:
            raise ValueError("the fixed-spacing gap anchor must be positive")
        if self.continuum_start < 0:
            raise ValueError("the continuum start must be nonnegative")

    def limit_error_bound(self) -> Fraction:
        """Return the exact volume plus spacing loss."""

        return self.volume_error.tail_bound(
            self.continuum_start
        ) + self.spacing_error.tail_bound(self.continuum_start)

    def is_semantically_closed(self) -> bool:
        """Check the physical Wilson, uniformity, spacing, and OS bindings."""

        return (
            self.wilson_readout_pinned
            and self.volume_modulus_uniform
            and self.spacing_conversion_proved
            and self.os_reconstruction_bound
        )


@dataclass(frozen=True)
class CompactDualContinuumRoute:
    """Dependency-complete route from exact dual data to a continuum gap."""

    evidence: FiniteDualEvidence
    block: PhysicalBlockRemainderCertificate | None = None
    remainder_norm: UniformRemainderNormCertificate | None = None
    enclosure: LanfordEnclosureCertificate | None = None
    landing: ConstructiveLandingCertificate | None = None
    distortion: SummableDistortionCertificate | None = None
    continuum: ContinuumGapSurvivalCertificate | None = None

    def candidate_gap_floor(self) -> Fraction | None:
        """Compute the proposed floor before the dependency audit."""

        if self.landing is None or self.distortion is None or self.continuum is None:
            return None
        total_loss = self.distortion.total_tail_bound(
            self.landing.scale
        ) + self.continuum.limit_error_bound()
        return self.continuum.fixed_spacing_gap - total_loss

    def gate_report(self) -> tuple[GateResult, ...]:
        """Audit every gate in dependency order, stopping substitutions."""

        block_closed = self.block is not None and self.block.is_closed()
        block_result = GateResult(
            ClosureGate.CD2_PHYSICAL_BLOCK,
            block_closed,
            (
                "physical pushforward, complete channels, zero-mass remainder, and "
                "reflection intertwining verified"
                if block_closed
                else "missing physical CD-2 semantic/kernel/remainder certificate"
            ),
        )

        remainder_closed = (
            block_closed
            and self.block is not None
            and self.remainder_norm is not None
            and self.remainder_norm.is_closed_for(self.block)
        )
        remainder_result = GateResult(
            ClosureGate.CD3_UNIFORM_REMAINDER,
            remainder_closed,
            (
                "actual CD-2 remainder has a cutoff-independent, volume-uniform norm"
                if remainder_closed
                else "missing norm identity, quadratic bound, or uniform cutoff modulus"
            ),
        )

        contraction_closed = (
            remainder_closed
            and self.enclosure is not None
            and self.enclosure.is_closed()
        )
        contraction_result = GateResult(
            ClosureGate.RG_I7_CONTRACTION,
            contraction_closed,
            (
                "physical domain is self-mapping, cone-preserving, and contractive"
                if contraction_closed
                else "missing preserved physical Lanford enclosure or contraction"
            ),
        )

        landing_closed = (
            contraction_closed
            and self.enclosure is not None
            and self.landing is not None
            and self.landing.is_closed_for(self.enclosure)
        )
        landing_result = GateResult(
            ClosureGate.RG_I8_LANDING,
            landing_closed,
            (
                "computed physical trajectory enters the certified enclosure"
                if landing_closed
                else "missing constructive physical crossover state and scale"
            ),
        )

        distortion_closed = (
            landing_closed
            and self.distortion is not None
            and self.distortion.is_closed()
        )
        distortion_result = GateResult(
            ClosureGate.RG_I9_DISTORTION,
            distortion_closed,
            (
                "dynamic, interface, and block-remainder tails have exact moduli"
                if distortion_closed
                else "missing physical summable distortion comparison or modulus"
            ),
        )

        floor = self.candidate_gap_floor()
        continuum_closed = (
            distortion_closed
            and self.continuum is not None
            and self.continuum.is_semantically_closed()
            and floor is not None
            and floor > 0
        )
        continuum_result = GateResult(
            ClosureGate.SPACING_UNIFORM_GAP,
            continuum_closed,
            (
                f"strict exact continuum gap floor {floor}"
                if continuum_closed
                else "missing physical readout/uniform limit binding or positive loss margin"
            ),
        )
        return (
            block_result,
            remainder_result,
            contraction_result,
            landing_result,
            distortion_result,
            continuum_result,
        )

    def first_open_gate(self) -> ClosureGate | None:
        """Return the first dependency that is not genuinely discharged."""

        for result in self.gate_report():
            if not result.closed:
                return result.gate
        return None

    def is_continuum_closed(self) -> bool:
        """Decide the full spacing-uniform continuum survival statement."""

        return self.first_open_gate() is None

    def certified_gap_floor(self) -> Fraction | None:
        """Return the floor only after every physical dependency has closed."""

        if not self.is_continuum_closed():
            return None
        return self.candidate_gap_floor()


def current_finite_dual_evidence() -> FiniteDualEvidence:
    """Return the present exact finite sign frontier without analytic inflation."""

    return FiniteDualEvidence(
        four_cube_pair_orbits=100,
        six_valent_pair_orbits=65,
        first_branching_defect_orbits=14,
        all_tested_complete_sums_nonnegative=True,
        local_sign_law_identified=True,
    )


def current_dual_route() -> CompactDualContinuumRoute:
    """Return the honest current route: finite evidence, with CD-2 still open."""

    return CompactDualContinuumRoute(evidence=current_finite_dual_evidence())
