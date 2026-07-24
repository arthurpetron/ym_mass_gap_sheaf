"""Executable CD-2 frontier after corrected-slab normalization.

The repository now contains all finite algebra surrounding a physical block:
normalized corrected-slab laws, single-scale reflection positivity, a local
source-dependent character/fusion kernel, a closed cutoff-one cube projector,
reflection-compatible composition for link-separated cubes, automatic
zero-mass remainder cancellation, and the universal probability bound
``||R||_1 <= 2``.  The first genuinely overlapping carrier is also exact:
two adjacent six-face cube boundaries cancel their shared face pair, every
touched link of the resulting ten-face carrier has incidence two, and its
activity is the tenth power of the fundamental face coefficient.  Normalizing
the four already-glued occupation carriers gives a nonnegative,
row-normalized, reversible, and demonstrably source-dependent cutoff-one
conditional kernel.  The Boolean channel has now also been replaced locally
by the complete bounded-spin shared-face recoupling fiber: all five SU(2)
fusion constraints are normalized at every cutoff and intertwine reflection.

This closes the shared-face fiber, and the adjacent target is assembled too:
both six-face target spaces, sixteen non-interface link factors, and the five
shared recoupling factors are summed under one all-cutoff denominator.  Its
reflection intertwining is exact.  But its rows are presently normalized only
on ``CubeStretchedCompatibleSource``: all six face-packet totals of each cube
are required to agree.  That is a positive-witness sector, not a proof that
every corrected-slab physical source is covered.  Full physical source
coverage is therefore the first open gate; a global fine-support projection
comes only after it.

The physical remainder now also has a locality fence: for every cylinder
intertwined pointwise by a candidate slab kernel, the fine/coarse Gibbs
cylinder mismatch is exactly a selected signed remainder and is bounded by
``||R||_1``.  Thus a nonlocal exact coupling cannot be promoted into a
remainder-free RG step.  The vanishing uniform norm belongs to CD-3.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction


class CD2Subgate(Enum):
    """Ordered construction gates inside the physical CD-2 block."""

    NORMALIZED_SLAB_LAWS = "normalized corrected-slab physical laws"
    LOCAL_FUSION_KERNEL = "source-dependent local character/fusion kernel"
    CLOSED_COMPONENT = "closed projected cube component"
    SEPARATED_COMPOSITION = "link-separated physical composition"
    OVERLAPPING_CARRIER_CORRECTION = (
        "exact adjacent-cube shared-face cancellation activity"
    )
    CUTOFF_ONE_OVERLAP_KERNEL = (
        "source-dependent reversible cutoff-one overlap kernel"
    )
    ALL_CUTOFF_SHARED_FACE_RECOUPLING = (
        "all-cutoff five-constraint shared-face recoupling kernel"
    )
    OVERLAPPING_LINK_ASSEMBLY = (
        "complete adjacent-cube joint production assembly"
    )
    OVERLAP_REFLECTION_INTERTWINING = (
        "reflection intertwining of the restricted adjacent target"
    )
    PHYSICAL_SOURCE_COVERAGE = (
        "coverage of every corrected-slab physical source"
    )
    GLOBAL_FINE_SUPPORT_PROJECTION = (
        "global fine-support projection for overlapping cube families"
    )
    ALL_CUTOFF_GLOBAL_KERNEL = "all-cutoff whole-slab kernel"
    PHYSICAL_PUSHFORWARD = "physical Gibbs pushforward identification"


CD2_LEAN_THEOREMS = (
    "CompactDualSlabPhysicalData.SlabPhysicalData.normalizedMass_total",
    "CompactDualSlabPhysicalData.SlabPhysicalData."
    "fullReflectionQuadratic_nonnegative",
    "Z4DyadicSlabCharacterFusionConditionalKernel."
    "packetPairChannelConditionalKernel_source_dependent",
    "Z4DyadicSlabCharacterFusionConditionalKernel."
    "dyadicSlabPairChannelConditionalKernel_reflection_equivariant",
    "Z4DyadicSlabCubeCoupledConditionalKernel."
    "cubeCoupledConditionalKernel_row_normalized",
    "Z4DyadicSlabCubeFineSupportProjectedKernel."
    "closedCubeFineSlotKernel_row_normalized",
    "Z4DyadicSlabCubeKernelProductComposition."
    "bridgedProjectedTwoCubeRawProduct_eqv_unionProductionSummand",
    "Z4AdjacentCubeCancellationActivity."
    "zeroXAxisCancelledRoot_canonicalSurfaceActivity_eqv_pow_ten",
    "Z4AdjacentCubeCancellationActivity."
    "independent_cube_power_eqv_shared_face_square_mul_cancelled",
    "Z4AdjacentCubeCancellationConditionalKernel."
    "adjacentCubeConditionalKernel_row_normalized",
    "Z4AdjacentCubeCancellationConditionalKernel."
    "adjacentCubeConditionalKernel_detailed_balance",
    "Z4AdjacentCubeCancellationConditionalKernel."
    "adjacentCubeConditionalKernel_anchor_source_dependent",
    "Z4AdjacentCubeSharedFaceRecouplingKernel."
    "adjacentCubeSharedFaceConditionalKernel_row_normalized",
    "Z4AdjacentCubeSharedFaceRecouplingKernel."
    "adjacentCubeSharedFaceConditionalKernel_reflection",
    "Z4AdjacentCubeSharedFaceRecouplingKernel."
    "adjacentCubeSharedFaceConditionalKernel_source_dependent",
    "Z4AdjacentCubeJointConditionalKernel."
    "adjacentCubeJointConditionalKernel_row_normalized",
    "Z4AdjacentCubeJointConditionalKernel."
    "adjacentCubeJointConditionalKernel_reflection",
    "CompactDualPhysicalRemainderLocality.PhysicalKernel."
    "fineCoarseCylinderDefect_abs_le_remainderL1",
    "CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel."
    "remainder_total_eqv_zero",
    "CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel."
    "remainderL1_le_two",
)


@dataclass(frozen=True)
class CD2Frontier:
    """Fail-closed ledger for the physical block construction."""

    normalized_slab_laws: bool
    local_fusion_kernel: bool
    closed_component: bool
    separated_composition: bool
    overlapping_carrier_correction: bool
    cutoff_one_overlap_kernel: bool
    all_cutoff_shared_face_recoupling: bool
    overlapping_link_assembly: bool
    overlap_reflection_intertwining: bool
    physical_source_coverage: bool
    global_fine_support_projection: bool
    all_cutoff_global_kernel: bool
    physical_pushforward: bool
    zero_mass_remainder_derived: bool
    universal_l1_cap: Fraction | None

    def gate_results(self) -> tuple[tuple[CD2Subgate, bool], ...]:
        """Return every construction subgate in dependency order."""

        return (
            (CD2Subgate.NORMALIZED_SLAB_LAWS, self.normalized_slab_laws),
            (CD2Subgate.LOCAL_FUSION_KERNEL, self.local_fusion_kernel),
            (CD2Subgate.CLOSED_COMPONENT, self.closed_component),
            (CD2Subgate.SEPARATED_COMPOSITION, self.separated_composition),
            (
                CD2Subgate.OVERLAPPING_CARRIER_CORRECTION,
                self.overlapping_carrier_correction,
            ),
            (
                CD2Subgate.CUTOFF_ONE_OVERLAP_KERNEL,
                self.cutoff_one_overlap_kernel,
            ),
            (
                CD2Subgate.ALL_CUTOFF_SHARED_FACE_RECOUPLING,
                self.all_cutoff_shared_face_recoupling,
            ),
            (
                CD2Subgate.OVERLAPPING_LINK_ASSEMBLY,
                self.overlapping_link_assembly,
            ),
            (
                CD2Subgate.OVERLAP_REFLECTION_INTERTWINING,
                self.overlap_reflection_intertwining,
            ),
            (
                CD2Subgate.PHYSICAL_SOURCE_COVERAGE,
                self.physical_source_coverage,
            ),
            (
                CD2Subgate.GLOBAL_FINE_SUPPORT_PROJECTION,
                self.global_fine_support_projection,
            ),
            (
                CD2Subgate.ALL_CUTOFF_GLOBAL_KERNEL,
                self.all_cutoff_global_kernel,
            ),
            (CD2Subgate.PHYSICAL_PUSHFORWARD, self.physical_pushforward),
        )

    def first_open_subgate(self) -> CD2Subgate | None:
        """Return the first physical construction subgate still open."""

        for gate, closed in self.gate_results():
            if not closed:
                return gate
        return None

    def finite_remainder_algebra_closed(self) -> bool:
        """Check the now-derived normalization consequences."""

        return (
            self.normalized_slab_laws
            and self.zero_mass_remainder_derived
            and self.universal_l1_cap == 2
        )

    def physical_cd2_closed(self) -> bool:
        """Require every physical construction subgate."""

        return self.first_open_subgate() is None

    def cd3_smallness_closed(self) -> bool:
        """The universal cap two is not a vanishing RG defect estimate."""

        return False


def current_cd2_frontier() -> CD2Frontier:
    """Return the exact current frontier without promoting local sectors."""

    return CD2Frontier(
        normalized_slab_laws=True,
        local_fusion_kernel=True,
        closed_component=True,
        separated_composition=True,
        overlapping_carrier_correction=True,
        cutoff_one_overlap_kernel=True,
        all_cutoff_shared_face_recoupling=True,
        overlapping_link_assembly=True,
        overlap_reflection_intertwining=True,
        physical_source_coverage=False,
        global_fine_support_projection=False,
        all_cutoff_global_kernel=False,
        physical_pushforward=False,
        zero_mass_remainder_derived=True,
        universal_l1_cap=Fraction(2),
    )
