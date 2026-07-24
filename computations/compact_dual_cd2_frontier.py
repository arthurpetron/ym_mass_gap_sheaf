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

This is not just an unproved coverage lemma.  An exact positive physical
counterexample is now pinned: a translated fine unit-cube boundary is
link-closed and has positive cutoff-one activity, but its induced bottom and
top dyadic face totals are respectively two and zero.  No
``CubeStretchedCompatibleSource`` can cover it.  The first open constructor
must therefore be generalized to arbitrary physical packets while retaining
the fine auxiliary/intertwiner witness.  That generalization is now closed:
the complete adjacent target is nonnegative, row-normalized, and
reflection-intertwining for arbitrary bounded face packets whenever one
positive joint target is retained.

The fine physical term also now supplies its retained datum constructively.
Every link multiplicity is expanded into the literal finite list of accepted
fusion paths; their whole-slab Cartesian product has length exactly equal to
the multiplicity product in the physical Gibbs summand.  Hence every strictly
positive physical fine summand has a global fine-intertwiner witness.  The
first open gate is now coarse recoupling coherence: transport that global
field through all dyadic face fusions while forcing every reused coarse face
and link to share one target channel.  At cutoff one the local algebra on
both sides of that assembly is now closed: the parity-selected channel of
every four-face packet has positive recoupling mass, and every binary
even-parity word of geometric link valence at most six has positive invariant
multiplicity at every production auxiliary cutoff.  What remains at cutoff
one that geometric assembly is now closed.  The global mod-two image is
contained in the corrected coarse slab, remains an even cellular surface,
is encoded by one listed coarse physical labelling, and gives a strictly
positive whole-slab raw target whenever the fine odd support is even and the
coarse coupling is positive.  That apparent hypothesis has now also been
discharged for the physical cutoff-one theory: strict positivity of the
actual fine Gibbs term forces every production link multiplicity nonzero,
so the SU(2) parity rule makes the fine odd-spin support an even cellular
surface.  Every positive cutoff-one Gibbs source therefore has an exact
normalized coherent whole-slab row.  The first open gate is the corresponding
all-cutoff recoupling coherence theorem.

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
    GENERAL_SOURCE_KERNEL = (
        "general-source adjacent kernel with retained positive witness"
    )
    FINE_INTERTWINER_WITNESS = (
        "global fine-intertwiner witness extraction from positive physical mass"
    )
    WHOLE_SLAB_RAW_CARRIER = (
        "whole-slab globally link-glued recoupling raw carrier"
    )
    CUTOFF_ONE_COARSE_FACE_DOOR = (
        "positive parity-selected coarse face channels at cutoff one"
    )
    CUTOFF_ONE_COARSE_LINK_DOOR = (
        "positive binary even-parity coarse links at cutoff one"
    )
    CUTOFF_ONE_GLOBAL_COHERENT_TARGET = (
        "globally coherent whole-slab parity target at cutoff one"
    )
    CUTOFF_ONE_POSITIVE_PHYSICAL_COVERAGE = (
        "whole-slab coherent row for every positive cutoff-one Gibbs source"
    )
    COARSE_RECOUPLING_COHERENCE = (
        "globally coherent coarse face/link recoupling field"
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
    "Z4AdjacentCubeGeneralSourceConditionalKernel."
    "generalAdjacentCubeConditionalKernel_row_normalized",
    "Z4AdjacentCubeGeneralSourceConditionalKernel."
    "generalAdjacentCubeConditionalKernel_reflection",
    "Z4AdjacentCubeGeneralSourceConditionalKernel."
    "generalKernel_of_stretched",
    "Z4CubeStretchedSourceCoverageFence."
    "originUnitCube_not_covered_by_stretched_source",
    "CompactDualSlabFineIntertwinerWitness."
    "positivePhysicalTerm_has_fineFusionWitness",
    "CompactDualWholeSlabRecouplingRawKernel."
    "wholeSlabRecouplingRawWeight_nonnegative",
    "CompactDualWholeSlabRecouplingRawKernel."
    "wholeSlabRecouplingConditionalKernel_row_normalized",
    "CompactDualCutoffOneCoarseFaceDoor."
    "fixedFinalFaceRawWeight_parity_pos",
    "CompactDualCutoffOneCoarseLinkDoor."
    "binaryEvenExplicitValenceMultiplicity_pos_of_cutoff",
    "CompactDualCutoffOneParitySlabTarget."
    "CutoffOneEvenSlabSource.toCoherentSlabRecouplingSource",
    "CompactDualCutoffOneParitySlabTarget."
    "cutoffOneWholeSlabConditionalKernel_row_normalized",
    "CompactDualCutoffOnePositivePhysicalClosure."
    "positiveCutoffOnePhysicalTerm_fineOddSupport_even",
    "CompactDualCutoffOnePositivePhysicalClosure."
    "cutoffOnePositivePhysicalSource_row_normalized",
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
    restricted_source_coverage_refuted: bool
    general_source_kernel: bool
    fine_intertwiner_witness: bool
    whole_slab_raw_carrier: bool
    cutoff_one_coarse_face_door: bool
    cutoff_one_coarse_link_door: bool
    cutoff_one_global_coherent_target: bool
    cutoff_one_positive_physical_coverage: bool
    coarse_recoupling_coherence: bool
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
                CD2Subgate.GENERAL_SOURCE_KERNEL,
                self.general_source_kernel,
            ),
            (
                CD2Subgate.FINE_INTERTWINER_WITNESS,
                self.fine_intertwiner_witness,
            ),
            (
                CD2Subgate.WHOLE_SLAB_RAW_CARRIER,
                self.whole_slab_raw_carrier,
            ),
            (
                CD2Subgate.CUTOFF_ONE_COARSE_FACE_DOOR,
                self.cutoff_one_coarse_face_door,
            ),
            (
                CD2Subgate.CUTOFF_ONE_COARSE_LINK_DOOR,
                self.cutoff_one_coarse_link_door,
            ),
            (
                CD2Subgate.CUTOFF_ONE_GLOBAL_COHERENT_TARGET,
                self.cutoff_one_global_coherent_target,
            ),
            (
                CD2Subgate.CUTOFF_ONE_POSITIVE_PHYSICAL_COVERAGE,
                self.cutoff_one_positive_physical_coverage,
            ),
            (
                CD2Subgate.COARSE_RECOUPLING_COHERENCE,
                self.coarse_recoupling_coherence,
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
        restricted_source_coverage_refuted=True,
        general_source_kernel=True,
        fine_intertwiner_witness=True,
        whole_slab_raw_carrier=True,
        cutoff_one_coarse_face_door=True,
        cutoff_one_coarse_link_door=True,
        cutoff_one_global_coherent_target=True,
        cutoff_one_positive_physical_coverage=True,
        coarse_recoupling_coherence=False,
        all_cutoff_global_kernel=False,
        physical_pushforward=False,
        zero_mass_remainder_derived=True,
        universal_l1_cap=Fraction(2),
    )
