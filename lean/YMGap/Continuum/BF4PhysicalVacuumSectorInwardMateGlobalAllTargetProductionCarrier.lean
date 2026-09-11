/-
# Recode the global all-target event into the production BF4 carrier

The all-target construction records each accepted local SU(2) witness in a
common root-first face order on the central cube.  The literal expanded BF4
carrier instead enumerates witnesses in production incidence order.  The two
complete fibers have the same proved finite cardinality, but their auxiliary
labels need not agree.

This module performs the missing constructive compiler.  It serializes the
fixed-order target by its exact residual code, reads that code's written rank,
and selects the same rank in the literal production-order fiber.  Every
all-target representative therefore becomes an actual member of
`slabExpandedFineSources`, with exactly the same unit-Haar BF4 weight.

This is a same-object carrier and weight theorem.  Injectivity of the recoded
representatives, construction of a two-copy conditional joint, posterior
variance, an OS form bound, a spectral gap, and continuum control remain
separate obligations.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
import YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
import YMGap.Continuum.FiniteBistochasticRankReindex

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Equal-rank compilation into the production fiber -/

/-- The extent-one corrected slab at the fixed strong-coupling anchor. -/
def globalInwardMateAnchorSlabData (K : Nat) : SlabPhysicalData :=
  { coupling := anchorCoupling
    coupling_nonnegative := by decide
    cutoff := K
    half := 0 }

/-- The literal production fiber and the fixed-order residual-code fiber have
the same cardinality for every bounded physical target. -/
theorem globalInwardMateProductionFiber_length_eq_targetCodes
    (K : Nat) (target : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded K 1 target) :
    (slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K) target).length =
      (cubeInwardMateFixedOrderTargetResidualCodes K target).length := by
  calc
    (slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K) target).length =
        slabExplicitLinkMultiplicityProduct K 1 target := by
      simpa [globalInwardMateAnchorSlabData,
        SlabPhysicalData.extent, centralExtent] using
        (slabFineFusionWitnesses_length
          (globalInwardMateAnchorSlabData K) target)
    _ = (cubeInwardMateFixedOrderTargetTuples K target).length :=
      (cubeInwardMateFixedOrderTargetTuples_length
        K target hbounded).symm
    _ = (cubeInwardMateFixedOrderTargetResidualCodes K target).length :=
      (cubeInwardMateFixedOrderTargetResidualCodes_length K target).symm

/-- Compile one fixed-order residual code to the production-order assignment
at the same written rank.  The empty assignment is only a total fallback;
membership below proves it is not inspected on the target-code carrier. -/
def globalInwardMateProductionRawAt
    (K : Nat) (target : EdgeLabelling)
    (code : List (List Nat) × List (List Nat)) :
    SlabFusionWitnessAssignment :=
  equalRankReindex []
    (slabFineFusionWitnesses (globalInwardMateAnchorSlabData K) target)
    (cubeInwardMateFixedOrderTargetResidualCodes K target) code

/-- Equal-rank compilation lands in the literal production-order fiber. -/
theorem globalInwardMateProductionRawAt_mem
    (K : Nat) (target : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded K 1 target)
    (code : List (List Nat) × List (List Nat))
    (hcode : code ∈ cubeInwardMateFixedOrderTargetResidualCodes K target) :
    globalInwardMateProductionRawAt K target code ∈
      slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K) target := by
  exact equalRankReindex_mem []
    (slabFineFusionWitnesses (globalInwardMateAnchorSlabData K) target)
    (cubeInwardMateFixedOrderTargetResidualCodes K target)
    (globalInwardMateProductionFiber_length_eq_targetCodes
      K target hbounded) code hcode

/-! ## 2. Every retained representative is an actual expanded BF4 atom -/

/-- The production-order auxiliary assignment selected for one realized
all-target representative. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    SlabFusionWitnessAssignment :=
  globalInwardMateProductionRawAt K
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
    (globalInwardMateTargetRepresentativeResidualCode source)

private theorem representative_mem_own_physical_block
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetRepresentatives K hK) :
    source ∈ globalInwardMateTargetPhysicalBlockRepresentatives
      K hK
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source) := by
  unfold globalInwardMateTargetPhysicalBlockRepresentatives
  apply List.mem_filter.mpr
  exact ⟨hsource, by simp⟩

/-- Every selected representative's recoded assignment is accepted in the
literal production-order fiber over its physical target. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetRepresentatives K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw source ∈
      slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K)
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source) := by
  apply globalInwardMateProductionRawAt_mem K
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_bounded source)
  exact globalInwardMateTargetPhysicalBlock_residualCode_mem_targetCodes
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem source) source
    (representative_mem_own_physical_block source hsource)

/-- The same-object production expanded atom attached to one all-target
representative. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    SlabLabelling × SlabFusionWitnessAssignment :=
  (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source,
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw source)

/-- Every recoded representative is a literal member of the production BF4
expanded carrier, not merely an equinumerous fixed-order presentation. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetRepresentatives K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom source ∈
      slabExpandedFineSources (globalInwardMateAnchorSlabData K) := by
  have hphysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source ∈
        (globalInwardMateAnchorSlabData K).physicalLabellings := by
    simpa [globalInwardMateAnchorSlabData,
      SlabPhysicalData.physicalLabellings, SlabPhysicalData.faceEdges,
      SlabPhysicalData.extent, centralExtent] using
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem source)
  have hraw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw source ∈
        slabFineFusionWitnesses (globalInwardMateAnchorSlabData K)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source) :=
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw_mem
      source hsource
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom
    slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source,
    hphysical, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw source,
    hraw, rfl⟩

/-! ## 3. The recoding preserves the exact BF4 atom weight -/

/-- Weight of the recoded target as a literal entry of the production
expanded carrier. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom source)

/-- Unit Haar counting makes the production-order recoding exactly
weight-preserving. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight_eqv_targetWeight
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight source ≈
      GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight source := by
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor anchorCoupling K 1
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)) _ ?_ ?_
  · unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
      slabExpandedFineSourceWeight
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom
    simpa [globalInwardMateAnchorSlabData,
      SlabPhysicalData.extent, centralExtent] using
      (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
        (globalInwardMateAnchorSlabData K)
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw source))
  · exact Q'.eqv_symm
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_faceFactor
        source)

/-- The total recoded production-target weight equals the previously
normalized distinct target weight term by term. -/
theorem globalInwardMateProductionTargets_weight_eqv
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
        (globalInwardMateTargetRepresentatives K hK) ≈
      listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
        (globalInwardMateTargetRepresentatives K hK) := by
  apply listQSum_congr
  intro source
  exact GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight_eqv_targetWeight
    source

/-- The positive retained fraction is now carried by literal production BF4
atoms.  Collision-freeness of the recoded representative list is deliberately
not asserted in this module. -/
theorem globalInwardMateRetainedTargetFraction_partition_le_productionTargets
    (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateRetainedTargetFraction *
        slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
        (globalInwardMateTargetRepresentatives K hK) := by
  exact Q'.le_trans' _ _ _
    (globalInwardMateRetainedTargetFraction_partition_le_targets K hK)
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (globalInwardMateProductionTargets_weight_eqv K hK)))

#print axioms globalInwardMateAnchorSlabData
#print axioms globalInwardMateProductionFiber_length_eq_targetCodes
#print axioms globalInwardMateProductionRawAt
#print axioms globalInwardMateProductionRawAt_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight_eqv_targetWeight
#print axioms globalInwardMateProductionTargets_weight_eqv
#print axioms globalInwardMateRetainedTargetFraction_partition_le_productionTargets

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
