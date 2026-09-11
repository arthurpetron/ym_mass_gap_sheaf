/-
# Weighted contraction of certified presented adaptive inverse fibers

The preceding module injects every fixed-target raw source family into a
carrier of size at most `10240000 ^ peelSize`.  The certified supported peel
pays `anchorFaceCoefficient ^ peelSize` pointwise.  This module packages those
two witnesses together and applies the existing finite weighted-sum compiler,
giving the exact contraction

  source fiber sum <= (8/25)^peelSize * target weight.

The family and its fixed-target witnesses remain explicit inputs.  Enumerating
all first-stretched sources into these fibers and summing roots and peel sizes
is downstream.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Pointwise weighted certificates -/

/-- A pointwise weighted removal certificate over a specified common target. -/
structure PresentedAdaptiveAnchorRemovalWitness
    (K rootFaceId peelSize : Nat)
    (targetPhysical : SlabLabelling)
    (targetAssignment : PresentedSlabFusionWitnessAssignment K 1
      targetPhysical (boundaryCompleteSlabLinks 1))
    (source : SlabLabelling × SlabFusionWitnessAssignment) : Type where
  removal : PresentedAdaptiveRemovalWitness K 1 rootFaceId peelSize
    targetPhysical targetAssignment source
  weight_le :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := K
        half := 0 }
    retainedFineIntertwinerPhysicalFiberWeight D source.1 source.2 <=
      anchorFaceCoefficient ^ peelSize *
        presentedSlabFusionWitnessAssignmentFiberWeight D
          targetPhysical targetAssignment

/-! ## 2. Strict fixed-target weighted contraction -/

/-- **Certified presented fixed-fiber contraction.**  A duplicate-free finite
family of raw sources with a common lowered presented target has total anchor
weight at most `(8/25)^peelSize` times that target's weight. -/
theorem presentedAdaptiveAnchorRemovalSources_weight_sum_le
    (K rootFaceId peelSize : Nat)
    (targetPhysical : SlabLabelling)
    (targetAssignment : PresentedSlabFusionWitnessAssignment K 1
      targetPhysical (boundaryCompleteSlabLinks 1))
    (sources : List (SlabLabelling × SlabFusionWitnessAssignment))
    (hsources : sources.Nodup)
    (witness : forall source, source ∈ sources ->
      PresentedAdaptiveAnchorRemovalWitness K rootFaceId peelSize
        targetPhysical targetAssignment source) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := K
        half := 0 }
    listQSum
        (fun source => retainedFineIntertwinerPhysicalFiberWeight
          D source.1 source.2) sources <=
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        presentedSlabFusionWitnessAssignmentFiberWeight
          D targetPhysical targetAssignment := by
  dsimp only
  unfold componentAdaptiveEntropyAnchorRatio
  apply fixedCardinalityWeightedSum_le
  · exact presentedAdaptiveRemovalSources_length_le K 1 rootFaceId peelSize
      targetPhysical targetAssignment sources hsources
      (fun source hsource => (witness source hsource).removal)
  · decide
  · unfold presentedSlabFusionWitnessAssignmentFiberWeight
    exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
      K 0 targetPhysical
        (presentedSlabFusionWitnessAssignmentRaw
          (boundaryCompleteSlabLinks 1) targetAssignment)
  · intro source hsource
    exact (witness source hsource).weight_le

#print axioms PresentedAdaptiveAnchorRemovalWitness
#print axioms presentedAdaptiveAnchorRemovalSources_weight_sum_le

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight
