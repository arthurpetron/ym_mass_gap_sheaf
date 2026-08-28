/-
# Weighted exterior-component fibers at arbitrary coupling

The adaptive inverse-fiber code bounds a fixed accepted component-removal
fiber of size `n` by `10,240,000^n`.  At the strong-coupling anchor, the
one-copy heat payment `1/32,000,000` contracts that entropy to `(8/25)^n`.

The high-spin component theorem supplies the identical one-copy payment for
every fixed rational `0 < w < 1`, provided the component passes the executable
reserve check at `anchorPaidExteriorThreshold w`.  This module combines the
two existing facts.  For a duplicate-free fixed-target family of exterior
component removals, the complete expanded BF4 source-weight sum obeys

```text
source fiber sum <= (8/25)^n * target fiber weight.
```

The strict rate is independent of `w`; all coupling dependence is exposed in
the moving finite-core threshold and its reserve check.

This is a genuine non-abelian strand-to-weight summation compiler.  It does
not assert that every source has an exterior component, sum over the remaining
core-blocked family, or prove a posterior-variance fraction.

Constructive contract: the existing injective finite code, finite rational
summation, and the accepted high-spin component path only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Expanded-fiber nonnegativity at arbitrary coupling -/

private theorem packetCoefficient_nonnegative
    {w : Q'} (hw0 : (0 : Q') <= w) (cutoff spin : Nat) :
    (0 : Q') <= coeffAt (heatKernelPacket cutoff w) spin := by
  by_cases hspin : spin < cutoff + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hw0 spin
  · have hlarge : cutoff < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket cutoff w) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative
    {w : Q'} (hw0 : (0 : Q') <= w)
    (cutoff : Nat) (physical : EdgeLabelling) : forall ids : List Nat,
    (0 : Q') <= eliminateLinks
      (fun id => coeffAt (heatKernelPacket cutoff w) (physical id)) ids
  | [] => Q'.zero_le_one
  | _ :: ids =>
      Q'.mul_nonneg _ _
        (packetCoefficient_nonnegative hw0 cutoff _)
        (eliminateLinks_nonnegative hw0 cutoff physical ids)

/-- Every literal expanded fine-intertwiner fiber entry is nonnegative for
every nonnegative coupling. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_nonnegative
    {w : Q'} (hw0 : (0 : Q') <= w)
    (cutoff half : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := hw0
        cutoff := cutoff
        half := half }
    (0 : Q') <=
      retainedFineIntertwinerPhysicalFiberWeight D physical assignment := by
  dsimp only
  unfold retainedFineIntertwinerPhysicalFiberWeight
    retainedFineIntertwinerRawWeight
    slabParametricKPhysicalFaceFactor
  exact Q'.mul_nonneg _ _
    (eliminateLinks_nonnegative hw0 cutoff physical
      (slabPhysicalFaceEdges (centralExtent half)))
    Q'.zero_le_one

/-! ## 2. Strict fixed-target exterior-fiber contraction -/

/-- **Arbitrary-coupling exterior fiber estimate.**  A duplicate-free family
of accepted sources, all removing one component of size `peelSize` to the same
target and all passing the moving high-spin reserve check, has total expanded
weight at most `(8/25)^peelSize` times the target weight. -/
theorem componentAdaptiveExteriorRemovalSources_weight_sum_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half rootFaceId peelSize : Nat)
    (targetPhysical : SlabLabelling)
    (targetAssignment : SlabFusionWitnessAssignment)
    (sources : List (SlabLabelling × SlabFusionWitnessAssignment))
    (hsources : sources.Nodup)
    (witness : forall source, source ∈ sources ->
      ComponentAdaptiveRemovalWitness cutoff (centralExtent half)
        rootFaceId peelSize targetPhysical targetAssignment source)
    (hbounded : forall source, source ∈ sources ->
      SlabFaceLabellingBounded cutoff (centralExtent half) source.1)
    (hexterior : forall source (hsource : source ∈ sources),
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
        (witness source hsource).seed
        (anchorPaidExteriorThreshold w) = true) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := Q'.le_of_lt hw0
        cutoff := cutoff
        half := half }
    listQSum
        (fun source => retainedFineIntertwinerPhysicalFiberWeight
          D source.1 source.2) sources <=
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        retainedFineIntertwinerPhysicalFiberWeight
          D targetPhysical targetAssignment := by
  dsimp only
  unfold componentAdaptiveEntropyAnchorRatio
  apply fixedCardinalityWeightedSum_le
  · exact componentAdaptiveRemovalSources_length_le
      cutoff (centralExtent half) rootFaceId peelSize
      targetPhysical targetAssignment sources hsources witness
  · decide
  · exact retainedFineIntertwinerPhysicalFiberWeight_nonnegative
      (Q'.le_of_lt hw0) cutoff half targetPhysical targetAssignment
  · intro source hsource
    have hweight :=
      SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_anchorPaidExterior_le
        hw0 hw1 cutoff half (witness source hsource).seed
          (hexterior source hsource) (hbounded source hsource)
    dsimp only at hweight
    rw [(witness source hsource).peelSize_eq,
      (witness source hsource).lowerPhysical_eq,
      (witness source hsource).lowerAssignment_eq] at hweight
    exact hweight

#print axioms retainedFineIntertwinerPhysicalFiberWeight_nonnegative
#print axioms componentAdaptiveExteriorRemovalSources_weight_sum_le

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
