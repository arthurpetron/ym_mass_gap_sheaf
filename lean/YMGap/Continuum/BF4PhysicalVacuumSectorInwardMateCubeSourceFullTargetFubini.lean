/-
# Exact Fubini over realized complete-source target fibers

Every complete first-stretched source belongs to exactly one realized exact
target-key fiber.  The representative partition therefore recovers the
complete source weight without loss.  Applying the established strict bound
inside every representative fiber gives one aggregate inequality whose right
side is the sum of `(8/25)^peelSize` times the distinct realized lowered-target
weights.

This module does not yet compare that target sum with the pure inward-mate
product.  It exposes precisely that remaining target-side congestion problem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFiber

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> left item ≤ right item) ->
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm =>
      Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hterm item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Source and target summands -/

/-- The exact anchor weight of one retained complete source entry. -/
def cubeInwardMateFullSourceEntryWeight
    (K : Nat) {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) : Q' :=
  let D : SlabPhysicalData :=
    { coupling := anchorCoupling
      coupling_nonnegative := by decide
      cutoff := K
      half := 0 }
  retainedFineIntertwinerPhysicalFiberWeight D physical entry.raw

/-- The strict-rate-weighted lowered target attached to one realized
representative. -/
def cubeInwardMateFullPeelRepresentativeTargetWeight
    (K : Nat) {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) : Q' :=
  let D : SlabPhysicalData :=
    { coupling := anchorCoupling
      coupling_nonnegative := by decide
      cutoff := K
      half := 0 }
  componentAdaptiveEntropyAnchorRatio ^
      representative.adaptiveInverseData.peelSize *
    presentedSlabFusionWitnessAssignmentFiberWeight D
      representative.adaptiveInverseData.lowerPhysical
      representative.adaptiveInverseData.lowerAssignment

/-! ## 2. Exact representative Fubini and aggregate contraction -/

/-- The realized representative fibers recover the complete enumerated
first-stretched source weight exactly. -/
theorem cubeInwardMateFullPeelRepresentativeFibers_weight_total
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    listQSum
        (fun representative =>
          listQSum (cubeInwardMateFullSourceEntryWeight K)
            (cubeInwardMateFullPeelTargetFiber representative))
        (cubeInwardMateFullPeelTargetRepresentatives
          K physical hK hbounded) ≈
      listQSum (cubeInwardMateFullSourceEntryWeight K)
        (enumeratedCubeInwardMateFullSources
          K physical hK hbounded) := by
  simpa only [cubeInwardMateFullPeelTargetRepresentatives,
    cubeInwardMateFullPeelTargetFiber] using
      keyRepresentativeFibers_weight_total
        (enumeratedCubeInwardMateFullSources K physical hK hbounded)
        (cubeInwardMateFullSourceEntryWeight K)
        EnumeratedCubeInwardMateFullSource.targetKey

/-- **Aggregate complete-source contraction.**  The entire enumerated
first-stretched source mass is bounded by the strict-rate-weighted sum of its
distinct realized lowered presented targets. -/
theorem cubeInwardMateFullSources_weight_sum_le_representativeTargets
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    listQSum (cubeInwardMateFullSourceEntryWeight K)
        (enumeratedCubeInwardMateFullSources
          K physical hK hbounded) ≤
      listQSum (cubeInwardMateFullPeelRepresentativeTargetWeight K)
        (cubeInwardMateFullPeelTargetRepresentatives
          K physical hK hbounded) := by
  have hpartition :=
    cubeInwardMateFullPeelRepresentativeFibers_weight_total
      K physical hK hbounded
  have hfibers := listQSum_le_termwise_local
    (fun representative =>
      listQSum (cubeInwardMateFullSourceEntryWeight K)
        (cubeInwardMateFullPeelTargetFiber representative))
    (cubeInwardMateFullPeelRepresentativeTargetWeight K)
    (cubeInwardMateFullPeelTargetRepresentatives K physical hK hbounded)
    (fun representative _ => by
      exact cubeInwardMateFullPeelTargetFiber_weight_sum_le representative)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition)) hfibers

#print axioms cubeInwardMateFullSourceEntryWeight
#print axioms cubeInwardMateFullPeelRepresentativeTargetWeight
#print axioms cubeInwardMateFullPeelRepresentativeFibers_weight_total
#print axioms cubeInwardMateFullSources_weight_sum_le_representativeTargets

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
