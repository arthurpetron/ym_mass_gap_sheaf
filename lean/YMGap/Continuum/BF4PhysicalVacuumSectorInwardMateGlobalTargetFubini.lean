/-
# Exact Fubini over all-physical realized target fibers

The global source carrier has now been partitioned by its exact lowered
presented target, and every realized fiber obeys the strict adaptive payment.
This module performs the corresponding finite Fubini without loss: each global
source occurs in exactly one representative fiber, after which the fiberwise
inequalities contract the full first-stretched mass to one sum over distinct
global lowered targets.

The remaining obstruction is entirely target-side congestion.  This module
does not yet bound that target sum by the physical partition and makes no
total-mass, transition, posterior, operator, or continuum claim.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFiber

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFubini

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFiber
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

/-! ## 1. The global representative target summand -/

/-- The strict-rate-weighted lowered target attached to one distinct global
representative. -/
def globalCubeInwardMateFullPeelRepresentativeTargetWeight
    (K : Nat) {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) : Q' :=
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

/-- The realized global representative fibers recover the complete
all-physical first-stretched source weight exactly. -/
theorem globalCubeInwardMateFullPeelRepresentativeFibers_weight_total
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        (fun representative =>
          listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
            (globalCubeInwardMateFullPeelTargetFiber representative))
        (globalCubeInwardMateFullPeelTargetRepresentatives K hK) ≈
      listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalEnumeratedCubeInwardMateFullSources K hK) := by
  simpa only [globalCubeInwardMateFullPeelTargetRepresentatives,
    globalCubeInwardMateFullPeelTargetFiber] using
      keyRepresentativeFibers_weight_total
        (globalEnumeratedCubeInwardMateFullSources K hK)
        GlobalEnumeratedCubeInwardMateFullSource.weight
        GlobalEnumeratedCubeInwardMateFullSource.targetKey

/-- **Aggregate all-physical complete-source contraction.**  The complete
global first-stretched source mass is bounded by one strict-rate-weighted sum
over distinct realized lowered presented targets. -/
theorem globalCubeInwardMateFullSources_weight_sum_le_representativeTargets
    (K : Nat) (hK : 1 ≤ K) :
    listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalEnumeratedCubeInwardMateFullSources K hK) ≤
      listQSum (globalCubeInwardMateFullPeelRepresentativeTargetWeight K)
        (globalCubeInwardMateFullPeelTargetRepresentatives K hK) := by
  have hpartition :=
    globalCubeInwardMateFullPeelRepresentativeFibers_weight_total K hK
  have hfibers := listQSum_le_termwise_local
    (fun representative =>
      listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalCubeInwardMateFullPeelTargetFiber representative))
    (globalCubeInwardMateFullPeelRepresentativeTargetWeight K)
    (globalCubeInwardMateFullPeelTargetRepresentatives K hK)
    (fun representative _ => by
      exact globalCubeInwardMateFullPeelTargetFiber_weight_sum_le
        representative)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition)) hfibers

#print axioms globalCubeInwardMateFullPeelRepresentativeTargetWeight
#print axioms globalCubeInwardMateFullPeelRepresentativeFibers_weight_total
#print axioms globalCubeInwardMateFullSources_weight_sum_le_representativeTargets

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFubini
