/-
# Equal-rank realization of the aligned-diagonal target compiler

For each actual corrected-slab link, realize the selected right target as an
accepted pair of production auxiliary labellings.  Structural recursion then
builds a complete accepted left assignment over any finite linked list.  At
the unique pivot, equal-rank enumeration produces the component-preserving
left carrier `(0,1)` proved in the pairing modules.

Constructive contract: local equal-rank target realization and structural
list recursion only; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabNonpivotPairing
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetAssignment

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetRealization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetAssignment
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. One selected and realized local target -/

theorem alignedDiagonalSwitchRightPhysical_bounded :
    SlabFaceLabellingBounded 1 5 alignedDiagonalSwitchRightPhysical := by
  intro faceId _
  change slabBinarySupportLabelling 5 [] faceId ≤ 1
  exact slabBinarySupportLabelling_le_one 5 [] faceId

def alignedDiagonalSwitchLocalData
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingDataAtLink 5
    alignedDiagonalSwitchLeftPhysical
    alignedDiagonalSwitchRightPhysical linked

def alignedDiagonalSwitchLocalAnchor
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingWitnessDataAtLink 1 5
    alignedDiagonalSwitchLeftPhysical
    alignedDiagonalSwitchRightPhysical
    alignedDiagonalSwitchLeftFineWitness.1
    alignedDiagonalSwitchRightFineWitness.1
    alignedDiagonalSwitchLeftAssignment_mem
    alignedDiagonalSwitchRightAssignment_mem linked

def alignedDiagonalSwitchLocalSource
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingProductionSource
    (slabIncidentPlaqIds 5 linked.1).length
    (alignedDiagonalSwitchLocalData linked)
    (alignedDiagonalSwitchLocalAnchor linked)

def alignedDiagonalSwitchLocalTarget
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  alignedDiagonalSwitchTargetForData
    (slabIncidentPlaqIds 5 linked.1).length
    (alignedDiagonalSwitchLocalData linked) rfl rfl
    (alignedDiagonalSwitchLocalSource linked)

def alignedDiagonalSwitchLocalRealizedPair
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairTargetProductionWitnessPair
    (alignedDiagonalSwitchLocalData linked)
    (alignedDiagonalSwitchLocalAnchor linked)
    alignedDiagonalSwitchLeftPhysical_bounded
    alignedDiagonalSwitchRightPhysical_bounded
    (alignedDiagonalSwitchLocalTarget linked)

def alignedDiagonalSwitchRealizedLeftAuxiliary
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  if linked.1 = alignedDiagonalSwitchPivot then
    alignedDiagonalPivotLeftAuxiliary
  else
    (alignedDiagonalSwitchLocalRealizedPair linked).leftAuxiliary

theorem alignedDiagonalSwitchRealizedLeftAuxiliary_mem
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    alignedDiagonalSwitchRealizedLeftAuxiliary linked ∈
      slabLinkFusionWitnesses 1 5
        alignedDiagonalSwitchLeftPhysical linked.1 := by
  by_cases hpivot : linked.1 = alignedDiagonalSwitchPivot
  · cases linked with
    | mk link hlink =>
        dsimp at hpivot
        subst link
        simpa only [alignedDiagonalSwitchRealizedLeftAuxiliary,
          if_pos rfl] using alignedDiagonalPivotLeftAuxiliary_mem
  · simpa only [alignedDiagonalSwitchRealizedLeftAuxiliary,
      if_neg hpivot] using
      (alignedDiagonalSwitchLocalRealizedPair linked).left_mem

/-! ## 2. Structural accepted assignment -/

def alignedDiagonalSwitchRealizedLeftAssignmentFrom :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, alignedDiagonalSwitchRealizedLeftAuxiliary linked) ::
        alignedDiagonalSwitchRealizedLeftAssignmentFrom rest

theorem alignedDiagonalSwitchRealizedLeftAssignmentFrom_mem :
    forall linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5},
      alignedDiagonalSwitchRealizedLeftAssignmentFrom linkedList ∈
        slabFusionWitnessAssignmentsOn 1 5
          alignedDiagonalSwitchLeftPhysical
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        alignedDiagonalSwitchRealizedLeftAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨alignedDiagonalSwitchRealizedLeftAuxiliary linked,
        alignedDiagonalSwitchRealizedLeftAuxiliary_mem linked, ?_⟩
      exact List.mem_map.mpr
        ⟨alignedDiagonalSwitchRealizedLeftAssignmentFrom rest,
          alignedDiagonalSwitchRealizedLeftAssignmentFrom_mem rest, rfl⟩

/-! ## 3. Equal-rank realization at the selected pivot -/

theorem alignedDiagonalPivotTargetProduction_leftAuxiliary
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      alignedDiagonalSwitchPivotRecouplingData) :
    (slabPhysicalPairTargetProductionWitnessPair
      alignedDiagonalSwitchPivotRecouplingData anchor
      alignedDiagonalSwitchLeftPhysical_bounded
      alignedDiagonalSwitchRightPhysical_bounded
      alignedDiagonalPivotTarget).leftAuxiliary =
        alignedDiagonalPivotLeftAuxiliary := by
  unfold slabPhysicalPairTargetProductionWitnessPair
    slabPhysicalPairProductionWitnessPairOfSource
  rw [alignedDiagonalPivotTarget_rank_source]
  rfl

theorem alignedDiagonalSwitchRealizedLeftAuxiliary_eq_pivot
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hpivot : linked.1 = alignedDiagonalSwitchPivot) :
    alignedDiagonalSwitchRealizedLeftAuxiliary linked =
      alignedDiagonalPivotLeftAuxiliary := by
  unfold alignedDiagonalSwitchRealizedLeftAuxiliary
  rw [if_pos hpivot]

#print axioms alignedDiagonalSwitchRightPhysical_bounded
#print axioms alignedDiagonalSwitchRealizedLeftAuxiliary_mem
#print axioms alignedDiagonalSwitchRealizedLeftAssignmentFrom_mem
#print axioms alignedDiagonalPivotTargetProduction_leftAuxiliary
#print axioms alignedDiagonalSwitchRealizedLeftAuxiliary_eq_pivot

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetRealization
