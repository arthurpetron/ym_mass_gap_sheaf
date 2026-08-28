/-
# Equal-rank realization of the reflected bent-cube target compiler

Realize every selected right target as an accepted production auxiliary pair.
At the unique pivot, equal-rank enumeration yields the component-preserving
left carrier `(1,0)`; structural recursion builds the complete accepted left
assignment over any finite actual-link list.

Constructive contract: local equal-rank realization and structural recursion
only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetAssignment

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetRealization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetAssignment
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

theorem reflectedBentSwitchRightPhysical_bounded :
    SlabFaceLabellingBounded 1 5 reflectedBentSwitchRightPhysical := by
  intro faceId _
  change slabBinarySupportLabelling 5 [] faceId ≤ 1
  exact slabBinarySupportLabelling_le_one 5 [] faceId

def reflectedBentSwitchLocalData
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingDataAtLink 5
    reflectedBentSwitchLeftPhysical
    reflectedBentSwitchRightPhysical linked

def reflectedBentSwitchLocalAnchor
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingWitnessDataAtLink 1 5
    reflectedBentSwitchLeftPhysical
    reflectedBentSwitchRightPhysical
    reflectedBentLeftFineWitness.1
    reflectedBentRightFineWitness.1
    reflectedBentSwitchLeftAssignment_mem
    reflectedBentSwitchRightAssignment_mem linked

def reflectedBentSwitchLocalSource
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingProductionSource
    (slabIncidentPlaqIds 5 linked.1).length
    (reflectedBentSwitchLocalData linked)
    (reflectedBentSwitchLocalAnchor linked)

def reflectedBentSwitchLocalTarget
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  reflectedBentSwitchTargetForData
    (slabIncidentPlaqIds 5 linked.1).length
    (reflectedBentSwitchLocalData linked) rfl rfl
    (reflectedBentSwitchLocalSource linked)

def reflectedBentSwitchLocalRealizedPair
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairTargetProductionWitnessPair
    (reflectedBentSwitchLocalData linked)
    (reflectedBentSwitchLocalAnchor linked)
    reflectedBentSwitchLeftPhysical_bounded
    reflectedBentSwitchRightPhysical_bounded
    (reflectedBentSwitchLocalTarget linked)

def reflectedBentSwitchRealizedLeftAuxiliary
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  if linked.1 = reflectedBentSwitchPivot then
    reflectedBentPivotLeftAuxiliary
  else
    (reflectedBentSwitchLocalRealizedPair linked).leftAuxiliary

theorem reflectedBentSwitchRealizedLeftAuxiliary_mem
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentSwitchRealizedLeftAuxiliary linked ∈
      slabLinkFusionWitnesses 1 5
        reflectedBentSwitchLeftPhysical linked.1 := by
  by_cases hpivot : linked.1 = reflectedBentSwitchPivot
  · cases linked with
    | mk link hlink =>
        dsimp at hpivot
        subst link
        simpa only [reflectedBentSwitchRealizedLeftAuxiliary,
          if_pos rfl] using reflectedBentPivotLeftAuxiliary_mem
  · simpa only [reflectedBentSwitchRealizedLeftAuxiliary,
      if_neg hpivot] using
      (reflectedBentSwitchLocalRealizedPair linked).left_mem

def reflectedBentSwitchRealizedLeftAssignmentFrom :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, reflectedBentSwitchRealizedLeftAuxiliary linked) ::
        reflectedBentSwitchRealizedLeftAssignmentFrom rest

theorem reflectedBentSwitchRealizedLeftAssignmentFrom_mem :
    forall linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentSwitchRealizedLeftAssignmentFrom linkedList ∈
        slabFusionWitnessAssignmentsOn 1 5
          reflectedBentSwitchLeftPhysical
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentSwitchRealizedLeftAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentSwitchRealizedLeftAuxiliary linked,
        reflectedBentSwitchRealizedLeftAuxiliary_mem linked, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentSwitchRealizedLeftAssignmentFrom rest,
          reflectedBentSwitchRealizedLeftAssignmentFrom_mem rest, rfl⟩

theorem reflectedBentPivotTargetProduction_leftAuxiliary
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      reflectedBentSwitchPivotRecouplingData) :
    (slabPhysicalPairTargetProductionWitnessPair
      reflectedBentSwitchPivotRecouplingData anchor
      reflectedBentSwitchLeftPhysical_bounded
      reflectedBentSwitchRightPhysical_bounded
      reflectedBentPivotTarget).leftAuxiliary =
        reflectedBentPivotLeftAuxiliary := by
  unfold slabPhysicalPairTargetProductionWitnessPair
    slabPhysicalPairProductionWitnessPairOfSource
  rw [reflectedBentPivotTarget_rank_source]
  rfl

theorem reflectedBentSwitchRealizedLeftAuxiliary_eq_pivot
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hpivot : linked.1 = reflectedBentSwitchPivot) :
    reflectedBentSwitchRealizedLeftAuxiliary linked =
      reflectedBentPivotLeftAuxiliary := by
  unfold reflectedBentSwitchRealizedLeftAuxiliary
  rw [if_pos hpivot]

#print axioms reflectedBentSwitchRightPhysical_bounded
#print axioms reflectedBentSwitchRealizedLeftAuxiliary_mem
#print axioms reflectedBentSwitchRealizedLeftAssignmentFrom_mem
#print axioms reflectedBentPivotTargetProduction_leftAuxiliary
#print axioms reflectedBentSwitchRealizedLeftAuxiliary_eq_pivot

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetRealization
