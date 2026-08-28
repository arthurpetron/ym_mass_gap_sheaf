/-
# Equal-rank realization of the outward Y/Z target compiler

For each actual corrected-slab link, represent the target selected by
`outwardYZSwitchTargetForData` as an accepted pair of production auxiliary
labellings.  Structural recursion then builds a complete accepted left
assignment over any finite linked list.  At the unique pivot, equal-rank
enumeration produces the written `(2,1)` left-tree carrier.

The literal pairing theorem proves that this carrier crosses the Y/Z cut.
Accordingly, this module certifies only an accepted, weight-preserving index
realization.  It does not claim that equal rank preserves the native
right-tree strand connectivity of the selected target; that missing basis
coherence is the next compiler frontier.

Constructive contract: local equal-rank target realization and structural
list recursion only; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNonpivotPairing
import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabTargetAssignment

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabTargetRealization

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
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabTargetAssignment
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. One selected and realized local target -/

theorem outwardYZSwitchRightPhysical_bounded :
    SlabFaceLabellingBounded 1 5 outwardYZSwitchRightPhysical := by
  intro faceId _
  change slabBinarySupportLabelling 5 [] faceId ≤ 1
  exact slabBinarySupportLabelling_le_one 5 [] faceId

def outwardYZSwitchLocalData
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingDataAtLink 5
    outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked

def outwardYZSwitchLocalAnchor
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingWitnessDataAtLink 1 5
    outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical
    outwardYZSwitchLeftFineWitness.1 outwardYZSwitchRightFineWitness.1
    outwardYZSwitchLeftAssignment_mem
    outwardYZSwitchRightAssignment_mem linked

def outwardYZSwitchLocalSource
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingProductionSource
    (slabIncidentPlaqIds 5 linked.1).length
    (outwardYZSwitchLocalData linked)
    (outwardYZSwitchLocalAnchor linked)

def outwardYZSwitchLocalTarget
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  outwardYZSwitchTargetForData
    (slabIncidentPlaqIds 5 linked.1).length
    (outwardYZSwitchLocalData linked) rfl rfl
    (outwardYZSwitchLocalSource linked)

def outwardYZSwitchLocalRealizedPair
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairTargetProductionWitnessPair
    (outwardYZSwitchLocalData linked)
    (outwardYZSwitchLocalAnchor linked)
    outwardYZSwitchLeftPhysical_bounded
    outwardYZSwitchRightPhysical_bounded
    (outwardYZSwitchLocalTarget linked)

def outwardYZSwitchRealizedLeftAuxiliary
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  if linked.1 = outwardYZSwitchPivot then
    outwardYZPivotLeftAuxiliary
  else
    (outwardYZSwitchLocalRealizedPair linked).leftAuxiliary

theorem outwardYZSwitchRealizedLeftAuxiliary_mem
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    outwardYZSwitchRealizedLeftAuxiliary linked ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical linked.1 := by
  by_cases hpivot : linked.1 = outwardYZSwitchPivot
  · cases linked with
    | mk link hlink =>
        dsimp at hpivot
        subst link
        simpa only [outwardYZSwitchRealizedLeftAuxiliary, if_pos rfl] using
          outwardYZPivotLeftAuxiliary_mem
  · simpa only [outwardYZSwitchRealizedLeftAuxiliary, if_neg hpivot] using
      (outwardYZSwitchLocalRealizedPair linked).left_mem

/-! ## 2. Structural accepted assignment -/

def outwardYZSwitchRealizedLeftAssignmentFrom :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, outwardYZSwitchRealizedLeftAuxiliary linked) ::
        outwardYZSwitchRealizedLeftAssignmentFrom rest

theorem outwardYZSwitchRealizedLeftAssignmentFrom_mem :
    forall linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      outwardYZSwitchRealizedLeftAssignmentFrom linkedList ∈
        slabFusionWitnessAssignmentsOn 1 5 outwardYZSwitchLeftPhysical
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        outwardYZSwitchRealizedLeftAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨outwardYZSwitchRealizedLeftAuxiliary linked,
        outwardYZSwitchRealizedLeftAuxiliary_mem linked, ?_⟩
      exact List.mem_map.mpr
        ⟨outwardYZSwitchRealizedLeftAssignmentFrom rest,
          outwardYZSwitchRealizedLeftAssignmentFrom_mem rest, rfl⟩

/-! ## 3. Equal-rank realization at the selected pivot -/

theorem outwardYZPivotTargetProduction_leftAuxiliary
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      outwardYZSwitchPivotRecouplingData) :
    (slabPhysicalPairTargetProductionWitnessPair
      outwardYZSwitchPivotRecouplingData anchor
      outwardYZSwitchLeftPhysical_bounded
      outwardYZSwitchRightPhysical_bounded
      outwardYZPivotTarget).leftAuxiliary =
        outwardYZPivotLeftAuxiliary := by
  unfold slabPhysicalPairTargetProductionWitnessPair
    slabPhysicalPairProductionWitnessPairOfSource
  rw [outwardYZPivotTarget_rank_source]
  rfl

theorem outwardYZSwitchRealizedLeftAuxiliary_eq_pivot
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hpivot : linked.1 = outwardYZSwitchPivot) :
    outwardYZSwitchRealizedLeftAuxiliary linked =
      outwardYZPivotLeftAuxiliary := by
  unfold outwardYZSwitchRealizedLeftAuxiliary
  rw [if_pos hpivot]

#print axioms outwardYZSwitchRightPhysical_bounded
#print axioms outwardYZSwitchRealizedLeftAuxiliary_mem
#print axioms outwardYZSwitchRealizedLeftAssignmentFrom_mem
#print axioms outwardYZPivotTargetProduction_leftAuxiliary
#print axioms outwardYZSwitchRealizedLeftAuxiliary_eq_pivot

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabTargetRealization
