/-
# Production realization of the two-pivot outward repair target

Realize every selected target column as accepted production auxiliaries.  The
two exceptional links are overridden by their explicit component-preserving
canonical-left auxiliaries; all other links use the generic equal-rank target
realization.  Structural recursion then constructs an accepted complete left
assignment on every finite linked list.

Constructive contract: local rank realization and structural list recursion
only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetAssignment

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetRealization

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
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotTarget
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetAssignment

theorem outwardYZCanonicalRepairSwitchRightPhysical_bounded :
    SlabFaceLabellingBounded 1 5
      outwardYZCanonicalRepairSwitchRightPhysical := by
  intro faceId _
  change slabBinarySupportLabelling 5 [] faceId ≤ 1
  exact slabBinarySupportLabelling_le_one 5 [] faceId

def outwardYZCanonicalRepairLocalData
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingDataAtLink 5
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchRightPhysical linked

def outwardYZCanonicalRepairLocalAnchor
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingWitnessDataAtLink 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchRightPhysical
    outwardYZCanonicalRepairLeftFineWitness.1
    outwardYZCanonicalRepairRightFineWitness.1
    outwardYZCanonicalRepairSwitchLeftAssignment_mem
    outwardYZCanonicalRepairSwitchRightAssignment_mem linked

def outwardYZCanonicalRepairLocalSource
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingProductionSource
    (slabIncidentPlaqIds 5 linked.1).length
    (outwardYZCanonicalRepairLocalData linked)
    (outwardYZCanonicalRepairLocalAnchor linked)

def outwardYZCanonicalRepairLocalTarget
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  outwardYZCanonicalRepairTargetForData
    (slabIncidentPlaqIds 5 linked.1).length
    (outwardYZCanonicalRepairLocalData linked) rfl rfl
    (outwardYZCanonicalRepairLocalSource linked)

def outwardYZCanonicalRepairLocalRealizedPair
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairTargetProductionWitnessPair
    (outwardYZCanonicalRepairLocalData linked)
    (outwardYZCanonicalRepairLocalAnchor linked)
    outwardYZCanonicalRepairSwitchLeftPhysical_bounded
    outwardYZCanonicalRepairSwitchRightPhysical_bounded
    (outwardYZCanonicalRepairLocalTarget linked)

def outwardYZCanonicalRepairRealizedLeftAuxiliary
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  if linked.1 = outwardYZCanonicalRepairSwitchSpatialPivot then
    outwardYZCanonicalRepairSpatialLeftAuxiliary
  else if linked.1 = outwardYZCanonicalRepairSwitchTemporalPivot then
    outwardYZCanonicalRepairTemporalLeftAuxiliary
  else
    (outwardYZCanonicalRepairLocalRealizedPair linked).leftAuxiliary

theorem outwardYZCanonicalRepairRealizedLeftAuxiliary_mem
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    outwardYZCanonicalRepairRealizedLeftAuxiliary linked ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical linked.1 := by
  by_cases hspatial :
      linked.1 = outwardYZCanonicalRepairSwitchSpatialPivot
  · cases linked with
    | mk link hlink =>
        dsimp at hspatial
        subst link
        simpa only [outwardYZCanonicalRepairRealizedLeftAuxiliary,
          if_pos rfl] using
            outwardYZCanonicalRepairSpatialLeftAuxiliary_mem
  · by_cases htemporal :
        linked.1 = outwardYZCanonicalRepairSwitchTemporalPivot
    · cases linked with
      | mk link hlink =>
          dsimp at htemporal hspatial
          subst link
          simpa only [outwardYZCanonicalRepairRealizedLeftAuxiliary,
            if_neg hspatial, if_pos rfl] using
              outwardYZCanonicalRepairTemporalLeftAuxiliary_mem
    · simpa only [outwardYZCanonicalRepairRealizedLeftAuxiliary,
          if_neg hspatial, if_neg htemporal] using
        (outwardYZCanonicalRepairLocalRealizedPair linked).left_mem

def outwardYZCanonicalRepairRealizedLeftAssignmentFrom :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, outwardYZCanonicalRepairRealizedLeftAuxiliary linked) ::
        outwardYZCanonicalRepairRealizedLeftAssignmentFrom rest

theorem outwardYZCanonicalRepairRealizedLeftAssignmentFrom_mem :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      outwardYZCanonicalRepairRealizedLeftAssignmentFrom linkedList ∈
        slabFusionWitnessAssignmentsOn 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        outwardYZCanonicalRepairRealizedLeftAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨outwardYZCanonicalRepairRealizedLeftAuxiliary linked,
        outwardYZCanonicalRepairRealizedLeftAuxiliary_mem linked, ?_⟩
      exact List.mem_map.mpr
        ⟨outwardYZCanonicalRepairRealizedLeftAssignmentFrom rest,
          outwardYZCanonicalRepairRealizedLeftAssignmentFrom_mem rest, rfl⟩

theorem outwardYZCanonicalRepairRealizedLeftAuxiliary_eq_spatial
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hspatial : linked.1 =
      outwardYZCanonicalRepairSwitchSpatialPivot) :
    outwardYZCanonicalRepairRealizedLeftAuxiliary linked =
      outwardYZCanonicalRepairSpatialLeftAuxiliary := by
  unfold outwardYZCanonicalRepairRealizedLeftAuxiliary
  rw [if_pos hspatial]

theorem outwardYZCanonicalRepairRealizedLeftAuxiliary_eq_temporal
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (htemporal : linked.1 =
      outwardYZCanonicalRepairSwitchTemporalPivot) :
    outwardYZCanonicalRepairRealizedLeftAuxiliary linked =
      outwardYZCanonicalRepairTemporalLeftAuxiliary := by
  have hne : linked.1 ≠
      outwardYZCanonicalRepairSwitchSpatialPivot := by
    intro hspatial
    have : outwardYZCanonicalRepairSwitchTemporalPivot =
        outwardYZCanonicalRepairSwitchSpatialPivot :=
      htemporal.symm.trans hspatial
    exact (show outwardYZCanonicalRepairSwitchTemporalPivot ≠
      outwardYZCanonicalRepairSwitchSpatialPivot by decide) this
  unfold outwardYZCanonicalRepairRealizedLeftAuxiliary
  rw [if_neg hne, if_pos htemporal]

#print axioms outwardYZCanonicalRepairSwitchRightPhysical_bounded
#print axioms outwardYZCanonicalRepairRealizedLeftAuxiliary_mem
#print axioms outwardYZCanonicalRepairRealizedLeftAssignmentFrom_mem
#print axioms outwardYZCanonicalRepairRealizedLeftAuxiliary_eq_spatial
#print axioms outwardYZCanonicalRepairRealizedLeftAuxiliary_eq_temporal

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetRealization
