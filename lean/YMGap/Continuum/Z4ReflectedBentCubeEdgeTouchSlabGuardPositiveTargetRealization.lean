/-
# Accepted realization of the positive guarded-graft target

Realize the selected positive recoupling column link by link.  Each local
target produces a literal accepted pair of SU(2) auxiliaries over the fixed
grafted physical fields.  Structural recursion assembles those pairs into
complete left and right assignments and hence an accepted two-replica target
state.

This module closes realization only.  Identifying the exceptional pivot with
the component-preserving reflected carrier and classifying every resulting
strand edge remain downstream geometric contractions.

Constructive contract: canonical equal-rank target realization and finite
list recursion only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget

/-! ## 1. Literal realization of each selected local column -/

theorem reflectedBentGuardGraftLeftPhysical_bounded_five
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFaceLabellingBounded 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) := by
  simpa only [hcutoff, hextent] using
    (reflectedBentGuardGraftLeftPhysical_bounded
      D hcutoff hextent state)

theorem reflectedBentGuardGraftRightPhysical_bounded_five
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFaceLabellingBounded 1 5
      (reflectedBentGuardGraftRightPhysical D hextent state) := by
  simpa only [hcutoff, hextent] using
    (reflectedBentGuardGraftRightPhysical_bounded D hextent state)

def reflectedBentGuardGraftLocalRealizedPair
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairTargetProductionWitnessPair
    (reflectedBentGuardGraftLocalData D hextent state linked)
    (reflectedBentGuardGraftLocalAnchor D hcutoff hextent state linked)
    (reflectedBentGuardGraftLeftPhysical_bounded_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftLocalTarget
      D hcutoff hextent state linked)

def reflectedBentGuardGraftRealizedLeftAuxiliary
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  (reflectedBentGuardGraftLocalRealizedPair
    D hcutoff hextent state linked).leftAuxiliary

def reflectedBentGuardGraftRealizedRightAuxiliary
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  (reflectedBentGuardGraftLocalRealizedPair
    D hcutoff hextent state linked).rightAuxiliary

theorem reflectedBentGuardGraftRealizedLeftAuxiliary_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentGuardGraftRealizedLeftAuxiliary
        D hcutoff hextent state linked ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1 :=
  (reflectedBentGuardGraftLocalRealizedPair
    D hcutoff hextent state linked).left_mem

theorem reflectedBentGuardGraftRealizedRightAuxiliary_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentGuardGraftRealizedRightAuxiliary
        D hcutoff hextent state linked ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1 :=
  (reflectedBentGuardGraftLocalRealizedPair
    D hcutoff hextent state linked).right_mem

/-! ## 2. Structural realization of both global assignments -/

def reflectedBentGuardGraftRealizedLeftAssignmentFrom
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, reflectedBentGuardGraftRealizedLeftAuxiliary
        D hcutoff hextent state linked) ::
        reflectedBentGuardGraftRealizedLeftAssignmentFrom
          D hcutoff hextent state rest

def reflectedBentGuardGraftRealizedRightAssignmentFrom
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, reflectedBentGuardGraftRealizedRightAuxiliary
        D hcutoff hextent state linked) ::
        reflectedBentGuardGraftRealizedRightAssignmentFrom
          D hcutoff hextent state rest

theorem reflectedBentGuardGraftRealizedLeftAssignmentFrom_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftRealizedLeftAssignmentFrom
          D hcutoff hextent state linkedList ∈
        slabFusionWitnessAssignmentsOn 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftRealizedLeftAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftRealizedLeftAuxiliary
          D hcutoff hextent state linked,
        reflectedBentGuardGraftRealizedLeftAuxiliary_mem
          D hcutoff hextent state linked, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftRealizedLeftAssignmentFrom
            D hcutoff hextent state rest,
          reflectedBentGuardGraftRealizedLeftAssignmentFrom_mem
            D hcutoff hextent state rest, rfl⟩

theorem reflectedBentGuardGraftRealizedRightAssignmentFrom_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftRealizedRightAssignmentFrom
          D hcutoff hextent state linkedList ∈
        slabFusionWitnessAssignmentsOn 1 5
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftRealizedRightAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftRealizedRightAuxiliary
          D hcutoff hextent state linked,
        reflectedBentGuardGraftRealizedRightAuxiliary_mem
          D hcutoff hextent state linked, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftRealizedRightAssignmentFrom
            D hcutoff hextent state rest,
          reflectedBentGuardGraftRealizedRightAssignmentFrom_mem
            D hcutoff hextent state rest, rfl⟩

/-! ## 3. The complete accepted target state -/

def reflectedBentGuardGraftRealizedLeftAssignment
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFusionWitnessAssignment :=
  reflectedBentGuardGraftRealizedLeftAssignmentFrom
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach

def reflectedBentGuardGraftRealizedRightAssignment
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFusionWitnessAssignment :=
  reflectedBentGuardGraftRealizedRightAssignmentFrom
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach

theorem reflectedBentGuardGraftRealizedLeftAssignment_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedLeftAssignment
        D hcutoff hextent state ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftLeftPhysical D hextent state) := by
  have hmem := reflectedBentGuardGraftRealizedLeftAssignmentFrom_mem
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  unfold reflectedBentGuardGraftRealizedLeftAssignment
    slabFineFusionWitnesses
  simpa only [hcutoff, hextent] using hmem

theorem reflectedBentGuardGraftRealizedRightAssignment_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedRightAssignment
        D hcutoff hextent state ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftRightPhysical D hextent state) := by
  have hmem := reflectedBentGuardGraftRealizedRightAssignmentFrom_mem
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  unfold reflectedBentGuardGraftRealizedRightAssignment
    slabFineFusionWitnesses
  simpa only [hcutoff, hextent] using hmem

theorem reflectedBentGuardGraftRealizedLeftSource_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftLeftPhysical D hextent state,
      reflectedBentGuardGraftRealizedLeftAssignment
        D hcutoff hextent state) ∈ slabExpandedFineSources D := by
  unfold slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨reflectedBentGuardGraftLeftPhysical D hextent state,
    reflectedBentGuardGraftLeftPhysical_mem
      D hcutoff hextent state, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨reflectedBentGuardGraftRealizedLeftAssignment
      D hcutoff hextent state,
    reflectedBentGuardGraftRealizedLeftAssignment_mem
      D hcutoff hextent state, rfl⟩

theorem reflectedBentGuardGraftRealizedRightSource_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftRightPhysical D hextent state,
      reflectedBentGuardGraftRealizedRightAssignment
        D hcutoff hextent state) ∈ slabExpandedFineSources D := by
  unfold slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨reflectedBentGuardGraftRightPhysical D hextent state,
    reflectedBentGuardGraftRightPhysical_mem D hextent state, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨reflectedBentGuardGraftRealizedRightAssignment
      D hcutoff hextent state,
    reflectedBentGuardGraftRealizedRightAssignment_mem
      D hcutoff hextent state, rfl⟩

def reflectedBentGuardGraftPositiveTargetAcceptedState
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabAcceptedTwoReplicaState D :=
  (⟨(reflectedBentGuardGraftLeftPhysical D hextent state,
      reflectedBentGuardGraftRealizedLeftAssignment
        D hcutoff hextent state),
    reflectedBentGuardGraftRealizedLeftSource_mem
      D hcutoff hextent state⟩,
   ⟨(reflectedBentGuardGraftRightPhysical D hextent state,
      reflectedBentGuardGraftRealizedRightAssignment
        D hcutoff hextent state),
    reflectedBentGuardGraftRealizedRightSource_mem
      D hcutoff hextent state⟩)

#print axioms reflectedBentGuardGraftLeftPhysical_bounded_five
#print axioms reflectedBentGuardGraftLocalRealizedPair
#print axioms reflectedBentGuardGraftRealizedLeftAuxiliary_mem
#print axioms reflectedBentGuardGraftRealizedRightAuxiliary_mem
#print axioms reflectedBentGuardGraftRealizedLeftAssignmentFrom_mem
#print axioms reflectedBentGuardGraftRealizedRightAssignmentFrom_mem
#print axioms reflectedBentGuardGraftRealizedLeftAssignment_mem
#print axioms reflectedBentGuardGraftRealizedRightAssignment_mem
#print axioms reflectedBentGuardGraftPositiveTargetAcceptedState

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization
