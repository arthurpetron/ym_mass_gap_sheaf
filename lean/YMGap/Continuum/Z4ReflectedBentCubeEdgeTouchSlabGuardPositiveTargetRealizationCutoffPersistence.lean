/-
# Accepted realization of the positive guarded target at every cutoff

The ambient-cutoff positive row already supplies one selected recoupling
target at every slab link.  Realize each selected target as a pair of accepted
SU(2) auxiliary labellings at the same ambient cutoff, assemble those local
witnesses by structural recursion, and package the result as an accepted
two-replica state.

This is exact finite-cutoff realization.  It proves no cutoff-uniform lower
bound on the positive product and no graph-disconnection statement.

Constructive contract: canonical target realization and finite-list recursion
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence

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
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence

/-! ## 1. Literal ambient-cutoff realization at each link -/

theorem reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFaceLabellingBounded D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) := by
  simpa only [hextent] using
    (reflectedBentGuardGraftLeftPhysical_bounded_of_one_le
      D hcutoff hextent state)

theorem reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFaceLabellingBounded D.cutoff 5
      (reflectedBentGuardGraftRightPhysical D hextent state) := by
  simpa only [hextent] using
    (reflectedBentGuardGraftRightPhysical_bounded D hextent state)

def reflectedBentGuardGraftLocalRealizedPairAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairTargetProductionWitnessPair
    (reflectedBentGuardGraftLocalData D hextent state linked)
    (reflectedBentGuardGraftLocalAnchorAtCutoff
      D hcutoff hextent state linked)
    (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
      D hextent state)
    (reflectedBentGuardGraftLocalTargetAtCutoff
      D hcutoff hextent state linked)

def reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  (reflectedBentGuardGraftLocalRealizedPairAtCutoff
    D hcutoff hextent state linked).leftAuxiliary

def reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  (reflectedBentGuardGraftLocalRealizedPairAtCutoff
    D hcutoff hextent state linked).rightAuxiliary

theorem reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state linked ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1 :=
  (reflectedBentGuardGraftLocalRealizedPairAtCutoff
    D hcutoff hextent state linked).left_mem

theorem reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
        D hcutoff hextent state linked ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1 :=
  (reflectedBentGuardGraftLocalRealizedPairAtCutoff
    D hcutoff hextent state linked).right_mem

/-! ## 2. Structural assembly of complete ambient assignments -/

def reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state linked) ::
        reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
          D hcutoff hextent state rest

def reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
        D hcutoff hextent state linked) ::
        reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
          D hcutoff hextent state rest

theorem reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
          D hcutoff hextent state linkedList ∈
        slabFusionWitnessAssignmentsOn D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state linked,
        reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
            D hcutoff hextent state rest,
          reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff_mem
            D hcutoff hextent state rest, rfl⟩

theorem reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
          D hcutoff hextent state linkedList ∈
        slabFusionWitnessAssignmentsOn D.cutoff 5
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
          D hcutoff hextent state linked,
        reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
            D hcutoff hextent state rest,
          reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff_mem
            D hcutoff hextent state rest, rfl⟩

/-! ## 3. The accepted ambient-cutoff target state -/

def reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFusionWitnessAssignment :=
  reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach

def reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFusionWitnessAssignment :=
  reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach

theorem reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
        D hcutoff hextent state ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftLeftPhysical D hextent state) := by
  have hmem :=
    reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff_mem
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  unfold reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
    slabFineFusionWitnesses
  simpa only [hextent] using hmem

theorem reflectedBentGuardGraftRealizedRightAssignmentAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
        D hcutoff hextent state ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftRightPhysical D hextent state) := by
  have hmem :=
    reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff_mem
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  unfold reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
    slabFineFusionWitnesses
  simpa only [hextent] using hmem

theorem reflectedBentGuardGraftRealizedLeftSourceAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftLeftPhysical D hextent state,
      reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
        D hcutoff hextent state) ∈ slabExpandedFineSources D := by
  unfold slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨reflectedBentGuardGraftLeftPhysical D hextent state,
    reflectedBentGuardGraftLeftPhysical_mem_of_one_le
      D hcutoff hextent state, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
      D hcutoff hextent state,
    reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff_mem
      D hcutoff hextent state, rfl⟩

theorem reflectedBentGuardGraftRealizedRightSourceAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftRightPhysical D hextent state,
      reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
        D hcutoff hextent state) ∈ slabExpandedFineSources D := by
  unfold slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨reflectedBentGuardGraftRightPhysical D hextent state,
    reflectedBentGuardGraftRightPhysical_mem D hextent state, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
      D hcutoff hextent state,
    reflectedBentGuardGraftRealizedRightAssignmentAtCutoff_mem
      D hcutoff hextent state, rfl⟩

def reflectedBentGuardGraftPositiveTargetAcceptedStateAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabAcceptedTwoReplicaState D :=
  (⟨(reflectedBentGuardGraftLeftPhysical D hextent state,
      reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
        D hcutoff hextent state),
    reflectedBentGuardGraftRealizedLeftSourceAtCutoff_mem
      D hcutoff hextent state⟩,
   ⟨(reflectedBentGuardGraftRightPhysical D hextent state,
      reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
        D hcutoff hextent state),
    reflectedBentGuardGraftRealizedRightSourceAtCutoff_mem
      D hcutoff hextent state⟩)

#print axioms reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
#print axioms reflectedBentGuardGraftLocalRealizedPairAtCutoff
#print axioms reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
#print axioms reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
#print axioms reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff_mem
#print axioms reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff_mem
#print axioms reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff_mem
#print axioms reflectedBentGuardGraftRealizedRightAssignmentAtCutoff_mem
#print axioms reflectedBentGuardGraftPositiveTargetAcceptedStateAtCutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
