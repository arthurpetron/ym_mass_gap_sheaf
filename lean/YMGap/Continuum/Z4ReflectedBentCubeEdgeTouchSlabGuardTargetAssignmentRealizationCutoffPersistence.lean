/-
# Realizing every guarded recoupling target assignment at every cutoff

The positive-target modules realized one distinguished recoupling column.
The pivot-cylinder argument instead retains an entire dependent family of
columns.  This module supplies the missing compiler uniformly: every local
target is reconstructed as two literal accepted SU(2) auxiliaries, and every
dependent target assignment is assembled into accepted left and right slab
assignments by structural recursion.

No positivity or cylinder property is needed here.  Those are orthogonal
facts about which target assignments are later selected.

Constructive contract: canonical target realization and finite-list recursion
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence

/-! ## 1. Every local column has accepted auxiliaries -/

def reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      linked).Target) :=
  slabPhysicalPairTargetProductionWitnessPair
    (reflectedBentGuardGraftLocalData D hextent state linked)
    (reflectedBentGuardGraftLocalAnchorAtCutoff
      D hcutoff hextent state linked)
    (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
      D hextent state)
    target

def reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      linked).Target) : SlabLabelling :=
  (reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
    D hcutoff hextent state linked target).leftAuxiliary

def reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      linked).Target) : SlabLabelling :=
  (reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
    D hcutoff hextent state linked target).rightAuxiliary

theorem reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      linked).Target) :
    reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
        D hcutoff hextent state linked target ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1 :=
  (reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
    D hcutoff hextent state linked target).left_mem

theorem reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      linked).Target) :
    reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
        D hcutoff hextent state linked target ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1 :=
  (reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
    D hcutoff hextent state linked target).right_mem

/-! ## 2. Every dependent target assignment has accepted slab assignments -/

def reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) →
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked) →
    SlabFusionWitnessAssignment
  | [], _ => []
  | linked :: rest, target =>
      (linked.1,
        reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
          D hcutoff hextent state linked target.1) ::
        reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
          D hcutoff hextent state rest target.2

def reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) →
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked) →
    SlabFusionWitnessAssignment
  | [], _ => []
  | linked :: rest, target =>
      (linked.1,
        reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
          D hcutoff hextent state linked target.1) ::
        reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
          D hcutoff hextent state rest target.2

theorem reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5})
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)),
      reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
          D hcutoff hextent state linkedList target ∈
        slabFusionWitnessAssignmentsOn D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [], _ => List.mem_cons_self
  | linked :: rest, target => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
          D hcutoff hextent state linked target.1,
        reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff_mem
          D hcutoff hextent state linked target.1, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
            D hcutoff hextent state rest target.2,
          reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_mem
            D hcutoff hextent state rest target.2, rfl⟩

theorem reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5})
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)),
      reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
          D hcutoff hextent state linkedList target ∈
        slabFusionWitnessAssignmentsOn D.cutoff 5
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [], _ => List.mem_cons_self
  | linked :: rest, target => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
          D hcutoff hextent state linked target.1,
        reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff_mem
          D hcutoff hextent state linked target.1, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
            D hcutoff hextent state rest target.2,
          reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff_mem
            D hcutoff hextent state rest target.2, rfl⟩

/-! ## 3. Exact agreement with the canonical whole-slab realizer -/

/-- The structurally assembled guarded realization is exactly the canonical
physical-pair realization for every target column, not only for the
distinguished positive target. -/
theorem reflectedBentGuardGraftRealizedAssignmentsFromTargetAtCutoff_eq_canonical
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5})
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)),
      let canonical := slabPhysicalPairCanonicalTargetAssignmentsFrom
        D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        (reflectedBentGuardGraftLeftAssignment D hextent state)
        (reflectedBentGuardGraftRightAssignment D hextent state)
        (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
          D hcutoff hextent state)
        (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
          D hcutoff hextent state)
        (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
          D hcutoff hextent state)
        (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
          D hextent state)
        linkedList target
      reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
          D hcutoff hextent state linkedList target =
          canonical.leftAssignment ∧
        reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
          D hcutoff hextent state linkedList target =
          canonical.rightAssignment
  | [], _ => ⟨rfl, rfl⟩
  | linked :: rest, target => by
      have htail :=
        reflectedBentGuardGraftRealizedAssignmentsFromTargetAtCutoff_eq_canonical
          D hcutoff hextent state rest target.2
      change
        (linked.1,
            (reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
              D hcutoff hextent state linked target.1).leftAuxiliary) ::
              reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
                D hcutoff hextent state rest target.2 =
          (linked.1,
            (reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
              D hcutoff hextent state linked target.1).leftAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom D.cutoff 5
                (reflectedBentGuardGraftLeftPhysical D hextent state)
                (reflectedBentGuardGraftRightPhysical D hextent state)
                (reflectedBentGuardGraftLeftAssignment D hextent state)
                (reflectedBentGuardGraftRightAssignment D hextent state)
                (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                  D hcutoff hextent state)
                (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                  D hcutoff hextent state)
                (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
                  D hcutoff hextent state)
                (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
                  D hextent state)
                rest target.2).leftAssignment ∧
        (linked.1,
            (reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
              D hcutoff hextent state linked target.1).rightAuxiliary) ::
              reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
                D hcutoff hextent state rest target.2 =
          (linked.1,
            (reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
              D hcutoff hextent state linked target.1).rightAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom D.cutoff 5
                (reflectedBentGuardGraftLeftPhysical D hextent state)
                (reflectedBentGuardGraftRightPhysical D hextent state)
                (reflectedBentGuardGraftLeftAssignment D hextent state)
                (reflectedBentGuardGraftRightAssignment D hextent state)
                (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                  D hcutoff hextent state)
                (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                  D hcutoff hextent state)
                (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
                  D hcutoff hextent state)
                (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
                  D hextent state)
                rest target.2).rightAssignment
      constructor
      · rw [htail.1]
      · rw [htail.2]

#print axioms reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
#print axioms reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff_mem
#print axioms reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff_mem
#print axioms reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_mem
#print axioms reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff_mem
#print axioms reflectedBentGuardGraftRealizedAssignmentsFromTargetAtCutoff_eq_canonical

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence
