/-
# The guarded positive target as an observable choice at every cutoff

Attach the selected ambient-cutoff target column to the literal guarded-graft
observable source.  The target selector and canonical realizer are unchanged;
only their source and membership witnesses now live at `D.cutoff` under the
explicit hypothesis `1 ≤ D.cutoff`.

This is a qualitative all-cutoff choice.  It supplies no cutoff-uniform lower
bound on the chosen column.

Constructive contract: dependent target transport and structural list
recursion only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoiceCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

/-! ## 1. The ambient-cutoff target in the observable carrier -/

def reflectedBentGuardGraftTargetMembershipPackageFromAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    TargetMembershipPackage
      (ReflectedBentGuardGraftLinkedPackagesFrom
        D hextent state linkedList) :=
  { target := reflectedBentGuardGraftTargetAssignmentFromAtCutoff
      D hcutoff hextent state linkedList
    target_mem := reflectedBentGuardGraftTargetAssignmentFromAtCutoff_mem
      D hcutoff hextent state linkedList }

theorem reflectedBentGuardGraftTargetMembershipPackageFromAtCutoff_target
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (reflectedBentGuardGraftTargetMembershipPackageFromAtCutoff
      D hcutoff hextent state linkedList).target =
        reflectedBentGuardGraftTargetAssignmentFromAtCutoff
          D hcutoff hextent state linkedList := rfl

theorem reflectedBentGuardGraftObservableRecouplingPackagesAtCutoff_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabPhysicalPairRecouplingPackages D.extent
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.1.1.1
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.2.1.1 =
      ReflectedBentGuardGraftLinkedPackagesFrom D hextent state
        (boundaryCompleteSlabLinks 5).attach := by
  rw [hextent,
    reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftPhysical,
    reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightPhysical]
  unfold slabPhysicalPairRecouplingPackages
    ReflectedBentGuardGraftLinkedPackagesFrom
  rfl

opaque reflectedBentGuardGraftObservableTargetPackageAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    TransportedTargetPackage
      (slabPhysicalPairRecouplingPackages D.extent
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.1.1.1
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.2.1.1)
      (ReflectedBentGuardGraftLinkedPackagesFrom D hextent state
        (boundaryCompleteSlabLinks 5).attach)
      (reflectedBentGuardGraftObservableRecouplingPackagesAtCutoff_eq
        D hcutoff hextent state) :=
  transportedTargetPackage
    (reflectedBentGuardGraftObservableRecouplingPackagesAtCutoff_eq
      D hcutoff hextent state)
    (reflectedBentGuardGraftTargetMembershipPackageFromAtCutoff
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach)

/-! ## 2. Structural equality with the ambient classified realization -/

theorem reflectedBentGuardGraftRealizedAssignmentsFromAtCutoff_eq_canonical
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
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
        linkedList
        (reflectedBentGuardGraftTargetAssignmentFromAtCutoff
          D hcutoff hextent state linkedList)
      reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
          D hcutoff hextent state linkedList = canonical.leftAssignment ∧
        reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
          D hcutoff hextent state linkedList = canonical.rightAssignment
  | [] => ⟨rfl, rfl⟩
  | linked :: rest => by
      have htail :=
        reflectedBentGuardGraftRealizedAssignmentsFromAtCutoff_eq_canonical
          D hcutoff hextent state rest
      change
        (linked.1,
            (reflectedBentGuardGraftLocalRealizedPairAtCutoff
              D hcutoff hextent state linked).leftAuxiliary) ::
              reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
                D hcutoff hextent state rest =
          (linked.1,
            (reflectedBentGuardGraftLocalRealizedPairAtCutoff
              D hcutoff hextent state linked).leftAuxiliary) ::
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
                rest
                (reflectedBentGuardGraftTargetAssignmentFromAtCutoff
                  D hcutoff hextent state rest)).leftAssignment ∧
        (linked.1,
            (reflectedBentGuardGraftLocalRealizedPairAtCutoff
              D hcutoff hextent state linked).rightAuxiliary) ::
              reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
                D hcutoff hextent state rest =
          (linked.1,
            (reflectedBentGuardGraftLocalRealizedPairAtCutoff
              D hcutoff hextent state linked).rightAuxiliary) ::
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
                rest
                (reflectedBentGuardGraftTargetAssignmentFromAtCutoff
                  D hcutoff hextent state rest)).rightAssignment
      constructor
      · rw [htail.1]
      · rw [htail.2]

/-! ## 3. The literal all-cutoff observable choice -/

abbrev reflectedBentGuardGraftObservableChoiceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  (reflectedBentGuardGraftObservableTargetPackageAtCutoff
    D hcutoff hextent state).target

theorem reflectedBentGuardGraftObservableChoiceAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftObservableChoiceAtCutoff
        D hcutoff hextent state ∈
      slabObservablePairedStrandRecouplingChoices D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state) :=
  (reflectedBentGuardGraftObservableTargetPackageAtCutoff
    D hcutoff hextent state).target_mem

/-! ## 4. The same column over the literal, unsealed source -/

theorem reflectedBentGuardGraftRawObservableRecouplingPackagesAtCutoff_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabPhysicalPairRecouplingPackages D.extent
        (reflectedBentGuardGraftRawObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.1.1.1
        (reflectedBentGuardGraftRawObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.2.1.1 =
      ReflectedBentGuardGraftLinkedPackagesFrom D hextent state
        (boundaryCompleteSlabLinks 5).attach := by
  rw [hextent]
  unfold reflectedBentGuardGraftRawObservableRecouplingSourceAtCutoff
    reflectedBentGuardGraftObservableSourcePairAtCutoff
  rw [reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical,
    reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical]
  rfl

@[irreducible] def reflectedBentGuardGraftRawObservableChoiceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePairedStrandRecouplingChoice D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftRawObservableRecouplingSourceAtCutoff
        D hcutoff hextent state) :=
  (transportedTargetPackage
    (reflectedBentGuardGraftRawObservableRecouplingPackagesAtCutoff_eq
      D hcutoff hextent state)
    (reflectedBentGuardGraftTargetMembershipPackageFromAtCutoff
      D hcutoff hextent state
      (boundaryCompleteSlabLinks 5).attach)).target

#print axioms reflectedBentGuardGraftObservableRecouplingPackagesAtCutoff_eq
#print axioms reflectedBentGuardGraftObservableTargetPackageAtCutoff
#print axioms reflectedBentGuardGraftRealizedAssignmentsFromAtCutoff_eq_canonical
#print axioms reflectedBentGuardGraftObservableChoiceAtCutoff_mem
#print axioms reflectedBentGuardGraftRawObservableRecouplingPackagesAtCutoff_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoiceCutoffPersistence
