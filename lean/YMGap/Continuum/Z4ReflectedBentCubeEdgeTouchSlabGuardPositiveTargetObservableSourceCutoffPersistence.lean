/-
# The guarded graft as an observable source at every cutoff

Package the ambient-cutoff accepted graft into the literal observable
`11 x 00` source cell.  The marked-face values are cutoff independent; only
the accepted physical and auxiliary membership certificates require the new
cutoff-persistence theorems.

Constructive contract: exact marked-face evaluation and finite carrier
membership only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnectionCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource

/-! ## 1. Literal ambient-cutoff `11 x 00` entries -/

def reflectedBentGuardGraftLeftPositiveEntryAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePositiveSourceEntry D reflectedBentRootFaceId :=
  slabObservablePositiveSourceEntryOfCarrier
    D reflectedBentRootFaceId
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftLeftPhysical_mem_of_one_le
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftAssignment D hextent state)
    (reflectedBentGuardGraftLeftAssignment_mem_of_one_le
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftPhysical_root_pos D hextent state)

def reflectedBentGuardGraftRightExpandedEntryAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabExpandedFineSourceEntry D :=
  slabExpandedFineSourceEntryOfCarrier
    D (reflectedBentGuardGraftRightPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical_mem D hextent state)
    (reflectedBentGuardGraftRightAssignment D hextent state)
    (reflectedBentGuardGraftRightAssignment_mem_of_one_le
      D hcutoff hextent state)

@[simp] theorem reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftLeftPositiveEntryAtCutoff
      D hcutoff hextent state).1.1 =
        reflectedBentGuardGraftLeftPhysical D hextent state := by
  unfold reflectedBentGuardGraftLeftPositiveEntryAtCutoff
  apply slabObservablePositiveSourceEntryOfCarrier_physical

@[simp] theorem reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftRightExpandedEntryAtCutoff
      D hcutoff hextent state).1.1 =
        reflectedBentGuardGraftRightPhysical D hextent state := by
  unfold reflectedBentGuardGraftRightExpandedEntryAtCutoff
  apply slabExpandedFineSourceEntryOfCarrier_physical

@[simp] theorem reflectedBentGuardGraftLeftPositiveEntryAtCutoff_assignment
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftLeftPositiveEntryAtCutoff
      D hcutoff hextent state).1.2 =
        reflectedBentGuardGraftLeftAssignment D hextent state := by
  unfold reflectedBentGuardGraftLeftPositiveEntryAtCutoff
  apply slabObservablePositiveSourceEntryOfCarrier_assignment

@[simp] theorem reflectedBentGuardGraftRightExpandedEntryAtCutoff_assignment
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftRightExpandedEntryAtCutoff
      D hcutoff hextent state).1.2 =
        reflectedBentGuardGraftRightAssignment D hextent state := by
  unfold reflectedBentGuardGraftRightExpandedEntryAtCutoff
  apply slabExpandedFineSourceEntryOfCarrier_assignment

theorem reflectedBentGuardGraftLeftPositiveEntryAtCutoff_mem_rootTarget
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLeftPositiveEntryAtCutoff
        D hcutoff hextent state ∈
      slabObservableRootTargetEntries D
        reflectedBentRootFaceId reflectedBentTargetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ _, ?_⟩
  unfold SlabObservablePositiveSourceEntry.facePositiveB
  rw [reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical]
  exact decide_eq_true
    (reflectedBentGuardGraftLeftPhysical_target_pos D hextent state)

theorem reflectedBentGuardGraftRightExpandedEntryAtCutoff_mem_complements
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRightExpandedEntryAtCutoff
        D hcutoff hextent state ∈
      slabObservableRootComplementTargetComplementEntries D
        reflectedBentRootFaceId reflectedBentTargetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ _, ?_⟩
  unfold SlabExpandedFineSourceEntry.facePositiveB
  rw [reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical,
    reflectedBentGuardGraftRightPhysical_root_zero,
    reflectedBentGuardGraftRightPhysical_target_zero]
  rfl

/-! ## 2. The literal ambient observable source -/

def reflectedBentGuardGraftObservableSourcePairAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservableTwoReplicaPair D reflectedBentRootFaceId :=
  (reflectedBentGuardGraftLeftPositiveEntryAtCutoff
      D hcutoff hextent state,
    reflectedBentGuardGraftRightExpandedEntryAtCutoff
      D hcutoff hextent state)

theorem reflectedBentGuardGraftObservableSourcePairAtCutoff_mem_fourCell
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftObservableSourcePairAtCutoff
        D hcutoff hextent state ∈
      slabObservableFourCellSourcePairs D
        reflectedBentRootFaceId reflectedBentTargetFaceId := by
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨
    reflectedBentGuardGraftLeftPositiveEntryAtCutoff_mem_rootTarget
      D hcutoff hextent state,
    reflectedBentGuardGraftRightExpandedEntryAtCutoff_mem_complements
      D hcutoff hextent state⟩

def reflectedBentGuardGraftRawObservableRecouplingSourceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePairedStrandRecouplingSource D
      reflectedBentRootFaceId reflectedBentTargetFaceId :=
  ⟨reflectedBentGuardGraftObservableSourcePairAtCutoff
      D hcutoff hextent state,
    reflectedBentGuardGraftObservableSourcePairAtCutoff_mem_fourCell
      D hcutoff hextent state⟩

structure ReflectedBentGuardGraftObservableSourcePackageAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Type where
  source : SlabObservablePairedStrandRecouplingSource D
    reflectedBentRootFaceId reflectedBentTargetFaceId
  sourcePair_eq : source.1 =
    reflectedBentGuardGraftObservableSourcePairAtCutoff
      D hcutoff hextent state
  leftPhysical : source.1.1.1.1 =
    reflectedBentGuardGraftLeftPhysical D hextent state
  rightPhysical : source.1.2.1.1 =
    reflectedBentGuardGraftRightPhysical D hextent state
  leftAssignment : source.1.1.1.2 =
    reflectedBentGuardGraftLeftAssignment D hextent state
  rightAssignment : source.1.2.1.2 =
    reflectedBentGuardGraftRightAssignment D hextent state

opaque reflectedBentGuardGraftObservableSourcePackageAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ReflectedBentGuardGraftObservableSourcePackageAtCutoff
      D hcutoff hextent state := by
  refine
    { source := reflectedBentGuardGraftRawObservableRecouplingSourceAtCutoff
        D hcutoff hextent state
      sourcePair_eq := rfl
      leftPhysical := ?_
      rightPhysical := ?_
      leftAssignment := ?_
      rightAssignment := ?_ }
  · exact reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical
      D hcutoff hextent state
  · exact reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical
      D hcutoff hextent state
  · exact reflectedBentGuardGraftLeftPositiveEntryAtCutoff_assignment
      D hcutoff hextent state
  · exact reflectedBentGuardGraftRightExpandedEntryAtCutoff_assignment
      D hcutoff hextent state

abbrev reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  (reflectedBentGuardGraftObservableSourcePackageAtCutoff
    D hcutoff hextent state).source

@[simp] theorem reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftPhysical
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
      D hcutoff hextent state).1.1.1.1 =
        reflectedBentGuardGraftLeftPhysical D hextent state :=
  (reflectedBentGuardGraftObservableSourcePackageAtCutoff
    D hcutoff hextent state).leftPhysical

@[simp] theorem reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightPhysical
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
      D hcutoff hextent state).1.2.1.1 =
        reflectedBentGuardGraftRightPhysical D hextent state :=
  (reflectedBentGuardGraftObservableSourcePackageAtCutoff
    D hcutoff hextent state).rightPhysical

@[simp] theorem reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftAssignment
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
      D hcutoff hextent state).1.1.1.2 =
        reflectedBentGuardGraftLeftAssignment D hextent state :=
  (reflectedBentGuardGraftObservableSourcePackageAtCutoff
    D hcutoff hextent state).leftAssignment

@[simp] theorem reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightAssignment
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
      D hcutoff hextent state).1.2.1.2 =
        reflectedBentGuardGraftRightAssignment D hextent state :=
  (reflectedBentGuardGraftObservableSourcePackageAtCutoff
    D hcutoff hextent state).rightAssignment

#print axioms reflectedBentGuardGraftLeftPositiveEntryAtCutoff_mem_rootTarget
#print axioms reflectedBentGuardGraftRightExpandedEntryAtCutoff_mem_complements
#print axioms reflectedBentGuardGraftObservableSourcePairAtCutoff_mem_fourCell
#print axioms reflectedBentGuardGraftObservableSourcePackageAtCutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
