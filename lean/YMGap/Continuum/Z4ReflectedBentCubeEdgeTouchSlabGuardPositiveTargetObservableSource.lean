/-
# The guarded graft as an observable recoupling source

The inserted reflected channel makes the left graft positive at both marked
faces.  The cleared guard makes the retained right graft zero at both marked
faces.  Package the accepted graft assignments as a literal member of the
observable `11 x 00` source cell, uniformly over the input accepted state.

Constructive contract: exact marked-face evaluation and finite carrier
membership only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource

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
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

/-! ## 1. Exact marked-face values -/

theorem reflectedBentGuardGraftLeftPhysical_root_pos
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    0 < reflectedBentGuardGraftLeftPhysical D hextent state
      reflectedBentRootFaceId := by
  have hpattern : 0 < reflectedBentSwitchLeftPhysical
      reflectedBentRootFaceId :=
    (mem_reflectedBentPatternFaceIds_iff
      reflectedBentRootFaceId_physical).mp
      reflectedBentRootFaceId_mem_pattern
  unfold reflectedBentGuardGraftLeftPhysical
  rw [if_pos hpattern]
  exact hpattern

theorem reflectedBentGuardGraftLeftPhysical_target_pos
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    0 < reflectedBentGuardGraftLeftPhysical D hextent state
      reflectedBentTargetFaceId := by
  have hpattern : 0 < reflectedBentSwitchLeftPhysical
      reflectedBentTargetFaceId :=
    (mem_reflectedBentPatternFaceIds_iff
      reflectedBentTargetFaceId_physical).mp
      reflectedBentTargetFaceId_mem_pattern
  unfold reflectedBentGuardGraftLeftPhysical
  rw [if_pos hpattern]
  exact hpattern

theorem reflectedBentGuardGraftRightPhysical_root_zero
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRightPhysical D hextent state
      reflectedBentRootFaceId = 0 := by
  rw [reflectedBentGuardGraftRightPhysical_eq_pattern_on_guard
    D hextent state reflectedBentRootFaceId
    (reflectedBentPatternFace_mem_guard
      reflectedBentRootFaceId_mem_pattern)]
  exact reflectedBentSwitchRightPhysical_eq_zero reflectedBentRootFaceId

theorem reflectedBentGuardGraftRightPhysical_target_zero
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRightPhysical D hextent state
      reflectedBentTargetFaceId = 0 := by
  rw [reflectedBentGuardGraftRightPhysical_eq_pattern_on_guard
    D hextent state reflectedBentTargetFaceId
    (reflectedBentPatternFace_mem_guard
      reflectedBentTargetFaceId_mem_pattern)]
  exact reflectedBentSwitchRightPhysical_eq_zero reflectedBentTargetFaceId

/-! ## 2. Literal `11 x 00` entries -/

def reflectedBentGuardGraftLeftPositiveEntry
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePositiveSourceEntry D reflectedBentRootFaceId :=
  slabObservablePositiveSourceEntryOfCarrier
    D reflectedBentRootFaceId
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftLeftPhysical_mem D hcutoff hextent state)
    (reflectedBentGuardGraftLeftAssignment D hextent state)
    (reflectedBentGuardGraftLeftAssignment_mem D hcutoff hextent state)
    (reflectedBentGuardGraftLeftPhysical_root_pos D hextent state)

def reflectedBentGuardGraftRightExpandedEntry
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabExpandedFineSourceEntry D :=
  slabExpandedFineSourceEntryOfCarrier
    D (reflectedBentGuardGraftRightPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical_mem D hextent state)
    (reflectedBentGuardGraftRightAssignment D hextent state)
    (reflectedBentGuardGraftRightAssignment_mem D hcutoff hextent state)

@[simp] theorem reflectedBentGuardGraftLeftPositiveEntry_physical
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftLeftPositiveEntry
      D hcutoff hextent state).1.1 =
        reflectedBentGuardGraftLeftPhysical D hextent state := by
  unfold reflectedBentGuardGraftLeftPositiveEntry
  apply slabObservablePositiveSourceEntryOfCarrier_physical

@[simp] theorem reflectedBentGuardGraftRightExpandedEntry_physical
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftRightExpandedEntry
      D hcutoff hextent state).1.1 =
        reflectedBentGuardGraftRightPhysical D hextent state := by
  unfold reflectedBentGuardGraftRightExpandedEntry
  apply slabExpandedFineSourceEntryOfCarrier_physical

theorem reflectedBentGuardGraftLeftPositiveEntry_mem_rootTarget
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLeftPositiveEntry D hcutoff hextent state ∈
      slabObservableRootTargetEntries D
        reflectedBentRootFaceId reflectedBentTargetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ _, ?_⟩
  unfold SlabObservablePositiveSourceEntry.facePositiveB
  rw [reflectedBentGuardGraftLeftPositiveEntry_physical]
  exact decide_eq_true
    (reflectedBentGuardGraftLeftPhysical_target_pos D hextent state)

theorem reflectedBentGuardGraftRightExpandedEntry_mem_rootComplementTargetComplement
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRightExpandedEntry D hcutoff hextent state ∈
      slabObservableRootComplementTargetComplementEntries D
        reflectedBentRootFaceId reflectedBentTargetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ _, ?_⟩
  unfold SlabExpandedFineSourceEntry.facePositiveB
  rw [reflectedBentGuardGraftRightExpandedEntry_physical,
    reflectedBentGuardGraftRightPhysical_root_zero,
    reflectedBentGuardGraftRightPhysical_target_zero]
  rfl

/-! ## 3. The observable recoupling source -/

def reflectedBentGuardGraftObservableSourcePair
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservableTwoReplicaPair D reflectedBentRootFaceId :=
  (reflectedBentGuardGraftLeftPositiveEntry D hcutoff hextent state,
    reflectedBentGuardGraftRightExpandedEntry D hcutoff hextent state)

theorem reflectedBentGuardGraftObservableSourcePair_mem_fourCell
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftObservableSourcePair D hcutoff hextent state ∈
      slabObservableFourCellSourcePairs D
        reflectedBentRootFaceId reflectedBentTargetFaceId := by
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨
    reflectedBentGuardGraftLeftPositiveEntry_mem_rootTarget
      D hcutoff hextent state,
    reflectedBentGuardGraftRightExpandedEntry_mem_rootComplementTargetComplement
      D hcutoff hextent state⟩

def reflectedBentGuardGraftRawObservableRecouplingSource
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePairedStrandRecouplingSource D
      reflectedBentRootFaceId reflectedBentTargetFaceId :=
  ⟨reflectedBentGuardGraftObservableSourcePair D hcutoff hextent state,
    reflectedBentGuardGraftObservableSourcePair_mem_fourCell
      D hcutoff hextent state⟩

/-- Seal the filter-membership construction while retaining the exact
physical fields and accepted source assignments needed by the recoupling
anchor. -/
structure ReflectedBentGuardGraftObservableSourcePackage
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Type where
  source : SlabObservablePairedStrandRecouplingSource D
    reflectedBentRootFaceId reflectedBentTargetFaceId
  sourcePair_eq : source.1 =
    reflectedBentGuardGraftObservableSourcePair D hcutoff hextent state
  leftPhysical : source.1.1.1.1 =
    reflectedBentGuardGraftLeftPhysical D hextent state
  rightPhysical : source.1.2.1.1 =
    reflectedBentGuardGraftRightPhysical D hextent state

opaque reflectedBentGuardGraftObservableSourcePackage
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ReflectedBentGuardGraftObservableSourcePackage
      D hcutoff hextent state := by
  refine
    { source := reflectedBentGuardGraftRawObservableRecouplingSource
        D hcutoff hextent state
      sourcePair_eq := rfl
      leftPhysical := ?_
      rightPhysical := ?_ }
  · exact reflectedBentGuardGraftLeftPositiveEntry_physical
      D hcutoff hextent state
  · exact reflectedBentGuardGraftRightExpandedEntry_physical
      D hcutoff hextent state

abbrev reflectedBentGuardGraftObservableRecouplingSource
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  (reflectedBentGuardGraftObservableSourcePackage
    D hcutoff hextent state).source

@[simp] theorem reflectedBentGuardGraftObservableRecouplingSource_leftPhysical
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftObservableRecouplingSource
      D hcutoff hextent state).1.1.1.1 =
        reflectedBentGuardGraftLeftPhysical D hextent state := by
  exact (reflectedBentGuardGraftObservableSourcePackage
    D hcutoff hextent state).leftPhysical

@[simp] theorem reflectedBentGuardGraftObservableRecouplingSource_rightPhysical
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftObservableRecouplingSource
      D hcutoff hextent state).1.2.1.1 =
        reflectedBentGuardGraftRightPhysical D hextent state := by
  exact (reflectedBentGuardGraftObservableSourcePackage
    D hcutoff hextent state).rightPhysical

#print axioms reflectedBentGuardGraftLeftPhysical_root_pos
#print axioms reflectedBentGuardGraftRightPhysical_target_zero
#print axioms reflectedBentGuardGraftObservableSourcePair_mem_fourCell
#print axioms reflectedBentGuardGraftObservableRecouplingSource

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
