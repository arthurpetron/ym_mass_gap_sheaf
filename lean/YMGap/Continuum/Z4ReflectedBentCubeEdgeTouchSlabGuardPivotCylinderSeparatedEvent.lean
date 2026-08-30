/-
# The quarter-mass pivot cylinder is a separated recoupling event

The cylinder weight theorem and the universal cylinder disconnection theorem
have the same parametric target carrier.  This module contracts them into one
data-bearing event: a literal list of recoupling targets with total normalized
row weight at least `1/4`, every member of which disconnects the marked faces.

Constructive contract: explicit finite target lists, rational weights, and
data-bearing disconnection witnesses only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderDisconnection

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderSeparatedEvent

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

/-- The normalized product-row weight on the same parametric written list used
by the pivot cylinder and its realized projected graph. -/
def reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) :
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked) → Q' :=
  finiteBistochasticProductWeight
    (slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      (reflectedBentGuardGraftLeftAssignment D hextent state)
      (reflectedBentGuardGraftRightAssignment D hextent state)
      (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
        D hcutoff hextent state)
      linkedList)

/-- A literal separated event in one normalized guarded recoupling row.  Both
the quantitative mass floor and the qualitative disconnection witnesses are
retained as fields over the same target list. -/
structure ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) : Type where
  targets : List
    (FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
  targets_eq : targets =
    reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
      D hcutoff hextent state linkedList
  weight_floor : oneQuarter ≤
    listQSum
      (reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
        D hcutoff hextent state linkedList)
      targets
  every_target_disconnected : ∀ target, target ∈ targets →
    ReflectedBentGuardGraftPivotCylinderTargetDisconnectionAtCutoff
      D hcutoff hextent state linkedList target

/-- **Quarter-mass separated cylinder event.**  Duplicate-freeness and pivot
membership are precisely the two list conditions shared by the exact weight
summation and the universal graph proof. -/
def reflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hnodup : linkedList.Nodup)
    (hpivot : reflectedBentSwitchPivotLinked ∈ linkedList) :
    ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      D hcutoff hextent state linkedList where
  targets := reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
    D hcutoff hextent state linkedList
  targets_eq := rfl
  weight_floor := by
    simpa only [
      reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff] using
      reflectedBentGuardGraftPivotCylinderFromAtCutoff_weight_sum_floor
        D hcutoff hextent state linkedList hnodup hpivot
  every_target_disconnected := fun target htarget =>
    reflectedBentGuardGraftPivotCylinderTargetDisconnectionAtCutoff
      D hcutoff hextent state linkedList target hnodup hpivot htarget

#print axioms reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
#print axioms reflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderSeparatedEvent
