/-
# The pivot cylinder pins exactly the load-bearing local realization

Every target assignment can now be realized as accepted auxiliaries.  The
only extra information carried by the pivot cylinder is that, at the unique
reflected pivot, its local target is the established component-preserving
column.  This module records that invariant directly on the dependent target
assignment and proves it for every member of the cylinder list.

All nonpivot coordinates remain unrestricted.  Their later disconnection
proof must therefore use geometry and acceptedness only.

Constructive contract: dependent list recursion and literal cylinder
membership only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderRealization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-- The dependent target assignment has the distinguished selected target at
the first (and, on the actual duplicate-free link list, unique) pivot. -/
def ReflectedBentGuardGraftPivotPinnedAtCutoff
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
          linked) → Prop
  | [], _ => False
  | linked :: rest, target =>
      if _hpivot : linked.1 = reflectedBentSwitchPivot then
        target.1 = reflectedBentGuardGraftLocalTargetAtCutoff
          D hcutoff hextent state linked
      else
        ReflectedBentGuardGraftPivotPinnedAtCutoff
          D hcutoff hextent state rest target.2

/-- Cylinder membership remembers precisely the selected pivot coordinate;
all target coordinates away from the pivot are free. -/
theorem reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_pinned
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
      target ∈
        reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
          D hcutoff hextent state linkedList →
      ReflectedBentGuardGraftPivotPinnedAtCutoff
        D hcutoff hextent state linkedList target
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | linked :: rest, target, hmem => by
      by_cases hpivot : linked.1 = reflectedBentSwitchPivot
      · simp only [ReflectedBentGuardGraftPivotPinnedAtCutoff,
          hpivot, dite_true]
        simp only [
          reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_true] at hmem
        obtain ⟨tail, _, heq⟩ := List.mem_map.mp hmem
        have hfirst := congrArg Prod.fst heq
        exact hfirst.symm
      · simp only [ReflectedBentGuardGraftPivotPinnedAtCutoff,
          hpivot, dite_false]
        simp only [
          reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_false] at hmem
        obtain ⟨localTarget, _, hlocal⟩ := List.mem_flatMap.mp hmem
        obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hlocal
        have hsecond := congrArg Prod.snd heq
        exact
          reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_pinned
            D hcutoff hextent state rest target.2
              (hsecond.symm ▸ htail)

/-- Equal local target columns have definitionally equal canonical accepted
realizations.  This is the bridge used at the pinned pivot. -/
theorem reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff_eq_selected
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      linked).Target)
    (htarget : target = reflectedBentGuardGraftLocalTargetAtCutoff
      D hcutoff hextent state linked) :
    reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff
        D hcutoff hextent state linked target =
      reflectedBentGuardGraftLocalRealizedPairAtCutoff
        D hcutoff hextent state linked := by
  subst target
  rfl

#print axioms ReflectedBentGuardGraftPivotPinnedAtCutoff
#print axioms reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_pinned
#print axioms reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff_eq_selected

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderRealization
