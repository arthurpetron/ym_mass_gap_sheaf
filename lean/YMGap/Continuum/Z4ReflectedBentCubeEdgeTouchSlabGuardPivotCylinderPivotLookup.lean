/-
# Exact pivot lookup for every realized cylinder target

The dependent target assignment is scanned in the same order as its realized
fusion-witness assignment.  If the target is pivot-pinned, total lookup in the
realized assignment returns exactly the selected component-preserving
auxiliary at the reflected pivot.

Constructive contract: dependent-list recursion and proof irrelevance only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderLocalEdges

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderGraph

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

theorem reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_pivot_lookup_eq
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
      ReflectedBentGuardGraftPivotPinnedAtCutoff
          D hcutoff hextent state linkedList target →
      slabFusionWitnessAssignmentAt reflectedBentSwitchPivot
          (reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
            D hcutoff hextent state linkedList target) =
        reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state reflectedBentSwitchPivotLinked
  | [], _, hpinned => False.elim hpinned
  | linked :: rest, target, hpinned => by
      by_cases hpivot : linked.1 = reflectedBentSwitchPivot
      · have htarget : target.1 =
            reflectedBentGuardGraftLocalTargetAtCutoff
              D hcutoff hextent state linked := by
          simpa only [ReflectedBentGuardGraftPivotPinnedAtCutoff,
            hpivot, dite_true] using hpinned
        have hlinked : linked = reflectedBentSwitchPivotLinked :=
          Subtype.ext hpivot
        subst linked
        have hpair :=
          reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff_eq_selected
            D hcutoff hextent state reflectedBentSwitchPivotLinked
              target.1 htarget
        have hleft := congrArg (fun pair => pair.leftAuxiliary) hpair
        simpa only [
          reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff,
          slabFusionWitnessAssignmentAt, if_pos] using hleft
      · have htailPinned :
            ReflectedBentGuardGraftPivotPinnedAtCutoff
              D hcutoff hextent state rest target.2 := by
          simpa only [ReflectedBentGuardGraftPivotPinnedAtCutoff,
            hpivot, dite_false] using hpinned
        simpa only [
          reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff,
          slabFusionWitnessAssignmentAt, hpivot, if_false] using
            reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_pivot_lookup_eq
              D hcutoff hextent state rest target.2 htailPinned

#print axioms reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_pivot_lookup_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderGraph
