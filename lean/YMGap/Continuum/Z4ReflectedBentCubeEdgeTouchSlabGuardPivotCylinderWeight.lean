/-
# A cutoff-uniform pivot cylinder in the guarded recoupling row

The earlier guarded target fixed one positive column at every slab link.
That proves qualitative positivity but needlessly pays cutoff-sensitive local
columns away from the unique non-abelian pivot.

Here the target event fixes only the component-preserving pivot column.  Every
target coordinate before the pivot is summed over its complete normalized
row, and after the pivot all remaining coordinates are summed at once.  The
whole cylinder therefore has exactly the mass of the pivot entry, hence at
least `1/4` at every ambient cutoff at least one.

Constructive contract: one explicit SU(2) pivot column, exact finite row
normalization elsewhere, and dependent finite products only; no `Classical`,
choice, `native_decide`, `sorry`, new axiom, noncomputable declaration, or
unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mul_right_local {A : Type}
    (weight : A → Q') (factor : Q') :
    ∀ items : List A,
      listQSum (fun item => weight item * factor) items ≈
        listQSum weight items * factor
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv factor)
  | head :: tail => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_refl (weight head * factor))
          (listQSum_mul_right_local weight factor tail))
        (Q'.eqv_symm
          (Q'.add_mul_eqv (weight head) (listQSum weight tail) factor))

/-- The target cylinder encountered while scanning the written slab-link list.
Before the pivot, every local target is retained.  At the pivot, only the
component-preserving target is retained; the entire tail is then free. -/
def reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) →
      List (FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked))
  | [] => []
  | linked :: rest =>
      if _hpivot : linked.1 = reflectedBentSwitchPivot then
        (finiteBistochasticTargetAssignments
          (rest.map fun tailLinked =>
            slabPhysicalPairRecouplingPackageAtLink 5
              (reflectedBentGuardGraftLeftPhysical D hextent state)
              (reflectedBentGuardGraftRightPhysical D hextent state)
              tailLinked)).map fun tail =>
          (reflectedBentGuardGraftLocalTargetAtCutoff
              D hcutoff hextent state linked,
            tail)
      else
        (slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked).kernel.targets.flatMap fun target =>
            (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
              D hcutoff hextent state rest).map fun tail =>
                (target, tail)

/-- If the written list is duplicate-free and contains the pivot, freely
summing every nonpivot target leaves at least the pivot quarter. -/
theorem reflectedBentGuardGraftPivotCylinderFromAtCutoff_weight_sum_floor
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5}),
      linkedList.Nodup →
      reflectedBentSwitchPivotLinked ∈ linkedList →
      oneQuarter ≤
        listQSum
          (finiteBistochasticProductWeight
            (slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
              (reflectedBentGuardGraftLeftPhysical D hextent state)
              (reflectedBentGuardGraftRightPhysical D hextent state)
              (reflectedBentGuardGraftLeftAssignment D hextent state)
              (reflectedBentGuardGraftRightAssignment D hextent state)
              (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                D hcutoff hextent state)
              (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                D hcutoff hextent state)
              linkedList))
          (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
            D hcutoff hextent state linkedList)
  | [], _, hpivot => False.elim (List.not_mem_nil hpivot)
  | linked :: rest, hnodup, hpivotMem => by
      have hnodupParts := List.nodup_cons.mp hnodup
      by_cases hpivot : linked.1 = reflectedBentSwitchPivot
      · simp only [
          reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_true, List.map_cons,
          slabPhysicalPairRecouplingProductionSourceFrom]
        rw [listQSum_map]
        have hsum :
            listQSum
                (fun tail =>
                  (slabPhysicalPairRecouplingPackageAtLink 5
                    (reflectedBentGuardGraftLeftPhysical D hextent state)
                    (reflectedBentGuardGraftRightPhysical D hextent state)
                    linked).kernel.weight
                      (reflectedBentGuardGraftLocalSourceAtCutoff
                        D hcutoff hextent state linked)
                      (reflectedBentGuardGraftLocalTargetAtCutoff
                        D hcutoff hextent state linked) *
                    finiteBistochasticProductWeight
                      (slabPhysicalPairRecouplingProductionSourceFrom
                        D.cutoff 5
                        (reflectedBentGuardGraftLeftPhysical
                          D hextent state)
                        (reflectedBentGuardGraftRightPhysical
                          D hextent state)
                        (reflectedBentGuardGraftLeftAssignment
                          D hextent state)
                        (reflectedBentGuardGraftRightAssignment
                          D hextent state)
                        (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                          D hcutoff hextent state)
                        (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                          D hcutoff hextent state)
                        rest) tail)
                (finiteBistochasticTargetAssignments
                  (rest.map fun tailLinked =>
                    slabPhysicalPairRecouplingPackageAtLink 5
                      (reflectedBentGuardGraftLeftPhysical D hextent state)
                      (reflectedBentGuardGraftRightPhysical D hextent state)
                      tailLinked)) ≈
              (slabPhysicalPairRecouplingPackageAtLink 5
                (reflectedBentGuardGraftLeftPhysical D hextent state)
                (reflectedBentGuardGraftRightPhysical D hextent state)
                linked).kernel.weight
                  (reflectedBentGuardGraftLocalSourceAtCutoff
                    D hcutoff hextent state linked)
                  (reflectedBentGuardGraftLocalTargetAtCutoff
                    D hcutoff hextent state linked) := by
          refine Q'.eqv_trans _ _ _
            (listQSum_mul_left
              ((slabPhysicalPairRecouplingPackageAtLink 5
                (reflectedBentGuardGraftLeftPhysical D hextent state)
                (reflectedBentGuardGraftRightPhysical D hextent state)
                linked).kernel.weight
                  (reflectedBentGuardGraftLocalSourceAtCutoff
                    D hcutoff hextent state linked)
                  (reflectedBentGuardGraftLocalTargetAtCutoff
                    D hcutoff hextent state linked))
              (finiteBistochasticProductWeight
                (slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
                  (reflectedBentGuardGraftLeftPhysical D hextent state)
                  (reflectedBentGuardGraftRightPhysical D hextent state)
                  (reflectedBentGuardGraftLeftAssignment D hextent state)
                  (reflectedBentGuardGraftRightAssignment D hextent state)
                  (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                    D hcutoff hextent state)
                  (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                    D hcutoff hextent state)
                  rest))
              (finiteBistochasticTargetAssignments
                (rest.map fun tailLinked =>
                  slabPhysicalPairRecouplingPackageAtLink 5
                    (reflectedBentGuardGraftLeftPhysical D hextent state)
                    (reflectedBentGuardGraftRightPhysical D hextent state)
                    tailLinked)) ) ?_
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (finiteBistochasticProduct_row_normalized _ _))
            (Q'.mul_one_eqv _)
        exact Q'.le_trans' _ _ _
          (reflectedBentGuardGraftLocalTargetAtCutoff_floor_of_pivot
            D hcutoff hextent state linked hpivot)
          (Q'.le_of_eqv (Q'.eqv_symm hsum))
      · simp only [
          reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_false, List.map_cons,
          slabPhysicalPairRecouplingProductionSourceFrom]
        have hpivotTail : reflectedBentSwitchPivotLinked ∈ rest := by
          rcases List.mem_cons.mp hpivotMem with hhead | htail
          · have hvalue := congrArg Subtype.val hhead
            exact False.elim (hpivot hvalue.symm)
          · exact htail
        have ih :=
          reflectedBentGuardGraftPivotCylinderFromAtCutoff_weight_sum_floor
            D hcutoff hextent state rest hnodupParts.2 hpivotTail
        have hsum :
            listQSum
                (finiteBistochasticProductWeight
                  (slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
                    (reflectedBentGuardGraftLeftPhysical D hextent state)
                    (reflectedBentGuardGraftRightPhysical D hextent state)
                    (reflectedBentGuardGraftLeftAssignment D hextent state)
                    (reflectedBentGuardGraftRightAssignment D hextent state)
                    (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                      D hcutoff hextent state)
                    (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                      D hcutoff hextent state)
                    (linked :: rest)))
                ((slabPhysicalPairRecouplingPackageAtLink 5
                  (reflectedBentGuardGraftLeftPhysical D hextent state)
                  (reflectedBentGuardGraftRightPhysical D hextent state)
                  linked).kernel.targets.flatMap fun target =>
                    (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
                      D hcutoff hextent state rest).map fun tail =>
                        (target, tail)) ≈
              listQSum
                (finiteBistochasticProductWeight
                  (slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
                    (reflectedBentGuardGraftLeftPhysical D hextent state)
                    (reflectedBentGuardGraftRightPhysical D hextent state)
                    (reflectedBentGuardGraftLeftAssignment D hextent state)
                    (reflectedBentGuardGraftRightAssignment D hextent state)
                    (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                      D hcutoff hextent state)
                    (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                      D hcutoff hextent state)
                    rest))
                (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
                  D hcutoff hextent state rest) := by
          let tailMass : Q' :=
            listQSum
              (finiteBistochasticProductWeight
                (slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
                  (reflectedBentGuardGraftLeftPhysical D hextent state)
                  (reflectedBentGuardGraftRightPhysical D hextent state)
                  (reflectedBentGuardGraftLeftAssignment D hextent state)
                  (reflectedBentGuardGraftRightAssignment D hextent state)
                  (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                    D hcutoff hextent state)
                  (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                    D hcutoff hextent state)
                  rest))
              (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
                D hcutoff hextent state rest)
          refine Q'.eqv_trans _ _ _
            (listQSum_flatMap _ _ _ ) ?_
          refine Q'.eqv_trans _
            (listQSum
              (fun target =>
                (slabPhysicalPairRecouplingPackageAtLink 5
                  (reflectedBentGuardGraftLeftPhysical D hextent state)
                  (reflectedBentGuardGraftRightPhysical D hextent state)
                  linked).kernel.weight
                    (reflectedBentGuardGraftLocalSourceAtCutoff
                      D hcutoff hextent state linked) target * tailMass)
              (slabPhysicalPairRecouplingPackageAtLink 5
                (reflectedBentGuardGraftLeftPhysical D hextent state)
                (reflectedBentGuardGraftRightPhysical D hextent state)
                linked).kernel.targets) _
            (listQSum_congr
              (f := fun target =>
                listQSum
                  (finiteBistochasticProductWeight
                    (slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
                      (reflectedBentGuardGraftLeftPhysical D hextent state)
                      (reflectedBentGuardGraftRightPhysical D hextent state)
                      (reflectedBentGuardGraftLeftAssignment D hextent state)
                      (reflectedBentGuardGraftRightAssignment D hextent state)
                      (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                        D hcutoff hextent state)
                      (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                        D hcutoff hextent state)
                      (linked :: rest)))
                  ((reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
                    D hcutoff hextent state rest).map fun tail =>
                      (target, tail)))
              (g := fun target =>
                (slabPhysicalPairRecouplingPackageAtLink 5
                  (reflectedBentGuardGraftLeftPhysical D hextent state)
                  (reflectedBentGuardGraftRightPhysical D hextent state)
                  linked).kernel.weight
                    (reflectedBentGuardGraftLocalSourceAtCutoff
                      D hcutoff hextent state linked) target * tailMass)
              (fun target => ?_)
              (slabPhysicalPairRecouplingPackageAtLink 5
                (reflectedBentGuardGraftLeftPhysical D hextent state)
                (reflectedBentGuardGraftRightPhysical D hextent state)
                linked).kernel.targets) ?_
          · dsimp only
            rw [listQSum_map]
            change listQSum
                (fun tail =>
                  (slabPhysicalPairRecouplingPackageAtLink 5
                    (reflectedBentGuardGraftLeftPhysical D hextent state)
                    (reflectedBentGuardGraftRightPhysical D hextent state)
                    linked).kernel.weight
                      (reflectedBentGuardGraftLocalSourceAtCutoff
                        D hcutoff hextent state linked) target *
                    finiteBistochasticProductWeight
                      (slabPhysicalPairRecouplingProductionSourceFrom
                        D.cutoff 5
                        (reflectedBentGuardGraftLeftPhysical D hextent state)
                        (reflectedBentGuardGraftRightPhysical D hextent state)
                        (reflectedBentGuardGraftLeftAssignment D hextent state)
                        (reflectedBentGuardGraftRightAssignment D hextent state)
                        (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
                          D hcutoff hextent state)
                        (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
                          D hcutoff hextent state)
                        rest) tail)
                (reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
                  D hcutoff hextent state rest) ≈ _
            exact listQSum_mul_left _ _ _
          · refine Q'.eqv_trans _ _ _
              (listQSum_mul_right_local _ _ _) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                ((slabPhysicalPairRecouplingPackageAtLink 5
                  (reflectedBentGuardGraftLeftPhysical D hextent state)
                  (reflectedBentGuardGraftRightPhysical D hextent state)
                  linked).kernel.row_normalized
                    (reflectedBentGuardGraftLocalSourceAtCutoff
                      D hcutoff hextent state linked))) ?_
            exact Q'.one_mul_eqv _
        exact Q'.le_trans' _ _ _ ih
          (Q'.le_of_eqv (Q'.eqv_symm hsum))

#print axioms reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
#print axioms reflectedBentGuardGraftPivotCylinderFromAtCutoff_weight_sum_floor

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight
