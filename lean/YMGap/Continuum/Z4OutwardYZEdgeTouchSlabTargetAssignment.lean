/-
# A complete target assignment with the distinguished outward Y/Z pivot

Compile the local within-component pivot column into a target coordinate at
the unique cut link.  At every other slab link, the accepted source row and
the all-valence first-target compiler choose one literal target column.
Structural recursion then builds a correctly typed column of the complete
heterogeneous slab product and proves membership in its target enumeration.

This module solves the dependent target-assembly problem.  Canonical
realization and the two-color marked-face disconnection proof are the next
geometric contraction.

Constructive contract: finite target selection, explicit SU(2) carriers, and
structural dependent products only; no choice, `Classical`, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingFirstTarget
import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabTargetAssignment

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingFirstTarget
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. The accepted explicit anchor -/

theorem outwardYZSwitchLeftAssignment_mem :
    outwardYZSwitchLeftFineWitness.1 ∈
      slabFusionWitnessAssignmentsOn 1 5 outwardYZSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5) := by
  have h := outwardYZSwitchLeftFineWitness.2
  change outwardYZSwitchLeftFineWitness.1 ∈
    slabFusionWitnessAssignmentsOn 1 5 outwardYZSwitchLeftPhysical
      (boundaryCompleteSlabLinks 5) at h
  exact h

theorem outwardYZSwitchRightAssignment_mem :
    outwardYZSwitchRightFineWitness.1 ∈
      slabFusionWitnessAssignmentsOn 1 5 outwardYZSwitchRightPhysical
        (boundaryCompleteSlabLinks 5) := by
  have h := outwardYZSwitchRightFineWitness.2
  change outwardYZSwitchRightFineWitness.1 ∈
    slabFusionWitnessAssignmentsOn 1 5 outwardYZSwitchRightPhysical
      (boundaryCompleteSlabLinks 5) at h
  exact h

/-! ## 2. One total local target selector -/

/-- An all-valence selector which overrides precisely the degree-five pivot.
Splitting on the seven possible degrees before inspecting the link keeps the
dependent carrier fixed in every branch. -/
def outwardYZSwitchTargetForData :
    (degree : Nat) ->
    (D : SlabPhysicalPairRecouplingData 5 degree) ->
    D.leftPhysical = outwardYZSwitchLeftPhysical ->
    D.rightPhysical = outwardYZSwitchRightPhysical ->
    (source : (slabPhysicalPairRecouplingKernelPackage degree D).Source) ->
      (slabPhysicalPairRecouplingKernelPackage degree D).Target
  | 0, D, _, _, source =>
      slabPhysicalPairRecouplingFirstTarget 0 D source
  | 1, D, _, _, source =>
      slabPhysicalPairRecouplingFirstTarget 1 D source
  | 2, D, _, _, source =>
      slabPhysicalPairRecouplingFirstTarget 2 D source
  | 3, D, _, _, source =>
      slabPhysicalPairRecouplingFirstTarget 3 D source
  | 4, D, _, _, source =>
      slabPhysicalPairRecouplingFirstTarget 4 D source
  | 5, D, hleft, hright, source => by
      by_cases hpivot : D.link = outwardYZSwitchPivot
      · have hdata : D = outwardYZSwitchPivotRecouplingData := by
          cases D with
          | mk leftPhysical rightPhysical link degree_eq =>
              dsimp at hleft hright hpivot
              cases hleft
              cases hright
              cases hpivot
              rfl
        rw [hdata]
        exact outwardYZPivotTarget
      · exact slabPhysicalPairRecouplingFirstTarget 5 D source
  | 6, D, _, _, source =>
      slabPhysicalPairRecouplingFirstTarget 6 D source
  | degree + 7, D, _, _, _ => False.elim (by
      have hdegree := D.degree_le_six
      omega)

/-! ## 3. Structural whole-product assembly -/

def outwardYZSwitchTargetAssignmentFrom :
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) ->
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked)
  | [] => ()
  | linked :: rest => by
      let localData := slabPhysicalPairRecouplingDataAtLink 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked
      let anchor := slabPhysicalPairRecouplingWitnessDataAtLink 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical
        outwardYZSwitchLeftFineWitness.1 outwardYZSwitchRightFineWitness.1
        outwardYZSwitchLeftAssignment_mem
        outwardYZSwitchRightAssignment_mem linked
      let source := slabPhysicalPairRecouplingProductionSource
        (slabIncidentPlaqIds 5 linked.1).length localData anchor
      refine (by
        unfold slabPhysicalPairRecouplingPackageAtLink
        exact outwardYZSwitchTargetForData
          (slabIncidentPlaqIds 5 linked.1).length
          localData rfl rfl source,
        outwardYZSwitchTargetAssignmentFrom rest)

theorem outwardYZSwitchTargetAssignmentFrom_mem :
    forall linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks 5},
    outwardYZSwitchTargetAssignmentFrom linkedList ∈
      finiteBistochasticTargetAssignments
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked)
  | [] => List.mem_cons_self
  | linked :: rest => by
      apply List.mem_flatMap.mpr
      refine ⟨(outwardYZSwitchTargetAssignmentFrom
        (linked :: rest)).1, ?_, ?_⟩
      · unfold slabPhysicalPairRecouplingPackageAtLink
        exact slabPhysicalPairRecouplingTarget_mem
          (slabIncidentPlaqIds 5 linked.1).length
          (slabPhysicalPairRecouplingDataAtLink 5
            outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked)
          (outwardYZSwitchTargetAssignmentFrom (linked :: rest)).1
      apply List.mem_map.mpr
      exact ⟨outwardYZSwitchTargetAssignmentFrom rest,
        outwardYZSwitchTargetAssignmentFrom_mem rest, rfl⟩

/-- Transport a heterogeneous target assignment across equality of its
package list without asking elaboration to normalize either list. -/
def transportFiniteBistochasticTargetAssignment
    {left right : List FiniteBistochasticQKernelPackage}
    (heq : left = right)
    (target : FiniteBistochasticTargetAssignment left) :
    FiniteBistochasticTargetAssignment right := by
  rw [← heq]
  exact target

def outwardYZSwitchTargetPackages_eq :
    ((boundaryCompleteSlabLinks 5).attach.map fun linked =>
      slabPhysicalPairRecouplingPackageAtLink 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked) =
      slabPhysicalPairRecouplingPackages 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical := by
  rfl

/-- Every symbolic linked list has a complete target column, with literal
membership in the corresponding heterogeneous product enumeration.  Keeping
the list symbolic lets Lean check the mathematical compiler without reducing
the 1,554-coordinate concrete slab tuple. -/
theorem outwardYZSwitchTargetExistsFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    ∃ target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked),
      target ∈ finiteBistochasticTargetAssignments
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked) :=
  ⟨outwardYZSwitchTargetAssignmentFrom linkedList,
    outwardYZSwitchTargetAssignmentFrom_mem linkedList⟩

/-- The compiler chooses the distinguished recoupling column at the pivot,
independently of the accepted local source anchor. -/
theorem outwardYZSwitchTargetForPivot_eq
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZSwitchPivotRecouplingData).Source) :
    outwardYZSwitchTargetForData 5 outwardYZSwitchPivotRecouplingData
      rfl rfl source = outwardYZPivotTarget := by
  simp [outwardYZSwitchTargetForData, outwardYZSwitchPivotRecouplingData]

#print axioms outwardYZSwitchLeftAssignment_mem
#print axioms outwardYZSwitchRightAssignment_mem
#print axioms outwardYZSwitchTargetForData
#print axioms outwardYZSwitchTargetAssignmentFrom_mem
#print axioms transportFiniteBistochasticTargetAssignment
#print axioms outwardYZSwitchTargetExistsFrom
#print axioms outwardYZSwitchTargetForPivot_eq

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabTargetAssignment
