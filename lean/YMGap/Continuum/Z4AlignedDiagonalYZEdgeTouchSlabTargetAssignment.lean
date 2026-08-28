/-
# Complete aligned target assignment with the rank-one pivot

Override the constructive first-target selector at the unique aligned pivot
with the written `m = 2` column.  At every other actual slab link, retain the
generic first target.  Structural recursion builds a correctly typed target
for every finite linked list and proves literal membership in the complete
heterogeneous target enumeration.

Constructive contract: explicit finite target selection and dependent
products only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingFirstTarget
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetAssignment

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
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. The accepted source anchor -/

theorem alignedDiagonalSwitchLeftAssignment_mem :
    alignedDiagonalSwitchLeftFineWitness.1 ∈
      slabFusionWitnessAssignmentsOn 1 5 alignedDiagonalSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5) := by
  have h := alignedDiagonalSwitchLeftFineWitness.2
  change alignedDiagonalSwitchLeftFineWitness.1 ∈
    slabFusionWitnessAssignmentsOn 1 5 alignedDiagonalSwitchLeftPhysical
      (boundaryCompleteSlabLinks 5) at h
  exact h

theorem alignedDiagonalSwitchRightAssignment_mem :
    alignedDiagonalSwitchRightFineWitness.1 ∈
      slabFusionWitnessAssignmentsOn 1 5 alignedDiagonalSwitchRightPhysical
        (boundaryCompleteSlabLinks 5) := by
  have h := alignedDiagonalSwitchRightFineWitness.2
  change alignedDiagonalSwitchRightFineWitness.1 ∈
    slabFusionWitnessAssignmentsOn 1 5 alignedDiagonalSwitchRightPhysical
      (boundaryCompleteSlabLinks 5) at h
  exact h

/-! ## 2. Total local selector -/

def alignedDiagonalSwitchTargetForData :
    (degree : Nat) ->
    (D : SlabPhysicalPairRecouplingData 5 degree) ->
    D.leftPhysical = alignedDiagonalSwitchLeftPhysical ->
    D.rightPhysical = alignedDiagonalSwitchRightPhysical ->
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
      by_cases hpivot : D.link = alignedDiagonalSwitchPivot
      · have hdata : D = alignedDiagonalSwitchPivotRecouplingData := by
          cases D with
          | mk leftPhysical rightPhysical link degree_eq =>
              dsimp at hleft hright hpivot
              cases hleft
              cases hright
              cases hpivot
              rfl
        rw [hdata]
        exact alignedDiagonalPivotTarget
      · exact slabPhysicalPairRecouplingFirstTarget 5 D source
  | 6, D, _, _, source =>
      slabPhysicalPairRecouplingFirstTarget 6 D source
  | degree + 7, D, _, _, _ => False.elim (by
      have hdegree := D.degree_le_six
      omega)

/-! ## 3. Structural whole-product assembly -/

def alignedDiagonalSwitchTargetAssignmentFrom :
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) ->
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          alignedDiagonalSwitchLeftPhysical
          alignedDiagonalSwitchRightPhysical linked)
  | [] => ()
  | linked :: rest => by
      let localData := slabPhysicalPairRecouplingDataAtLink 5
        alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchRightPhysical linked
      let anchor := slabPhysicalPairRecouplingWitnessDataAtLink 1 5
        alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchRightPhysical
        alignedDiagonalSwitchLeftFineWitness.1
        alignedDiagonalSwitchRightFineWitness.1
        alignedDiagonalSwitchLeftAssignment_mem
        alignedDiagonalSwitchRightAssignment_mem linked
      let source := slabPhysicalPairRecouplingProductionSource
        (slabIncidentPlaqIds 5 linked.1).length localData anchor
      refine (by
        unfold slabPhysicalPairRecouplingPackageAtLink
        exact alignedDiagonalSwitchTargetForData
          (slabIncidentPlaqIds 5 linked.1).length
          localData rfl rfl source,
        alignedDiagonalSwitchTargetAssignmentFrom rest)

theorem alignedDiagonalSwitchTargetAssignmentFrom_mem :
    forall linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks 5},
    alignedDiagonalSwitchTargetAssignmentFrom linkedList ∈
      finiteBistochasticTargetAssignments
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            alignedDiagonalSwitchLeftPhysical
            alignedDiagonalSwitchRightPhysical linked)
  | [] => List.mem_cons_self
  | linked :: rest => by
      apply List.mem_flatMap.mpr
      refine ⟨(alignedDiagonalSwitchTargetAssignmentFrom
        (linked :: rest)).1, ?_, ?_⟩
      · unfold slabPhysicalPairRecouplingPackageAtLink
        exact slabPhysicalPairRecouplingTarget_mem
          (slabIncidentPlaqIds 5 linked.1).length
          (slabPhysicalPairRecouplingDataAtLink 5
            alignedDiagonalSwitchLeftPhysical
            alignedDiagonalSwitchRightPhysical linked)
          (alignedDiagonalSwitchTargetAssignmentFrom
            (linked :: rest)).1
      apply List.mem_map.mpr
      exact ⟨alignedDiagonalSwitchTargetAssignmentFrom rest,
        alignedDiagonalSwitchTargetAssignmentFrom_mem rest, rfl⟩

theorem alignedDiagonalSwitchTargetExistsFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    ∃ target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            alignedDiagonalSwitchLeftPhysical
            alignedDiagonalSwitchRightPhysical linked),
      target ∈ finiteBistochasticTargetAssignments
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            alignedDiagonalSwitchLeftPhysical
            alignedDiagonalSwitchRightPhysical linked) :=
  ⟨alignedDiagonalSwitchTargetAssignmentFrom linkedList,
    alignedDiagonalSwitchTargetAssignmentFrom_mem linkedList⟩

theorem alignedDiagonalSwitchTargetForPivot_eq
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      alignedDiagonalSwitchPivotRecouplingData).Source) :
    alignedDiagonalSwitchTargetForData 5
      alignedDiagonalSwitchPivotRecouplingData rfl rfl source =
        alignedDiagonalPivotTarget := by
  simp [alignedDiagonalSwitchTargetForData,
    alignedDiagonalSwitchPivotRecouplingData]

#print axioms alignedDiagonalSwitchLeftAssignment_mem
#print axioms alignedDiagonalSwitchRightAssignment_mem
#print axioms alignedDiagonalSwitchTargetForData
#print axioms alignedDiagonalSwitchTargetAssignmentFrom_mem
#print axioms alignedDiagonalSwitchTargetExistsFrom
#print axioms alignedDiagonalSwitchTargetForPivot_eq

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetAssignment
