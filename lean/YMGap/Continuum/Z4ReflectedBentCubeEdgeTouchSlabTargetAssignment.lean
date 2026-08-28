/-
# Complete reflected bent-cube target assignment

Override the constructive first-target selector at the unique reflected pivot
with the component-preserving rank-zero column.  At every other actual slab
link retain the generic first target.  Structural recursion builds a typed
target for every finite linked list and proves membership in the complete
heterogeneous target enumeration.

Constructive contract: explicit finite target selection and dependent
products only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingFirstTarget
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabNonpivotPairing

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetAssignment

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
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

/-! ## 1. The accepted source anchor -/

theorem reflectedBentSwitchLeftAssignment_mem :
    reflectedBentLeftFineWitness.1 ∈
      slabFusionWitnessAssignmentsOn 1 5 reflectedBentSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5) := by
  have h := reflectedBentLeftFineWitness.2
  change reflectedBentLeftFineWitness.1 ∈
    slabFusionWitnessAssignmentsOn 1 5 reflectedBentSwitchLeftPhysical
      (boundaryCompleteSlabLinks 5) at h
  exact h

theorem reflectedBentSwitchRightAssignment_mem :
    reflectedBentRightFineWitness.1 ∈
      slabFusionWitnessAssignmentsOn 1 5 reflectedBentSwitchRightPhysical
        (boundaryCompleteSlabLinks 5) := by
  have h := reflectedBentRightFineWitness.2
  change reflectedBentRightFineWitness.1 ∈
    slabFusionWitnessAssignmentsOn 1 5 reflectedBentSwitchRightPhysical
      (boundaryCompleteSlabLinks 5) at h
  exact h

/-! ## 2. Total local selector -/

def reflectedBentSwitchTargetForData :
    (degree : Nat) ->
    (D : SlabPhysicalPairRecouplingData 5 degree) ->
    D.leftPhysical = reflectedBentSwitchLeftPhysical ->
    D.rightPhysical = reflectedBentSwitchRightPhysical ->
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
      by_cases hpivot : D.link = reflectedBentSwitchPivot
      · have hdata : D = reflectedBentSwitchPivotRecouplingData := by
          cases D with
          | mk leftPhysical rightPhysical link degree_eq =>
              dsimp at hleft hright hpivot
              cases hleft
              cases hright
              cases hpivot
              rfl
        rw [hdata]
        exact reflectedBentPivotTarget
      · exact slabPhysicalPairRecouplingFirstTarget 5 D source
  | 6, D, _, _, source =>
      slabPhysicalPairRecouplingFirstTarget 6 D source
  | degree + 7, D, _, _, _ => False.elim (by
      have hdegree := D.degree_le_six
      omega)

/-! ## 3. Structural whole-product assembly -/

def reflectedBentSwitchTargetAssignmentFrom :
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) ->
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          reflectedBentSwitchLeftPhysical
          reflectedBentSwitchRightPhysical linked)
  | [] => ()
  | linked :: rest => by
      let localData := slabPhysicalPairRecouplingDataAtLink 5
        reflectedBentSwitchLeftPhysical
        reflectedBentSwitchRightPhysical linked
      let anchor := slabPhysicalPairRecouplingWitnessDataAtLink 1 5
        reflectedBentSwitchLeftPhysical
        reflectedBentSwitchRightPhysical
        reflectedBentLeftFineWitness.1
        reflectedBentRightFineWitness.1
        reflectedBentSwitchLeftAssignment_mem
        reflectedBentSwitchRightAssignment_mem linked
      let source := slabPhysicalPairRecouplingProductionSource
        (slabIncidentPlaqIds 5 linked.1).length localData anchor
      refine (by
        unfold slabPhysicalPairRecouplingPackageAtLink
        exact reflectedBentSwitchTargetForData
          (slabIncidentPlaqIds 5 linked.1).length
          localData rfl rfl source,
        reflectedBentSwitchTargetAssignmentFrom rest)

theorem reflectedBentSwitchTargetAssignmentFrom_mem :
    forall linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks 5},
    reflectedBentSwitchTargetAssignmentFrom linkedList ∈
      finiteBistochasticTargetAssignments
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            reflectedBentSwitchLeftPhysical
            reflectedBentSwitchRightPhysical linked)
  | [] => List.mem_cons_self
  | linked :: rest => by
      apply List.mem_flatMap.mpr
      refine ⟨(reflectedBentSwitchTargetAssignmentFrom
        (linked :: rest)).1, ?_, ?_⟩
      · unfold slabPhysicalPairRecouplingPackageAtLink
        exact slabPhysicalPairRecouplingTarget_mem
          (slabIncidentPlaqIds 5 linked.1).length
          (slabPhysicalPairRecouplingDataAtLink 5
            reflectedBentSwitchLeftPhysical
            reflectedBentSwitchRightPhysical linked)
          (reflectedBentSwitchTargetAssignmentFrom
            (linked :: rest)).1
      apply List.mem_map.mpr
      exact ⟨reflectedBentSwitchTargetAssignmentFrom rest,
        reflectedBentSwitchTargetAssignmentFrom_mem rest, rfl⟩

theorem reflectedBentSwitchTargetForPivot_eq
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      reflectedBentSwitchPivotRecouplingData).Source) :
    reflectedBentSwitchTargetForData 5
      reflectedBentSwitchPivotRecouplingData rfl rfl source =
        reflectedBentPivotTarget := by
  simp [reflectedBentSwitchTargetForData,
    reflectedBentSwitchPivotRecouplingData]

#print axioms reflectedBentSwitchLeftAssignment_mem
#print axioms reflectedBentSwitchRightAssignment_mem
#print axioms reflectedBentSwitchTargetForData
#print axioms reflectedBentSwitchTargetAssignmentFrom_mem
#print axioms reflectedBentSwitchTargetForPivot_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetAssignment
