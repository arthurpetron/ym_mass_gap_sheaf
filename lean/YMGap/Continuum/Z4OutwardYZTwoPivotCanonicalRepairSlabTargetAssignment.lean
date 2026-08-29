/-
# Complete target assignment for the two-pivot outward repair surface

Override the complete slab product at exactly the spatial and temporal repair
pivots by the two columns whose equal-rank representatives preserve the two
lobes.  At every other link, use the total first-target selector.  Structural
recursion builds a correctly typed heterogeneous target assignment and proves
its finite-product membership.

Constructive contract: finite target selection and structural dependent
products only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingFirstTarget
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotTarget

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetAssignment

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

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
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotTarget
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile

theorem outwardYZCanonicalRepairSwitchLeftAssignment_mem :
    outwardYZCanonicalRepairLeftFineWitness.1 ∈
      slabFusionWitnessAssignmentsOn 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5) := by
  have h := outwardYZCanonicalRepairLeftFineWitness.2
  change outwardYZCanonicalRepairLeftFineWitness.1 ∈
    slabFusionWitnessAssignmentsOn 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      (boundaryCompleteSlabLinks 5) at h
  exact h

theorem outwardYZCanonicalRepairSwitchRightAssignment_mem :
    outwardYZCanonicalRepairRightFineWitness.1 ∈
      slabFusionWitnessAssignmentsOn 1 5
        outwardYZCanonicalRepairSwitchRightPhysical
        (boundaryCompleteSlabLinks 5) := by
  have h := outwardYZCanonicalRepairRightFineWitness.2
  change outwardYZCanonicalRepairRightFineWitness.1 ∈
    slabFusionWitnessAssignmentsOn 1 5
      outwardYZCanonicalRepairSwitchRightPhysical
      (boundaryCompleteSlabLinks 5) at h
  exact h

/-- Total all-valence selector with exactly two degree-five overrides. -/
def outwardYZCanonicalRepairTargetForData :
    (degree : Nat) →
    (D : SlabPhysicalPairRecouplingData 5 degree) →
    D.leftPhysical = outwardYZCanonicalRepairSwitchLeftPhysical →
    D.rightPhysical = outwardYZCanonicalRepairSwitchRightPhysical →
    (source : (slabPhysicalPairRecouplingKernelPackage degree D).Source) →
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
      by_cases hspatial :
          D.link = outwardYZCanonicalRepairSwitchSpatialPivot
      · have hdata : D =
            outwardYZCanonicalRepairSpatialPivotRecouplingData := by
          cases D with
          | mk leftPhysical rightPhysical link degree_eq =>
              dsimp at hleft hright hspatial
              cases hleft
              cases hright
              cases hspatial
              rfl
        rw [hdata]
        exact outwardYZCanonicalRepairSpatialTarget
      · by_cases htemporal :
            D.link = outwardYZCanonicalRepairSwitchTemporalPivot
        · have hdata : D =
              outwardYZCanonicalRepairTemporalPivotRecouplingData := by
            cases D with
            | mk leftPhysical rightPhysical link degree_eq =>
                dsimp at hleft hright htemporal
                cases hleft
                cases hright
                cases htemporal
                rfl
          rw [hdata]
          exact outwardYZCanonicalRepairTemporalTarget
        · exact slabPhysicalPairRecouplingFirstTarget 5 D source
  | 6, D, _, _, source =>
      slabPhysicalPairRecouplingFirstTarget 6 D source
  | degree + 7, D, _, _, _ => False.elim (by
      have hdegree := D.degree_le_six
      omega)

def outwardYZCanonicalRepairTargetAssignmentFrom :
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) →
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchRightPhysical linked)
  | [] => ()
  | linked :: rest => by
      let localData := slabPhysicalPairRecouplingDataAtLink 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchRightPhysical linked
      let anchor := slabPhysicalPairRecouplingWitnessDataAtLink 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchRightPhysical
        outwardYZCanonicalRepairLeftFineWitness.1
        outwardYZCanonicalRepairRightFineWitness.1
        outwardYZCanonicalRepairSwitchLeftAssignment_mem
        outwardYZCanonicalRepairSwitchRightAssignment_mem linked
      let source := slabPhysicalPairRecouplingProductionSource
        (slabIncidentPlaqIds 5 linked.1).length localData anchor
      refine (by
        unfold slabPhysicalPairRecouplingPackageAtLink
        exact outwardYZCanonicalRepairTargetForData
          (slabIncidentPlaqIds 5 linked.1).length
          localData rfl rfl source,
        outwardYZCanonicalRepairTargetAssignmentFrom rest)

theorem outwardYZCanonicalRepairTargetAssignmentFrom_mem :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
    outwardYZCanonicalRepairTargetAssignmentFrom linkedList ∈
      finiteBistochasticTargetAssignments
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            outwardYZCanonicalRepairSwitchLeftPhysical
            outwardYZCanonicalRepairSwitchRightPhysical linked)
  | [] => List.mem_cons_self
  | linked :: rest => by
      apply List.mem_flatMap.mpr
      refine ⟨(outwardYZCanonicalRepairTargetAssignmentFrom
        (linked :: rest)).1, ?_, ?_⟩
      · unfold slabPhysicalPairRecouplingPackageAtLink
        exact slabPhysicalPairRecouplingTarget_mem
          (slabIncidentPlaqIds 5 linked.1).length
          (slabPhysicalPairRecouplingDataAtLink 5
            outwardYZCanonicalRepairSwitchLeftPhysical
            outwardYZCanonicalRepairSwitchRightPhysical linked)
          (outwardYZCanonicalRepairTargetAssignmentFrom
            (linked :: rest)).1
      · apply List.mem_map.mpr
        exact ⟨outwardYZCanonicalRepairTargetAssignmentFrom rest,
          outwardYZCanonicalRepairTargetAssignmentFrom_mem rest, rfl⟩

theorem outwardYZCanonicalRepairTargetExistsFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    ∃ target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            outwardYZCanonicalRepairSwitchLeftPhysical
            outwardYZCanonicalRepairSwitchRightPhysical linked),
      target ∈ finiteBistochasticTargetAssignments
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            outwardYZCanonicalRepairSwitchLeftPhysical
            outwardYZCanonicalRepairSwitchRightPhysical linked) :=
  ⟨outwardYZCanonicalRepairTargetAssignmentFrom linkedList,
    outwardYZCanonicalRepairTargetAssignmentFrom_mem linkedList⟩

theorem outwardYZCanonicalRepairTargetForSpatialPivot_eq
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairSpatialPivotRecouplingData).Source) :
    outwardYZCanonicalRepairTargetForData 5
      outwardYZCanonicalRepairSpatialPivotRecouplingData rfl rfl source =
        outwardYZCanonicalRepairSpatialTarget := by
  simp [outwardYZCanonicalRepairTargetForData,
    outwardYZCanonicalRepairSpatialPivotRecouplingData]

theorem outwardYZCanonicalRepairTargetForTemporalPivot_eq
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairTemporalPivotRecouplingData).Source) :
    outwardYZCanonicalRepairTargetForData 5
      outwardYZCanonicalRepairTemporalPivotRecouplingData rfl rfl source =
        outwardYZCanonicalRepairTemporalTarget := by
  have hne : outwardYZCanonicalRepairSwitchTemporalPivot ≠
      outwardYZCanonicalRepairSwitchSpatialPivot := by
    decide
  simp [outwardYZCanonicalRepairTargetForData,
    outwardYZCanonicalRepairTemporalPivotRecouplingData, hne]

#print axioms outwardYZCanonicalRepairSwitchLeftAssignment_mem
#print axioms outwardYZCanonicalRepairSwitchRightAssignment_mem
#print axioms outwardYZCanonicalRepairTargetForData
#print axioms outwardYZCanonicalRepairTargetAssignmentFrom_mem
#print axioms outwardYZCanonicalRepairTargetExistsFrom
#print axioms outwardYZCanonicalRepairTargetForSpatialPivot_eq
#print axioms outwardYZCanonicalRepairTargetForTemporalPivot_eq

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetAssignment
