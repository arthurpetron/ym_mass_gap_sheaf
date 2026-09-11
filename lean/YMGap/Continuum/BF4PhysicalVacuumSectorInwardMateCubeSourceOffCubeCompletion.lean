/-
# Complete a certified cube source from only the off-cube fibers

The earlier completion map accepts a full production background and overwrites
its twelve cube entries.  That is appropriate for existence, but enumerating
such backgrounds would retain choices that are subsequently discarded and
would therefore overcount the source fiber.

This file removes that redundancy at the type boundary.  It filters the
complete extent-one slab links to the literal complement of the twelve cube
links, enumerates the production fusion assignments only on that complement,
and fills a complete presented assignment piecewise: certified root-first data
on cube links and the enumerated production data off the cube.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. The literal off-cube link complement -/

/-- The complete extent-one slab links with exactly the twelve cube-boundary
links removed. -/
def cubeInwardMateOffCubeSlabLinks : List SlabLink :=
  (boundaryCompleteSlabLinks 1).filter fun link =>
    decide (link ∉ coarseCubeBoundaryLinks)

theorem mem_cubeInwardMateOffCubeSlabLinks_iff (link : SlabLink) :
    link ∈ cubeInwardMateOffCubeSlabLinks ↔
      link ∈ boundaryCompleteSlabLinks 1 ∧
        link ∉ coarseCubeBoundaryLinks := by
  simp [cubeInwardMateOffCubeSlabLinks]

/-- The cube-incidence lookup fails exactly off the mapped twelve-link cube
boundary. -/
theorem cubeProductionIncidenceForLink?_eq_none_iff (link : SlabLink) :
    cubeProductionIncidenceForLink? link = none ↔
      link ∉ coarseCubeBoundaryLinks := by
  constructor
  · intro hnone hmem
    have hnoneDirect : cubeProductionIncidences.find?
        (cubeProductionIncidenceHasLink link) = none := by
      simpa [cubeProductionIncidenceForLink?] using hnone
    rw [← cubeProductionIncidences_map_link] at hmem
    obtain ⟨incidence, hincidence, hlink⟩ := List.mem_map.mp hmem
    have hfalse :=
      (List.find?_eq_none.mp hnoneDirect) incidence hincidence
    simp [cubeProductionIncidenceHasLink, hlink] at hfalse
  · intro hnot
    unfold cubeProductionIncidenceForLink?
    cases hfind : cubeProductionIncidences.find?
        (cubeProductionIncidenceHasLink link) with
    | none => rfl
    | some incidence =>
        have hincidence : incidence ∈ cubeProductionIncidences :=
          List.mem_of_find?_eq_some hfind
        have htest := List.find?_some hfind
        have hlink : incidence.link = link :=
          of_decide_eq_true (by
            simpa [cubeProductionIncidenceHasLink] using htest)
        exact False.elim (hnot (by
          rw [← cubeProductionIncidences_map_link]
          exact List.mem_map.mpr ⟨incidence, hincidence, hlink⟩))

/-- An attached off-cube link, viewed in the complete slab-link carrier. -/
def cubeInwardMateOffCubeSlabLinkToComplete
    (linked : {link // link ∈ cubeInwardMateOffCubeSlabLinks}) :
    {link // link ∈ boundaryCompleteSlabLinks 1} :=
  ⟨linked.1,
    (mem_cubeInwardMateOffCubeSlabLinks_iff linked.1).mp linked.2 |>.1⟩

/-! ## 2. Enumerate only the production fibers that survive completion -/

/-- The Cartesian production assignments on precisely the off-cube links. -/
def cubeInwardMateOffCubeFusionWitnessAssignments
    (K : Nat) (physical : EdgeLabelling) :
    List SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentsOn K 1 physical
    cubeInwardMateOffCubeSlabLinks

theorem cubeInwardMateOffCubeFusionWitnessAssignments_length
    (K : Nat) (physical : EdgeLabelling) :
    (cubeInwardMateOffCubeFusionWitnessAssignments K physical).length =
      natListProduct
        (slabExplicitLinkMultiplicity K 1 physical)
        cubeInwardMateOffCubeSlabLinks := by
  exact slabFusionWitnessAssignmentsOn_length
    K 1 physical cubeInwardMateOffCubeSlabLinks

theorem cubeInwardMateOffCubeFusionWitnessAssignments_nodup
    (K : Nat) (physical : EdgeLabelling) :
    (cubeInwardMateOffCubeFusionWitnessAssignments K physical).Nodup := by
  exact slabFusionWitnessAssignmentsOn_nodup
    K 1 physical cubeInwardMateOffCubeSlabLinks

/-! ## 3. No-overcount completion of the presented source -/

/-- Fill a complete presented slab source from certified root-first cube data
and an accepted production assignment only on the off-cube complement. -/
def completePresentedSlabSourceOfCertifiedCubeAndOffAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (certified : CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded)
    (offAssignment : SlabFusionWitnessAssignment)
    (hoffAssignment : offAssignment ∈
      cubeInwardMateOffCubeFusionWitnessAssignments K physical) :
    PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1) :=
  fun linked =>
    match hfind : cubeProductionIncidenceForLink? linked.1 with
    | some incidence =>
        have hfindDirect : cubeProductionIncidences.find?
            (cubeProductionIncidenceHasLink linked.1) = some incidence := by
          simpa [cubeProductionIncidenceForLink?] using hfind
        let cubeLinked : CubeProductionIncidenceMember :=
          ⟨incidence, List.mem_of_find?_eq_some hfindDirect⟩
        have htest := List.find?_some hfindDirect
        have hlink : incidence.link = linked.1 :=
          of_decide_eq_true (by
            simpa [cubeProductionIncidenceHasLink] using htest)
        hlink ▸
          cubeInwardMatePresentedSourceAssignmentOfCertified
            K physical hK hbounded certified cubeLinked
    | none =>
        { order := productionSlabLinkFaceOrder 1 linked.1
          auxiliary := slabFusionWitnessAssignmentAt
            linked.1 offAssignment
          auxiliary_mem := by
            have hoff : linked.1 ∈ cubeInwardMateOffCubeSlabLinks :=
              (mem_cubeInwardMateOffCubeSlabLinks_iff linked.1).mpr
                ⟨linked.2,
                  (cubeProductionIncidenceForLink?_eq_none_iff
                    linked.1).mp hfind⟩
            simpa [cubeInwardMateOffCubeFusionWitnessAssignments,
              orderedSlabLinkFusionWitnesses,
              productionSlabLinkFaceOrder, slabLinkFusionWitnesses,
              slabLinkExternalSpins, fusionWitnessesForSpins] using
                (slabFusionWitnessAssignmentAt_mem_local
                  K 1 physical cubeInwardMateOffCubeSlabLinks
                  offAssignment hoffAssignment linked.1 hoff) }

/-- At every cube incidence, no-overcount completion uses exactly the
certified root-first presentation. -/
theorem completePresentedSlabSourceOfCertifiedCubeAndOffAssignment_at_cube
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (certified : CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded)
    (offAssignment : SlabFusionWitnessAssignment)
    (hoffAssignment : offAssignment ∈
      cubeInwardMateOffCubeFusionWitnessAssignments K physical)
    (linked : CubeProductionIncidenceMember) :
    completePresentedSlabSourceOfCertifiedCubeAndOffAssignment
        K physical hK hbounded certified offAssignment hoffAssignment
        (cubeProductionIncidenceSlabLink linked) =
      cubeInwardMatePresentedSourceAssignmentOfCertified
        K physical hK hbounded certified linked := by
  unfold completePresentedSlabSourceOfCertifiedCubeAndOffAssignment
    cubeProductionIncidenceSlabLink
  split
  · rename_i incidence hfound
    have hexact := cubeProductionIncidenceForLink?_eq_some linked
    rw [hfound] at hexact
    have heq : incidence = linked.1 := Option.some.inj hexact
    subst incidence
    rfl
  · rename_i hnone
    have hsome := cubeProductionIncidenceForLink?_eq_some linked
    rw [hnone] at hsome
    cases hsome

/-- At any complete slab link outside the cube, no-overcount completion
retains exactly the production auxiliary chosen in the complement
assignment. -/
theorem completePresentedSlabSourceOfCertifiedCubeAndOffAssignment_at_not_cube
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (certified : CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded)
    (offAssignment : SlabFusionWitnessAssignment)
    (hoffAssignment : offAssignment ∈
      cubeInwardMateOffCubeFusionWitnessAssignments K physical)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1})
    (hnot : linked.1 ∉ coarseCubeBoundaryLinks) :
    (completePresentedSlabSourceOfCertifiedCubeAndOffAssignment
        K physical hK hbounded certified offAssignment hoffAssignment
        linked).auxiliary =
      slabFusionWitnessAssignmentAt linked.1 offAssignment := by
  unfold completePresentedSlabSourceOfCertifiedCubeAndOffAssignment
  split
  · rename_i incidence hfound
    have hnone :=
      (cubeProductionIncidenceForLink?_eq_none_iff linked.1).mpr hnot
    rw [hfound] at hnone
    cases hnone
  · rfl

/-- Specialize the no-overcount completion to the certified data retained by
the enumerated first-stretched branch. -/
def completePresentedSlabSourceOfFirstStretchedAndOffAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (offAssignment : SlabFusionWitnessAssignment)
    (hoffAssignment : offAssignment ∈
      cubeInwardMateOffCubeFusionWitnessAssignments K physical) :
    PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1) :=
  completePresentedSlabSourceOfCertifiedCubeAndOffAssignment
    K physical hK hbounded stretched.certified
      offAssignment hoffAssignment

#print axioms mem_cubeInwardMateOffCubeSlabLinks_iff
#print axioms cubeProductionIncidenceForLink?_eq_none_iff
#print axioms cubeInwardMateOffCubeFusionWitnessAssignments_length
#print axioms cubeInwardMateOffCubeFusionWitnessAssignments_nodup
#print axioms completePresentedSlabSourceOfCertifiedCubeAndOffAssignment
#print axioms completePresentedSlabSourceOfCertifiedCubeAndOffAssignment_at_cube
#print axioms completePresentedSlabSourceOfCertifiedCubeAndOffAssignment_at_not_cube
#print axioms completePresentedSlabSourceOfFirstStretchedAndOffAssignment

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
