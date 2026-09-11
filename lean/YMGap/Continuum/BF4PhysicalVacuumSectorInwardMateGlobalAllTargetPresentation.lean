/-
# Complete presentation of the global all-target physical state

Every successful global source already carries twelve certified target
witnesses on the central cube and an accepted production assignment on all
off-cube links.  This module joins those two pieces over the parity-flipped
physical target.  Cube links use the classified inward-mate witness; off-cube
links retain the source auxiliary, whose acceptance transports because the
complete incident physical spin word is unchanged there.

This is a literal accepted target assignment.  It does not yet compare source
and target weights, bound target-column congestion, or prove a posterior,
conditional-variance, Osterwalder--Schrader, or spectral inequality.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPresentation

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Join cube targets and the unchanged off-cube assignment -/

/-- The complete accepted presented assignment over the parity-flipped target
physical field carried by one successful global source. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    PresentedSlabFusionWitnessAssignment K 1
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
      (boundaryCompleteSlabLinks 1) :=
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
        hlink ▸ presentedMatedLinkWitnessOfCubeInwardMateTarget
          K source.physical cubeLinked (source.entry.1 cubeLinked)
    | none =>
        { order := productionSlabLinkFaceOrder 1 linked.1
          auxiliary := slabFusionWitnessAssignmentAt
            linked.1 source.entry.2.1
          auxiliary_mem := by
            have hnot : linked.1 ∉ coarseCubeBoundaryLinks :=
              (cubeProductionIncidenceForLink?_eq_none_iff linked.1).mp hfind
            have hoff : linked.1 ∈ cubeInwardMateOffCubeSlabLinks :=
              (mem_cubeInwardMateOffCubeSlabLinks_iff linked.1).mpr
                ⟨linked.2, hnot⟩
            have hsource := slabFusionWitnessAssignmentAt_mem_local
              K 1 source.physical cubeInwardMateOffCubeSlabLinks
              source.entry.2.1 source.entry.2.2 linked.1 hoff
            simpa [GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical,
              orderedSlabLinkFusionWitnesses,
              productionSlabLinkFaceOrder, slabLinkFusionWitnesses,
              slabLinkExternalSpins, fusionWitnessesForSpins,
              slabIncidentPhysicalSpins_centralCubeEvenInwardMate_eq_of_not_boundary
                source.physical hnot] using hsource }

/-! ## 2. Exact local lookup equations -/

/-- At a selected cube link, the complete target uses exactly the classified
inward-mate witness. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_at_cube
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (linked : CubeProductionIncidenceMember) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented source
        (cubeProductionIncidenceSlabLink linked) =
      presentedMatedLinkWitnessOfCubeInwardMateTarget
        K source.physical linked (source.entry.1 linked) := by
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
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

/-- Off the cube, the complete target retains exactly the source auxiliary. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_at_not_cube
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1})
    (hnot : linked.1 ∉ coarseCubeBoundaryLinks) :
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
      source linked).auxiliary =
      slabFusionWitnessAssignmentAt linked.1 source.entry.2.1 := by
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
  split
  · rename_i incidence hfound
    have hnone :=
      (cubeProductionIncidenceForLink?_eq_none_iff linked.1).mpr hnot
    rw [hfound] at hnone
    cases hnone
  · rfl

#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_at_cube
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_at_not_cube

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPresentation
