/-
# One fixed presented order for every complete-source lowered target

The nonredundant complete first-stretched source family uses the same local
face order at every displayed slab link: the certified root-first order on
the twelve cube links and the production order off the cube.  The deterministic
two-root peel changes only physical and auxiliary labels, so every lowered
target retains that same order profile.

This file isolates the fixed-order invariant needed to place all realized
lowered targets in one explicit Cartesian target carrier.  It does not yet
construct that carrier or compare its weight with the physical partition.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullInjectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The common complete-slab order profile -/

/-- Root-first on the twelve cube links and production-ordered everywhere
else.  The computable incidence lookup makes this one dependent order family
on the complete extent-one slab-link carrier. -/
def cubeInwardMateCompleteSourceFaceOrder
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    SlabLinkFaceOrder 1 linked.1 :=
  match hfind : cubeProductionIncidenceForLink? linked.1 with
  | none => productionSlabLinkFaceOrder 1 linked.1
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
      hlink ▸ cubeInwardMateSourceFaceOrder cubeLinked

/-- On a recorded cube incidence, the common profile is its literal
root-first order. -/
theorem cubeInwardMateCompleteSourceFaceOrder_at_cube
    (linked : CubeProductionIncidenceMember) :
    cubeInwardMateCompleteSourceFaceOrder
        (cubeProductionIncidenceSlabLink linked) =
      cubeInwardMateSourceFaceOrder linked := by
  unfold cubeInwardMateCompleteSourceFaceOrder
    cubeProductionIncidenceSlabLink
  split
  · rename_i hnone
    have hsome := cubeProductionIncidenceForLink?_eq_some linked
    rw [hnone] at hsome
    contradiction
  · rename_i incidence hfound
    have hexact := cubeProductionIncidenceForLink?_eq_some linked
    rw [hfound] at hexact
    have heq : incidence = linked.1 := Option.some.inj hexact
    subst incidence
    rfl

/-- Away from the twelve cube incidences, the common profile is the ordinary
production order. -/
theorem cubeInwardMateCompleteSourceFaceOrder_at_not_cube
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1})
    (hnot : linked.1 ∉ coarseCubeBoundaryLinks) :
    cubeInwardMateCompleteSourceFaceOrder linked =
      productionSlabLinkFaceOrder 1 linked.1 := by
  unfold cubeInwardMateCompleteSourceFaceOrder
  split
  · rfl
  · rename_i incidence hsome
    have hnone :=
      (cubeProductionIncidenceForLink?_eq_none_iff linked.1).mpr hnot
    rw [hsome] at hnone
    contradiction

/-- The no-overcount completion retains production order off the cube. -/
theorem CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_order_at_not_cube
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1})
    (hnot : linked.1 ∉ coarseCubeBoundaryLinks) :
    (source.toPresented linked).order =
      productionSlabLinkFaceOrder 1 linked.1 := by
  unfold CubeInwardMateCertifiedFirstStretchedFullSource.toPresented
    completePresentedSlabSourceOfFirstStretchedAndOffAssignment
    completePresentedSlabSourceOfCertifiedCubeAndOffAssignment
  split
  · rename_i incidence hsome
    have hnone :=
      (cubeProductionIncidenceForLink?_eq_none_iff linked.1).mpr hnot
    rw [hsome] at hnone
    contradiction
  · rfl

/-- Every nonredundant complete source has exactly the common order profile. -/
theorem CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_order
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (source.toPresented linked).order =
      cubeInwardMateCompleteSourceFaceOrder linked := by
  cases hfind : cubeProductionIncidenceForLink? linked.1 with
  | none =>
      have hnot :=
        (cubeProductionIncidenceForLink?_eq_none_iff linked.1).mp hfind
      exact
        (CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_order_at_not_cube
          source linked hnot).trans
        (cubeInwardMateCompleteSourceFaceOrder_at_not_cube
          linked hnot).symm
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
      have hlinked : cubeProductionIncidenceSlabLink cubeLinked = linked :=
        Subtype.ext hlink
      rw [← hlinked]
      rw [cubeInwardMateCompleteSourceFaceOrder_at_cube]
      calc
        (source.toPresented
            (cubeProductionIncidenceSlabLink cubeLinked)).order =
            (cubeInwardMatePresentedSourceAssignmentOfCertified
              K physical hK hbounded source.1.certified cubeLinked).order :=
          congrArg (fun item => item.order)
            (CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_cube
              source cubeLinked)
        _ = cubeInwardMateSourceFaceOrder cubeLinked := by
          unfold cubeInwardMatePresentedSourceAssignmentOfCertified
            cubeInwardMatePresentedSourceAssignment
          rfl

/-! ## 2. The peel preserves the common order -/

/-- Any defensive cube completion preserves a common order profile already
carried by its background. -/
theorem completePresentedSlabSourceOfCertifiedCube_order
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (certified : CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1))
    (hbackground : ∀ linked,
      (background linked).order = cubeInwardMateCompleteSourceFaceOrder linked)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded certified background linked).order =
      cubeInwardMateCompleteSourceFaceOrder linked := by
  cases hfind : cubeProductionIncidenceForLink? linked.1 with
  | none =>
      unfold completePresentedSlabSourceOfCertifiedCube
      split
      · exact hbackground linked
      · rename_i incidence hsome
        rw [hfind] at hsome
        contradiction
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
      have hlinked : cubeProductionIncidenceSlabLink cubeLinked = linked :=
        Subtype.ext hlink
      rw [← hlinked]
      rw [cubeInwardMateCompleteSourceFaceOrder_at_cube]
      calc
        (completePresentedSlabSourceOfCertifiedCube
            K physical hK hbounded certified background
            (cubeProductionIncidenceSlabLink cubeLinked)).order =
            (cubeInwardMatePresentedSourceAssignmentOfCertified
              K physical hK hbounded certified cubeLinked).order :=
          congrArg (fun item => item.order)
            (completePresentedSlabSourceOfCertifiedCube_at_cube
              K physical hK hbounded certified background cubeLinked)
        _ = cubeInwardMateSourceFaceOrder cubeLinked := by
          unfold cubeInwardMatePresentedSourceAssignmentOfCertified
            cubeInwardMatePresentedSourceAssignment
          rfl

/-- Reapplying the defensive cube completion to a complete source retains the
same common order profile. -/
theorem completePresentedSlabSourceOfCertifiedCube_on_fullSource_order
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded source.1.certified source.toPresented
        linked).order = cubeInwardMateCompleteSourceFaceOrder linked := by
  exact completePresentedSlabSourceOfCertifiedCube_order
    source.1.certified source.toPresented
    (CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_order source)
    linked

/-- **Fixed-order lowered-target invariant.**  Every enumerated source's
adaptive lowered target lies in the same dependent order family. -/
theorem EnumeratedCubeInwardMateFullSource.adaptiveInverseData_lowerAssignment_order
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (entry.adaptiveInverseData.lowerAssignment linked).order =
      cubeInwardMateCompleteSourceFaceOrder linked := by
  change
    ((certifiedStretchedComponentUnionSelection
        entry.source.1 entry.source.toPresented).loweredWitnessAt linked).order = _
  exact completePresentedSlabSourceOfCertifiedCube_on_fullSource_order
    entry.source linked

#print axioms cubeInwardMateCompleteSourceFaceOrder
#print axioms cubeInwardMateCompleteSourceFaceOrder_at_cube
#print axioms cubeInwardMateCompleteSourceFaceOrder_at_not_cube
#print axioms CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_order_at_not_cube
#print axioms CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_order
#print axioms completePresentedSlabSourceOfCertifiedCube_order
#print axioms completePresentedSlabSourceOfCertifiedCube_on_fullSource_order
#print axioms EnumeratedCubeInwardMateFullSource.adaptiveInverseData_lowerAssignment_order

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder
