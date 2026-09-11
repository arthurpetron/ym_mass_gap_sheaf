/-
# Exact cube/off-cube source multiplicity split

The source classifier enumerates root-first fusion data on the twelve cube
boundary links and ordinary production data on the complementary slab links.
This module proves that these two factors multiply to the complete extent-one
SU(2) link multiplicity.  It is the numeric conservation law required before
the classified all-target and first-stretched branches can be normalized to
the physical partition.

No weighted branch or success fraction is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetCongestion
import YMGap.Continuum.Z4CanonicalPolymerUniverse

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceMultiplicitySplit

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Generic finite product partition -/

private theorem natListProduct_bool_filter_split_local
    {A : Type} (value : A -> Nat) (keep : A -> Bool) : ∀ items : List A,
    natListProduct value items =
      natListProduct value (items.filter keep) *
        natListProduct value (items.filter fun item => !keep item)
  | [] => rfl
  | head :: tail => by
      have ih := natListProduct_bool_filter_split_local value keep tail
      cases hhead : keep head <;>
        simp [hhead, natListProduct, ih, Nat.mul_assoc, Nat.mul_left_comm]

/-! ## 2. The filtered cube links are exactly the incidence links -/

private theorem coarseCubeBoundaryLink_mem_complete
    {link : SlabLink} (hlink : link ∈ coarseCubeBoundaryLinks) :
    link ∈ boundaryCompleteSlabLinks 1 := by
  rw [← cubeProductionIncidences_map_link] at hlink
  obtain ⟨incidence, hincidence, hlinkEq⟩ := List.mem_map.mp hlink
  have hincidenceLink :
      incidence.link ∈ boundaryCompleteSlabLinks 1 := by
    exact cubeProductionIncidence_link_mem_boundaryCompleteSlabLinks
      (⟨incidence, hincidence⟩ : CubeProductionIncidenceMember)
  exact hlinkEq ▸ hincidenceLink

/-- Filtering the complete extent-one slab links by cube membership is a
permutation of the literal twelve-link cube boundary. -/
theorem boundaryCompleteSlabLinks_filter_cube_perm :
    ((boundaryCompleteSlabLinks 1).filter
      fun link => decide (link ∈ coarseCubeBoundaryLinks)).Perm
        coarseCubeBoundaryLinks := by
  apply perm_of_nodup_mem_iff
  · exact (boundaryCompleteSlabLinks_nodup 1).filter _
  · exact coarseCubeBoundaryLinks_nodup
  · intro link
    constructor
    · intro hlink
      exact of_decide_eq_true (List.mem_filter.mp hlink).2
    · intro hlink
      exact List.mem_filter.mpr
        ⟨coarseCubeBoundaryLink_mem_complete hlink,
          decide_eq_true hlink⟩

/-- The root-first cube product is exactly the ordinary multiplicity product
over the twelve literal cube-boundary links. -/
theorem cubeInwardMateSourceBoundaryProduct_eq_cubeLinkProduct
    (K : Nat) (physical : EdgeLabelling) :
    cubeInwardMateSourceBoundaryProduct K physical =
      natListProduct (slabExplicitLinkMultiplicity K 1 physical)
        coarseCubeBoundaryLinks := by
  unfold cubeInwardMateSourceBoundaryProduct
    cubeInwardMateSourceLinkMultiplicity
  rw [← natListProduct_map
    (slabExplicitLinkMultiplicity K 1 physical)
    (fun linked : CubeProductionIncidenceMember => linked.1.link)
    cubeProductionIncidences.attach]
  have hlinks :
      cubeProductionIncidences.attach.map
          (fun linked : CubeProductionIncidenceMember => linked.1.link) =
        coarseCubeBoundaryLinks := by
    calc
      cubeProductionIncidences.attach.map
          (fun linked : CubeProductionIncidenceMember => linked.1.link) =
        (cubeProductionIncidences.attach.map Subtype.val).map
          CubeProductionIncidence.link := by
            rw [List.map_map]
            apply List.map_congr_left
            intro linked _
            rfl
      _ = cubeProductionIncidences.map CubeProductionIncidence.link := by
            rw [List.attach_map_subtype_val]
      _ = coarseCubeBoundaryLinks := cubeProductionIncidences_map_link
  rw [hlinks]

/-- The complete slab multiplicity splits exactly into the classifier's cube
source product and the surviving off-cube production product. -/
theorem cubeInwardMateSourceBoundary_mul_offCube_eq_slabMultiplicity
    (K : Nat) (physical : EdgeLabelling) :
    cubeInwardMateSourceBoundaryProduct K physical *
        natListProduct (slabExplicitLinkMultiplicity K 1 physical)
          cubeInwardMateOffCubeSlabLinks =
      slabExplicitLinkMultiplicityProduct K 1 physical := by
  have hsplit := natListProduct_bool_filter_split_local
    (slabExplicitLinkMultiplicity K 1 physical)
    (fun link => decide (link ∈ coarseCubeBoundaryLinks))
    (boundaryCompleteSlabLinks 1)
  have hcubePerm := boundaryCompleteSlabLinks_filter_cube_perm
  have hcubeProduct := natListProduct_perm
    (slabExplicitLinkMultiplicity K 1 physical) hcubePerm
  unfold slabExplicitLinkMultiplicityProduct cubeInwardMateOffCubeSlabLinks
  rw [cubeInwardMateSourceBoundaryProduct_eq_cubeLinkProduct]
  calc
    natListProduct (slabExplicitLinkMultiplicity K 1 physical)
        coarseCubeBoundaryLinks *
        natListProduct (slabExplicitLinkMultiplicity K 1 physical)
          ((boundaryCompleteSlabLinks 1).filter
            fun link => decide (link ∉ coarseCubeBoundaryLinks)) =
      natListProduct (slabExplicitLinkMultiplicity K 1 physical)
          ((boundaryCompleteSlabLinks 1).filter
            fun link => decide (link ∈ coarseCubeBoundaryLinks)) *
        natListProduct (slabExplicitLinkMultiplicity K 1 physical)
          ((boundaryCompleteSlabLinks 1).filter
            fun link => decide (link ∉ coarseCubeBoundaryLinks)) := by
              rw [hcubeProduct]
    _ = natListProduct (slabExplicitLinkMultiplicity K 1 physical)
          (boundaryCompleteSlabLinks 1) := by
            rw [hsplit]
            simp only [decide_not]

#print axioms boundaryCompleteSlabLinks_filter_cube_perm
#print axioms cubeInwardMateSourceBoundaryProduct_eq_cubeLinkProduct
#print axioms cubeInwardMateSourceBoundary_mul_offCube_eq_slabMultiplicity

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceMultiplicitySplit
