/-
# Complete the certified cube source to a presented slab assignment

A classified source now reconstructs accepted root-first witnesses on the
twelve cube-boundary links.  The global strand graph, however, expects one
presented witness at every displayed slab link.  Given any accepted complete
background for the same physical field, this file replaces exactly the cube
entries by the certified source witnesses and leaves every other entry intact.

The replacement is driven by a computable lookup in the literal twelve-entry
incidence table.  Duplicate-freeness of the mapped link list proves that lookup
returns the unique recorded incidence, so every overwritten entry is exactly
the intended dependent cube witness.

The background remains an explicit input: this theorem does not claim that an
arbitrary bounded physical labelling has a nonempty global intertwiner fiber.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. Unique computable lookup of a cube incidence by its link -/

def cubeProductionIncidenceHasLink
    (link : SlabLink) (incidence : CubeProductionIncidence) : Bool :=
  decide (incidence.link = link)

def cubeProductionIncidenceForLink? (link : SlabLink) :
    Option CubeProductionIncidence :=
  cubeProductionIncidences.find? (cubeProductionIncidenceHasLink link)

private theorem injectiveOn_of_map_nodup
    {A B : Type} [DecidableEq A] [DecidableEq B]
    (map : A → B) :
    ∀ (items : List A), (items.map map).Nodup →
      ∀ left, left ∈ items →
      ∀ right, right ∈ items →
        map left = map right → left = right
  | [], _, _, hleft, _, _, _ => False.elim (List.not_mem_nil hleft)
  | head :: tail, hnodup, left, hleft, right, hright, heq => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hleft with hleftHead | hleftTail
      · subst left
        rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · exact hrightHead.symm
        · exact False.elim (hparts.1 (by
            rw [heq]
            exact List.mem_map.mpr ⟨right, hrightTail, rfl⟩))
      · rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · subst right
          exact False.elim (hparts.1 (by
            rw [← heq]
            exact List.mem_map.mpr ⟨left, hleftTail, rfl⟩))
        · exact injectiveOn_of_map_nodup map tail hparts.2
            left hleftTail right hrightTail heq

theorem cubeProductionIncidence_eq_of_link_eq
    {left right : CubeProductionIncidence}
    (hleft : left ∈ cubeProductionIncidences)
    (hright : right ∈ cubeProductionIncidences)
    (heq : left.link = right.link) :
    left = right := by
  apply injectiveOn_of_map_nodup CubeProductionIncidence.link
    cubeProductionIncidences
  · rw [cubeProductionIncidences_map_link]
    exact coarseCubeBoundaryLinks_nodup
  · exact hleft
  · exact hright
  · exact heq

theorem cubeProductionIncidenceForLink?_eq_some
    (linked : CubeProductionIncidenceMember) :
    cubeProductionIncidenceForLink? linked.1.link = some linked.1 := by
  unfold cubeProductionIncidenceForLink?
  cases hfind : cubeProductionIncidences.find?
      (cubeProductionIncidenceHasLink linked.1.link) with
  | none =>
      have hfalse := (List.find?_eq_none.mp hfind) linked.1 linked.2
      simp [cubeProductionIncidenceHasLink] at hfalse
  | some found =>
      have hfoundMem : found ∈ cubeProductionIncidences :=
        List.mem_of_find?_eq_some hfind
      have hfoundTest := List.find?_some hfind
      have hfoundLink : found.link = linked.1.link :=
        of_decide_eq_true (by
          simpa [cubeProductionIncidenceHasLink] using hfoundTest)
      have hfoundEq : found = linked.1 :=
        cubeProductionIncidence_eq_of_link_eq
          hfoundMem linked.2 hfoundLink
      subst found
      rfl

/-- Every recorded cube link is one of the complete corrected-slab links at
extent one. -/
theorem cubeProductionIncidence_link_mem_boundaryCompleteSlabLinks
    (linked : CubeProductionIncidenceMember) :
    linked.1.link ∈ boundaryCompleteSlabLinks 1 := by
  have hincident :=
    (cubeProductionIncidence_numeric_exact linked.2).1
  obtain ⟨plaquette, hindexed, hedge⟩ :=
    mem_slabIncidentPlaqIds.mp hincident
  apply (mem_boundaryCompleteSlabLinks_iff 1 linked.1.link).mpr
  refine ⟨plaquette, ?_, hedge⟩
  have hmapped : plaquette ∈
      (enumerate (boundaryCompleteSlabPlaquettes 1)).map Prod.snd :=
    List.mem_map.mpr
      ⟨(centralLowerCubeFaceId linked.1.left, plaquette),
        hindexed, rfl⟩
  rw [enumerate_map_snd] at hmapped
  exact hmapped

def cubeProductionIncidenceSlabLink
    (linked : CubeProductionIncidenceMember) :
    {link // link ∈ boundaryCompleteSlabLinks 1} :=
  ⟨linked.1.link,
    cubeProductionIncidence_link_mem_boundaryCompleteSlabLinks linked⟩

/-! ## 2. Override precisely the twelve cube entries -/

/-- Complete a certified cube source using explicit accepted off-cube data
from a presented background.  At a cube link, the background entry is ignored
and the decoded certified source witness is used in its literal root-first
order. -/
def completePresentedSlabSourceOfCertifiedCube
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (certified : CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1) :=
  fun linked =>
    match hfind : cubeProductionIncidenceForLink? linked.1 with
    | none => background linked
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

/-- At every recorded cube incidence, the completed assignment is exactly the
certified root-first source presentation stored at that incidence. -/
theorem completePresentedSlabSourceOfCertifiedCube_at_cube
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (certified : CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1))
    (linked : CubeProductionIncidenceMember) :
    completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded certified background
        (cubeProductionIncidenceSlabLink linked) =
      cubeInwardMatePresentedSourceAssignmentOfCertified
        K physical hK hbounded certified linked := by
  unfold completePresentedSlabSourceOfCertifiedCube
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

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.cubeProductionIncidence_eq_of_link_eq
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.cubeProductionIncidenceForLink?_eq_some
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.cubeProductionIncidence_link_mem_boundaryCompleteSlabLinks
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.completePresentedSlabSourceOfCertifiedCube
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.completePresentedSlabSourceOfCertifiedCube_at_cube
