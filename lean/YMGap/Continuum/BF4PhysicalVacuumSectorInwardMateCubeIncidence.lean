/-
# Instantiating the inward mate on the twelve cube-boundary links

The corrected extent-one slab numbers the six faces of the central lower cube
by `[0, 1, 3, 9, 19, 39]`.  This file identifies those numbers with the six
geometric `CubeFaceIndex` values and compiles the existing twelve-entry cube
incidence table into exact numerical incidence facts.

At every recorded boundary link, the two recorded cube-face IDs occur in the
production incident list, are distinct, and exhaust all selected cube-face IDs
in that list.  Hence the global six-face even inward mate changes exactly the
two exposed incident coordinates.  The constructive incident-order compiler
then gives the actual corrected-slab link-multiplicity inequality with one
explicit stretched continuation.

This is still a local statement.  It does not reroute the twelve stretched
continuations through complete strand components or prove a transition floor,
Poincare inequality, spectral gap, continuum limit, or Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4CentralLowerCubePositiveRow
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateIncidentOrder
import YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
import YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionReordering
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateIncidentOrder
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Numerical realization of the six geometric faces -/

/-- Corrected extent-one slab ID of each central lower cube face. -/
def centralLowerCubeFaceId : CubeFaceIndex → Nat
  | .bottomXY => 0
  | .topXY => 9
  | .frontXZ => 1
  | .backXZ => 19
  | .leftYZ => 3
  | .rightYZ => 39

theorem centralLowerCubeFaceId_mem (face : CubeFaceIndex) :
    centralLowerCubeFaceId face ∈ centralLowerCubeFaceIds := by
  cases face <;> simp [centralLowerCubeFaceId, centralLowerCubeFaceIds]

theorem centralLowerCubeFaceId_injective
    {left right : CubeFaceIndex}
    (heq : centralLowerCubeFaceId left = centralLowerCubeFaceId right) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [centralLowerCubeFaceId]

/-- The numerical ID really decodes to the corresponding geometric face. -/
theorem slabPlaquetteAt_one_centralLowerCubeFaceId
    (face : CubeFaceIndex) :
    slabPlaquetteAt 1 (centralLowerCubeFaceId face) = cubeFace face := by
  cases face <;> decide

/-! ## 2. Exact two-of-six incidence classification -/

/-- The existing twelve-entry geometric table is also exact at the numerical
corrected-slab level.  Its two selected IDs occur, they are distinct, and any
selected central-cube ID incident on the link is one of those two.  The last
clause is the explicit exclusion of the other four cube faces. -/
theorem cubeProductionIncidence_numeric_exact
    {incidence : CubeProductionIncidence}
    (hincidence : incidence ∈ cubeProductionIncidences) :
    centralLowerCubeFaceId incidence.left ∈
        slabIncidentPlaqIds 1 incidence.link ∧
      centralLowerCubeFaceId incidence.right ∈
        slabIncidentPlaqIds 1 incidence.link ∧
      centralLowerCubeFaceId incidence.left ≠
        centralLowerCubeFaceId incidence.right ∧
      ∀ faceId,
        faceId ∈ slabIncidentPlaqIds 1 incidence.link →
        faceId ∈ centralLowerCubeFaceIds →
        faceId = centralLowerCubeFaceId incidence.left ∨
          faceId = centralLowerCubeFaceId incidence.right := by
  simp only [cubeProductionIncidences, List.mem_cons,
    List.not_mem_nil, or_false] at hincidence
  rcases hincidence with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-! ## 3. The global six-face mate restricts to the local two-face mate -/

/-- Apply the even inward mate to all six central lower cube faces and leave
every other corrected-slab coordinate unchanged. -/
def centralLowerCubeEvenInwardMatePhysical
    (physical : EdgeLabelling) : EdgeLabelling :=
  fun faceId =>
    if faceId ∈ centralLowerCubeFaceIds then
      evenInwardMateLabel (physical faceId)
    else physical faceId

theorem centralLowerCubeEvenInwardMatePhysical_on_cube
    (physical : EdgeLabelling) {faceId : Nat}
    (hface : faceId ∈ centralLowerCubeFaceIds) :
    centralLowerCubeEvenInwardMatePhysical physical faceId =
      evenInwardMateLabel (physical faceId) := by
  simp [centralLowerCubeEvenInwardMatePhysical, hface]

theorem centralLowerCubeEvenInwardMatePhysical_off_cube
    (physical : EdgeLabelling) {faceId : Nat}
    (hface : faceId ∉ centralLowerCubeFaceIds) :
    centralLowerCubeEvenInwardMatePhysical physical faceId =
      physical faceId := by
  simp [centralLowerCubeEvenInwardMatePhysical, hface]

/-- At a recorded cube-boundary link, the source incident word and the global
six-face mate word admit the same explicit residual word after exposing the
two incident cube spins. -/
def slabIncidentPhysicalSpinsCentralCubeEvenInwardMatePermutations
    (incidence : CubeProductionIncidence)
    (hincidence : incidence ∈ cubeProductionIncidences)
    (physical : EdgeLabelling) :
    Σ' rest : List Nat,
      ((slabIncidentPlaqIds 1 incidence.link).map physical).Perm
        (physical (centralLowerCubeFaceId incidence.left) ::
          physical (centralLowerCubeFaceId incidence.right) :: rest) ∧
      ((slabIncidentPlaqIds 1 incidence.link).map
          (centralLowerCubeEvenInwardMatePhysical physical)).Perm
        (evenInwardMateLabel
            (physical (centralLowerCubeFaceId incidence.left)) ::
          evenInwardMateLabel
            (physical (centralLowerCubeFaceId incidence.right)) :: rest) := by
  have hgeometry := cubeProductionIncidence_numeric_exact hincidence
  let order := twoHeadPermOfMem
    hgeometry.1 hgeometry.2.1 hgeometry.2.2.1
  let restIds := order.1
  have hids := order.2
  have hexcludes := two_head_perm_rest_excludes
    (slabIncidentPlaqIds_nodup 1 incidence.link) hids
  have hrestMate :
      restIds.map (centralLowerCubeEvenInwardMatePhysical physical) =
        restIds.map physical := by
    apply List.map_congr_left
    intro faceId hface
    apply centralLowerCubeEvenInwardMatePhysical_off_cube
    intro hselected
    have hpair := hgeometry.2.2.2 faceId
      (hids.mem_iff.mpr (by
        simp only [List.mem_cons]
        exact Or.inr (Or.inr hface))) hselected
    rcases hpair with hleft | hright
    · exact hexcludes.1 (hleft ▸ hface)
    · exact hexcludes.2 (hright ▸ hface)
  refine ⟨restIds.map physical, ?_, ?_⟩
  · simpa only [List.map_cons] using hids.map physical
  · have hmate := hids.map
      (centralLowerCubeEvenInwardMatePhysical physical)
    dsimp [restIds] at hrestMate ⊢
    simpa only [List.map_cons,
      centralLowerCubeEvenInwardMatePhysical_on_cube physical
        (centralLowerCubeFaceId_mem incidence.left),
      centralLowerCubeEvenInwardMatePhysical_on_cube physical
        (centralLowerCubeFaceId_mem incidence.right),
      hrestMate] using hmate

/-! ## 4. Corrected-slab production multiplicity -/

/-- **Twelve-link cube compiler.**  At every recorded cube-boundary link, the
actual corrected-slab source multiplicity is bounded by the global six-face
mate multiplicity plus one explicit stretched continuation. -/
def slabExplicitLinkMultiplicityCentralCubeEvenInwardMateLeAddStretched
    (K : Nat) (incidence : CubeProductionIncidence)
    (hincidence : incidence ∈ cubeProductionIncidences)
    (physical : EdgeLabelling)
    (hK : 1 ≤ K)
    (hbounded : SlabFaceLabellingBounded K 1 physical) :
    Σ' rest : List Nat,
      ((slabIncidentPlaqIds 1 incidence.link).map physical).Perm
        (physical (centralLowerCubeFaceId incidence.left) ::
          physical (centralLowerCubeFaceId incidence.right) :: rest) ∧
      ((slabIncidentPlaqIds 1 incidence.link).map
          (centralLowerCubeEvenInwardMatePhysical physical)).Perm
        (evenInwardMateLabel
            (physical (centralLowerCubeFaceId incidence.left)) ::
          evenInwardMateLabel
            (physical (centralLowerCubeFaceId incidence.right)) :: rest) ∧
      slabExplicitLinkMultiplicity K 1 physical incidence.link ≤
        slabExplicitLinkMultiplicity K 1
            (centralLowerCubeEvenInwardMatePhysical physical)
            incidence.link +
          explicitValenceMultiplicity (linkAuxiliaryCutoff K)
            ((physical (centralLowerCubeFaceId incidence.left) +
              physical (centralLowerCubeFaceId incidence.right)) :: rest).length
            (externalSpinsOfList
              ((physical (centralLowerCubeFaceId incidence.left) +
                physical (centralLowerCubeFaceId incidence.right)) ::
                rest)) := by
  let certificate :=
    slabIncidentPhysicalSpinsCentralCubeEvenInwardMatePermutations
      incidence hincidence physical
  let rest := certificate.1
  have hsource := certificate.2.1
  have hmate := certificate.2.2
  have hlength :
      (physical (centralLowerCubeFaceId incidence.left) ::
        physical (centralLowerCubeFaceId incidence.right) :: rest).length ≤ 6 := by
    rw [← hsource.length_eq]
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 incidence.link
  have hsourceBounded : SpinsBounded K
      ((slabIncidentPlaqIds 1 incidence.link).map physical) :=
    slabIncidentSpins_bounded hbounded incidence.link
  have hfrontBounded : SpinsBounded K
      (physical (centralLowerCubeFaceId incidence.left) ::
        physical (centralLowerCubeFaceId incidence.right) :: rest) :=
    spinsBounded_of_perm hsource hsourceBounded
  refine ⟨rest, hsource, hmate, ?_⟩
  unfold slabExplicitLinkMultiplicity
  exact explicitValenceMultiplicity_physical_inwardMate_of_permutations
    K
    (physical (centralLowerCubeFaceId incidence.left))
    (physical (centralLowerCubeFaceId incidence.right)) rest
    ((slabIncidentPlaqIds 1 incidence.link).map physical)
    ((slabIncidentPlaqIds 1 incidence.link).map
      (centralLowerCubeEvenInwardMatePhysical physical))
    hK hlength hfrontBounded hsource hmate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence.cubeProductionIncidence_numeric_exact
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence.slabIncidentPhysicalSpinsCentralCubeEvenInwardMatePermutations
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence.slabExplicitLinkMultiplicityCentralCubeEvenInwardMateLeAddStretched
