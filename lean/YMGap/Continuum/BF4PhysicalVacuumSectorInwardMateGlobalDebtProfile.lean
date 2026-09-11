/-
# The twelve-link stretched-debt profile of the BF4 inward mate

The local cube-incidence compiler returns one explicit residual word and one
stretched continuation at each of the twelve boundary links.  This file makes
those witnesses into a single observable finite profile indexed by the
attached production-incidence list.

First, geometric locality proves that the global six-face mate leaves every
link outside the cube boundary unchanged.  Second, the twelve local
inequalities multiply to one exact boundary-product inequality.  Its right
side is deliberately left as the product of `mate + stretchedDebt` factors:
the next module must expand and reroute those debts through closed strand
components.  No independent per-link absorption is assumed.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
import YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionReordering
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. Support and cutoff locality of the global mate -/

theorem centralLowerCubeEvenInwardMatePhysical_bounded
    {K : Nat} (hK : 1 ≤ K) {physical : EdgeLabelling}
    (hbounded : SlabFaceLabellingBounded K 1 physical) :
    SlabFaceLabellingBounded K 1
      (centralLowerCubeEvenInwardMatePhysical physical) := by
  intro faceId hphysical
  by_cases hcube : faceId ∈ centralLowerCubeFaceIds
  · rw [centralLowerCubeEvenInwardMatePhysical_on_cube physical hcube]
    exact evenInwardMateLabel_le_cutoff hK (hbounded faceId hphysical)
  · rw [centralLowerCubeEvenInwardMatePhysical_off_cube physical hcube]
    exact hbounded faceId hphysical

theorem slabPlaquetteAt_one_mem_unitCubeSurface_of_mem
    {faceId : Nat} (hface : faceId ∈ centralLowerCubeFaceIds) :
    slabPlaquetteAt 1 faceId ∈ unitCubeSurface := by
  simp only [centralLowerCubeFaceIds, List.mem_cons,
    List.not_mem_nil, or_false] at hface
  rcases hface with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem slabPlaquetteAt_eq_of_enumerate_local
    {faceId : Nat} {plaquette :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plaq}
    (hindexed : (faceId, plaquette) ∈
      enumerate (boundaryCompleteSlabPlaquettes 1)) :
    slabPlaquetteAt 1 faceId = plaquette := by
  unfold slabPlaquetteAt
  exact enumerate_getD_of_mem fallbackPlaquette hindexed

/-- Every selected central-cube face incident on a link forces that link into
the twelve-element cube boundary. -/
theorem mem_coarseCubeBoundaryLinks_of_slabIncident_selected
    {link : YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    {faceId : Nat}
    (hincident : faceId ∈ slabIncidentPlaqIds 1 link)
    (hselected : faceId ∈ centralLowerCubeFaceIds) :
    link ∈ coarseCubeBoundaryLinks := by
  obtain ⟨plaquette, hindexed, hedge⟩ :=
    mem_slabIncidentPlaqIds.mp hincident
  have hlookup : slabPlaquetteAt 1 faceId = plaquette :=
    slabPlaquetteAt_eq_of_enumerate_local hindexed
  have hcube : plaquette ∈ unitCubeSurface := by
    rw [← hlookup]
    exact slabPlaquetteAt_one_mem_unitCubeSurface_of_mem hselected
  have hboundary : link ∈ unitCubeSurface.flatMap edgesOf :=
    List.mem_flatMap.mpr ⟨plaquette, hcube, hedge⟩
  by_cases hmem : link ∈ coarseCubeBoundaryLinks
  · exact hmem
  · have htwo := unitCubeBoundaryMultiplicity_eq_two_of_mem hboundary
    have htwice := unitCubeBoundaryMultiplicity_eq_twice link
    have hzero := occurrenceCount_eq_zero_of_not_mem
      link coarseCubeBoundaryLinks hmem
    rw [htwice, hzero] at htwo
    omega

/-- Outside the twelve cube-boundary links, the entire incident spin word is
definitionally unchanged by the global six-face mate. -/
theorem slabIncidentPhysicalSpins_centralCubeEvenInwardMate_eq_of_not_boundary
    (physical : EdgeLabelling)
    {link : YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    (hnot : link ∉ coarseCubeBoundaryLinks) :
    (slabIncidentPlaqIds 1 link).map
        (centralLowerCubeEvenInwardMatePhysical physical) =
      (slabIncidentPlaqIds 1 link).map physical := by
  apply List.map_congr_left
  intro faceId hincident
  by_cases hselected : faceId ∈ centralLowerCubeFaceIds
  · exact False.elim
      (hnot (mem_coarseCubeBoundaryLinks_of_slabIncident_selected
        hincident hselected))
  · exact centralLowerCubeEvenInwardMatePhysical_off_cube
      physical hselected

theorem slabExplicitLinkMultiplicity_centralCubeEvenInwardMate_eq_of_not_boundary
    (K : Nat) (physical : EdgeLabelling)
    {link : YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    (hnot : link ∉ coarseCubeBoundaryLinks) :
    slabExplicitLinkMultiplicity K 1
        (centralLowerCubeEvenInwardMatePhysical physical) link =
      slabExplicitLinkMultiplicity K 1 physical link := by
  unfold slabExplicitLinkMultiplicity
  rw [slabIncidentPhysicalSpins_centralCubeEvenInwardMate_eq_of_not_boundary
    physical hnot]

/-! ## 2. One explicit data record per boundary link -/

abbrev CubeProductionIncidenceMember :=
  { incidence : CubeProductionIncidence //
    incidence ∈ cubeProductionIncidences }

def cubeInwardMateLinkCertificate
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :=
  slabExplicitLinkMultiplicityCentralCubeEvenInwardMateLeAddStretched
    K linked.1 linked.2 physical hK hbounded

/-- The residual incident word carried as data by one boundary-link
certificate. -/
def cubeInwardMateLinkRest
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) : List Nat :=
  (cubeInwardMateLinkCertificate K physical hK hbounded linked).1

def cubeInwardMateSourceLinkMultiplicity
    (K : Nat) (physical : EdgeLabelling)
    (linked : CubeProductionIncidenceMember) : Nat :=
  slabExplicitLinkMultiplicity K 1 physical linked.1.link

def cubeInwardMateTargetLinkMultiplicity
    (K : Nat) (physical : EdgeLabelling)
    (linked : CubeProductionIncidenceMember) : Nat :=
  slabExplicitLinkMultiplicity K 1
    (centralLowerCubeEvenInwardMatePhysical physical) linked.1.link

/-- The sole local obstruction: the continuation after fusing the two
incident cube spins through their stretched channel. -/
def cubeInwardMateStretchedDebt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) : Nat :=
  explicitValenceMultiplicity (linkAuxiliaryCutoff K)
    ((physical (centralLowerCubeFaceId linked.1.left) +
      physical (centralLowerCubeFaceId linked.1.right)) ::
      cubeInwardMateLinkRest K physical hK hbounded linked).length
    (externalSpinsOfList
      ((physical (centralLowerCubeFaceId linked.1.left) +
        physical (centralLowerCubeFaceId linked.1.right)) ::
        cubeInwardMateLinkRest K physical hK hbounded linked))

theorem cubeInwardMateSourceLinkMultiplicity_le_target_add_stretchedDebt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    cubeInwardMateSourceLinkMultiplicity K physical linked ≤
      cubeInwardMateTargetLinkMultiplicity K physical linked +
        cubeInwardMateStretchedDebt K physical hK hbounded linked := by
  exact (cubeInwardMateLinkCertificate K physical hK hbounded linked).2.2.2

/-! ## 3. Multiplying the twelve local inequalities -/

private theorem natListProduct_mono_on
    {A : Type} (left right : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        natListProduct left items ≤ natListProduct right items
  | [], _ => Nat.le_refl 1
  | head :: tail, hle => by
      simp only [natListProduct]
      exact Nat.mul_le_mul
        (hle head List.mem_cons_self)
        (natListProduct_mono_on left right tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

def cubeInwardMateSourceBoundaryProduct
    (K : Nat) (physical : EdgeLabelling) : Nat :=
  natListProduct (cubeInwardMateSourceLinkMultiplicity K physical)
    cubeProductionIncidences.attach

def cubeInwardMateTargetPlusDebtBoundaryProduct
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Nat :=
  natListProduct
    (fun linked =>
      cubeInwardMateTargetLinkMultiplicity K physical linked +
        cubeInwardMateStretchedDebt K physical hK hbounded linked)
    cubeProductionIncidences.attach

/-- **Twelve-link product compiler.**  The complete cube-boundary source
intertwiner multiplicity is bounded by the product of the twelve explicit
`mate + stretchedDebt` factors. -/
theorem cubeInwardMateSourceBoundaryProduct_le_targetPlusDebt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    cubeInwardMateSourceBoundaryProduct K physical ≤
      cubeInwardMateTargetPlusDebtBoundaryProduct
        K physical hK hbounded := by
  apply natListProduct_mono_on
  intro linked _
  exact cubeInwardMateSourceLinkMultiplicity_le_target_add_stretchedDebt
    K physical hK hbounded linked

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.mem_coarseCubeBoundaryLinks_of_slabIncident_selected
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.slabExplicitLinkMultiplicity_centralCubeEvenInwardMate_eq_of_not_boundary
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.cubeInwardMateLinkCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.cubeInwardMateSourceBoundaryProduct_le_targetPlusDebt
