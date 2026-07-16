/-
# Explicit translated composition of projected fine cubes

The two assignments retained by the six-slot fine-support projector are now
realized simultaneously in one physical size-five box.  The odd cube is
embedded by exact zero extension, while its corrected-slab partner is the
genuine one-step Euclidean-time translate.  Their geometric supports lie on
different time slices, hence share neither a face nor an actual lattice link.

Both physical summands are obtained from the same derived sixth-power mass by
exact cross-volume/time-translation covariance.  Thus the abstract separation
hypotheses of the projected two-cube bridge are concretely inhabited.  A final
finite-family wrapper lifts the binary bridge to arbitrary recursively
link-separated lists and is instantiated by this reflection pair.
-/

import YMGap.Continuum.Z4DyadicSlabCubeKernelProductComposition
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
import YMGap.Continuum.Z4TimeShiftedPhysicalWeights

namespace YMGap.Continuum.Z4DyadicSlabCubeTranslatedProjectedComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSlabCubeFineSupportProjectedKernel
open YMGap.Continuum.Z4DyadicSlabCubeKernelProductComposition
open YMGap.Continuum.Z4DyadicSlabCubePhysicalSummandBridge
open YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
open YMGap.Continuum.Z4DyadicSU2ParityMinimalLiftFence
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open YMGap.Continuum.Z4TimeShiftedPhysicalWeights
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sameSupport_map_local
    {X Y : List Z4Plaq} (mapP : Z4Plaq → Z4Plaq)
    (h : sameSupport (L := z4Chain.toLattice) X Y) :
    sameSupport (L := z4Chain.toLattice)
      (X.map mapP) (Y.map mapP) := by
  constructor
  · intro target htarget
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htarget
    exact List.mem_map.mpr ⟨source, h.1 source hsource, rfl⟩
  · intro target htarget
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htarget
    exact List.mem_map.mpr ⟨source, h.2 source hsource, rfl⟩

/-! ## 1. Two physical embeddings in one box -/

abbrev oddFineCubePhysical : EdgeLabelling :=
  componentLabel oddFineUnitCubeSupportIds

def embeddedOddFineCubePhysical : EdgeLabelling :=
  transportPhysical 4 5 oddFineCubePhysical

def timeReflectedOddFineCubePhysical : EdgeLabelling :=
  timeShiftTransportPhysical 1 4 oddFineCubePhysical

def embeddedOddFineCubeSupportIds : List Nat :=
  transportPolymer 4 5 oddFineUnitCubeSupportIds

def timeReflectedOddFineCubeSupportIds : List Nat :=
  timeShiftCanonicalRoot 1 4 oddFineUnitCubeSupportIds

theorem oddFineCubePhysical_mem :
    oddFineCubePhysical ∈ explicitPhysicalLabellings 1 4 := by
  simpa [oddFineCubePhysical,
    dyadicParityFineStateSpace] using
    oddFineUnitCubeLabel_mem_fineStateSpace

private theorem oddFineCubePhysical_mem_bounded :
    oddFineCubePhysical ∈
      boundedEdgeLabellings 1
        (List.range (plaquetteEdgeCount 4)) := by
  simpa [explicitPhysicalLabellings, physicalFaceEdges] using
    oddFineCubePhysical_mem

theorem embeddedOddFineCubePhysical_mem :
    embeddedOddFineCubePhysical ∈
      explicitPhysicalLabellings 1 5 := by
  unfold embeddedOddFineCubePhysical explicitPhysicalLabellings
    physicalFaceEdges
  exact transportPhysical_mem_bounded oddFineCubePhysical_mem_bounded

theorem timeReflectedOddFineCubePhysical_mem :
    timeReflectedOddFineCubePhysical ∈
      explicitPhysicalLabellings 1 5 := by
  unfold timeReflectedOddFineCubePhysical explicitPhysicalLabellings
    physicalFaceEdges
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using timeShiftTransportPhysical_mem_bounded
      (shift := 1) oddFineCubePhysical_mem_bounded

theorem embeddedOddFineCube_excitedSupport :
    excitedPlaquetteIds 5 embeddedOddFineCubePhysical =
      embeddedOddFineCubeSupportIds := by
  unfold embeddedOddFineCubePhysical embeddedOddFineCubeSupportIds
  rw [excitedPlaquetteIds_transportPhysical,
    excitedPlaquetteIds_componentLabel_eq_support
      oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports]

theorem timeReflectedOddFineCube_excitedSupport :
    excitedPlaquetteIds 5 timeReflectedOddFineCubePhysical =
      timeReflectedOddFineCubeSupportIds := by
  unfold timeReflectedOddFineCubePhysical
    timeReflectedOddFineCubeSupportIds
  change excitedPlaquetteIds (4 + 1)
      (timeShiftTransportPhysical 1 4 oddFineCubePhysical) = _
  rw [excitedPlaquetteIds_timeShiftTransportPhysical,
    excitedPlaquetteIds_componentLabel_eq_support
      oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports]

theorem embeddedOddFineCubeSupportIds_mem :
    embeddedOddFineCubeSupportIds ∈ cutoffOneFaceSupports 5 := by
  unfold embeddedOddFineCubeSupportIds
  exact transportPolymer_mem_cutoffOneFaceSupports
    4 5 oddFineUnitCubeSupportIds

theorem timeReflectedOddFineCubeSupportIds_mem :
    timeReflectedOddFineCubeSupportIds ∈
      cutoffOneFaceSupports 5 := by
  unfold timeReflectedOddFineCubeSupportIds timeShiftCanonicalRoot
  exact geometricSupportIds_mem_cutoffOneFaceSupports 5 _

theorem embeddedOddFineCubePhysical_eq_componentLabel :
    embeddedOddFineCubePhysical =
      componentLabel embeddedOddFineCubeSupportIds := by
  apply cutoffOne_supportIds_injective
    embeddedOddFineCubePhysical_mem
  · rw [explicitPhysicalLabellings_one_eq_supportIndicators]
    exact List.mem_map.mpr
      ⟨embeddedOddFineCubeSupportIds,
        embeddedOddFineCubeSupportIds_mem, rfl⟩
  · rw [embeddedOddFineCube_excitedSupport,
      excitedPlaquetteIds_componentLabel_eq_support
        embeddedOddFineCubeSupportIds_mem]

theorem timeReflectedOddFineCubePhysical_eq_componentLabel :
    timeReflectedOddFineCubePhysical =
      componentLabel timeReflectedOddFineCubeSupportIds := by
  apply cutoffOne_supportIds_injective
    timeReflectedOddFineCubePhysical_mem
  · rw [explicitPhysicalLabellings_one_eq_supportIndicators]
    exact List.mem_map.mpr
      ⟨timeReflectedOddFineCubeSupportIds,
        timeReflectedOddFineCubeSupportIds_mem, rfl⟩
  · rw [timeReflectedOddFineCube_excitedSupport,
      excitedPlaquetteIds_componentLabel_eq_support
        timeReflectedOddFineCubeSupportIds_mem]

/-! ## 2. Literal geometric separation and corrected reflection -/

def timeShiftedOddFineUnitCubeSurface : List Z4Plaq :=
  oddFineUnitCubeSurface.map (timeShiftPlaquette 1)

theorem timeShiftedOddFineUnitCubeSurface_same_reflected :
    sameSupport (L := z4Chain.toLattice)
      timeShiftedOddFineUnitCubeSurface
      reflectedOddFineCubeSurface := by
  have hmapped := sameSupport_map_local (timeShiftPlaquette 1)
    cubeOrderedOddFineSurface_sameSupport
  have hsymm := sameSupport_symm hmapped
  simpa [timeShiftedOddFineUnitCubeSurface,
    reflectedOddFineCubeSurface_eq_timeShift] using hsymm

theorem oddFineUnitCubeSurface_time_zero
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ oddFineUnitCubeSurface) :
    plaquette.1.2.2.2 = 0 := by
  simp only [oddFineUnitCubeSurface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem oddFineUnitCubeSurface_spatialPlane
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ oddFineUnitCubeSurface) :
    plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12 := by
  simp only [oddFineUnitCubeSurface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

theorem timeShiftedOddFineUnitCubeSurface_time_one
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ timeShiftedOddFineUnitCubeSurface) :
    plaquette.1.2.2.2 = 1 := by
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  have htime := oddFineUnitCubeSurface_time_zero hsource
  simp only [timeShiftPlaquette, timeShiftVertex] at htime ⊢
  omega

theorem timeShiftedOddFineUnitCubeSurface_spatialPlane
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ timeShiftedOddFineUnitCubeSurface) :
    plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12 := by
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq]
  simpa only [timeShiftPlaquette] using
    oddFineUnitCubeSurface_spatialPlane hsource

private theorem spatialPlaquette_edge_timeCoordinate
    {plaquette : Z4Plaq} {link : Z4Link}
    (hplane : plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12)
    (hlink : link ∈ edgesOf plaquette) :
    link.1.2.2.2 = plaquette.1.2.2.2 := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rcases hplane with rfl | rfl | rfl <;>
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hlink <;>
    rcases hlink with rfl | rfl | rfl | rfl <;> rfl

theorem oddAndTimeShiftedFineCubeSurfaces_disjoint :
    SupportsDisjoint oddFineUnitCubeSurface
      timeShiftedOddFineUnitCubeSurface := by
  intro plaquette hzero hone
  have htimeZero := oddFineUnitCubeSurface_time_zero hzero
  have htimeOne := timeShiftedOddFineUnitCubeSurface_time_one hone
  omega

theorem oddAndTimeShiftedFineCubeSurfaces_linkDisjoint
    {first second : Z4Plaq} {link : Z4Link}
    (hfirst : first ∈ oddFineUnitCubeSurface)
    (hsecond : second ∈ timeShiftedOddFineUnitCubeSurface)
    (hlinkFirst : link ∈ edgesOf first)
    (hlinkSecond : link ∈ edgesOf second) : False := by
  have hfirstTime := spatialPlaquette_edge_timeCoordinate
    (oddFineUnitCubeSurface_spatialPlane hfirst) hlinkFirst
  have hsecondTime := spatialPlaquette_edge_timeCoordinate
    (timeShiftedOddFineUnitCubeSurface_spatialPlane hsecond) hlinkSecond
  rw [oddFineUnitCubeSurface_time_zero hfirst] at hfirstTime
  rw [timeShiftedOddFineUnitCubeSurface_time_one hsecond] at hsecondTime
  omega

theorem embeddedOddFineCubeSupportIds_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 5 embeddedOddFineCubeSupportIds)
      oddFineUnitCubeSurface := by
  exact sameSupport_trans
    (sameSupport_symm
      (transportPolymer_sameSupport (by omega)
        oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports))
    oddFineUnitCubeSupportIds_sameSupport

theorem timeReflectedOddFineCubeSupportIds_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 5 timeReflectedOddFineCubeSupportIds)
      timeShiftedOddFineUnitCubeSurface := by
  unfold timeReflectedOddFineCubeSupportIds timeShiftCanonicalRoot
  exact sameSupport_trans
    (geometricSupportIds_sameSupport (by
      intro plaquette hplaquette
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
      exact timeShiftPlaquette_mem_box_add
        (geometricPolymer_subset_box
          oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports
          source hsource)))
    (sameSupport_map_local (timeShiftPlaquette 1)
      oddFineUnitCubeSupportIds_sameSupport)

theorem embeddedAndTimeReflectedSupportIds_disjoint :
    SupportsDisjoint embeddedOddFineCubeSupportIds
      timeReflectedOddFineCubeSupportIds := by
  intro face hleft hright
  have hleftGeom : boxPlaquetteAt 5 face ∈
      geometricPolymer 5 embeddedOddFineCubeSupportIds :=
    List.mem_map.mpr ⟨face, hleft, rfl⟩
  have hrightGeom : boxPlaquetteAt 5 face ∈
      geometricPolymer 5 timeReflectedOddFineCubeSupportIds :=
    List.mem_map.mpr ⟨face, hright, rfl⟩
  exact oddAndTimeShiftedFineCubeSurfaces_disjoint
    (boxPlaquetteAt 5 face)
    (embeddedOddFineCubeSupportIds_sameSupport.1 _ hleftGeom)
    (timeReflectedOddFineCubeSupportIds_sameSupport.1 _ hrightGeom)

theorem embeddedAndTimeReflectedSupportIds_separated :
    SupportsSeparated (faceLinkAdjacentB 5)
      embeddedOddFineCubeSupportIds
      timeReflectedOddFineCubeSupportIds := by
  intro first hfirst second hsecond
  cases hadj : faceLinkAdjacentB 5 first second with
  | false => rfl
  | true =>
      have hactual := actualAdjacentOfFaceLinkAdjacent hadj
      have hfirstGeom : boxPlaquetteAt 5 first ∈
          geometricPolymer 5 embeddedOddFineCubeSupportIds :=
        List.mem_map.mpr ⟨first, hfirst, rfl⟩
      have hsecondGeom : boxPlaquetteAt 5 second ∈
          geometricPolymer 5 timeReflectedOddFineCubeSupportIds :=
        List.mem_map.mpr ⟨second, hsecond, rfl⟩
      have hleft := hactual.on_p
      have hright := hactual.on_q
      change z4Boundary (boxPlaquetteAt 5 first) hactual.link = true
        at hleft
      change z4Boundary (boxPlaquetteAt 5 second) hactual.link = true
        at hright
      exact False.elim
        (oddAndTimeShiftedFineCubeSurfaces_linkDisjoint
          (embeddedOddFineCubeSupportIds_sameSupport.1 _ hfirstGeom)
          (timeReflectedOddFineCubeSupportIds_sameSupport.1 _ hsecondGeom)
          (of_decide_eq_true hleft) (of_decide_eq_true hright))

theorem embeddedAndTimeReflected_faceDisjoint :
    FaceDisjoint 5 embeddedOddFineCubePhysical
      timeReflectedOddFineCubePhysical := by
  rw [embeddedOddFineCubePhysical_eq_componentLabel,
    timeReflectedOddFineCubePhysical_eq_componentLabel]
  intro face _
  by_cases hleft : face ∈ embeddedOddFineCubeSupportIds
  · right
    apply componentLabel_eq_zero_of_not_mem
    intro hright
    exact embeddedAndTimeReflectedSupportIds_disjoint face hleft hright
  · left
    exact componentLabel_eq_zero_of_not_mem hleft

theorem embeddedAndTimeReflected_linkSeparated :
    LinkSeparated 5 embeddedOddFineCubePhysical
      timeReflectedOddFineCubePhysical := by
  rw [embeddedOddFineCubePhysical_eq_componentLabel,
    timeReflectedOddFineCubePhysical_eq_componentLabel]
  have hsingle := componentLabel_linkSeparated_union 5
    embeddedOddFineCubeSupportIds
    [timeReflectedOddFineCubeSupportIds] (by
      intro component hcomponent
      have heq := List.mem_singleton.mp hcomponent
      subst component
      exact embeddedAndTimeReflectedSupportIds_separated)
  have hsingleton :
      binaryUnionLabels
          [componentLabel timeReflectedOddFineCubeSupportIds] =
        componentLabel timeReflectedOddFineCubeSupportIds := by
    funext face
    simp [binaryUnionLabels, binaryUnionLabel, zeroEdgeLabelling]
  change LinkSeparated 5
    (componentLabel embeddedOddFineCubeSupportIds)
    (binaryUnionLabels
      [componentLabel timeReflectedOddFineCubeSupportIds]) at hsingle
  rw [hsingleton] at hsingle
  exact hsingle

/-! ## 3. Exact translated production-summand bridges -/

theorem embeddedOddFineCube_raw_eqv_production
    (w : Q') :
    closedCubeFineSlotRawWeight w oddFineCubeSlotAssignment ≈
      parametricLocalizedSpinFoamWeight w 5
        embeddedOddFineCubePhysical := by
  exact Q'.eqv_trans _
    (parametricLocalizedSpinFoamWeight w 4 oddFineCubePhysical) _
    (oddFineCubeProjectedSummandBridge w).raw_eqv
    (Q'.eqv_trans _
      (parametricKPhysicalTerm w 1 4 oddFineCubePhysical) _
      (Q'.eqv_symm
        (parametricKPhysicalTerm_one_eqv_localized
          w 4 oddFineCubePhysical))
      (Q'.eqv_trans _
        (parametricKPhysicalTerm w 1 5
          embeddedOddFineCubePhysical) _
        (parametricKPhysicalTerm_cross_volume w (by omega)
          oddFineCubePhysical_mem_bounded)
        (parametricKPhysicalTerm_one_eqv_localized
          w 5 embeddedOddFineCubePhysical)))

theorem timeReflectedOddFineCube_raw_eqv_production
    (w : Q') :
    closedCubeFineSlotRawWeight w
        reflectedOddFineCubeSlotAssignment ≈
      parametricLocalizedSpinFoamWeight w 5
        timeReflectedOddFineCubePhysical := by
  exact Q'.eqv_trans _
    (closedCubeFineSlotRawWeight w oddFineCubeSlotAssignment) _
    (Q'.eqv_trans _ ((coeffW w 1) ^ 6) _
      (closedCubeFineSlotRawWeight_eqv_pow_six w _)
      (Q'.eqv_symm
        (closedCubeFineSlotRawWeight_eqv_pow_six w
          oddFineCubeSlotAssignment)))
    (Q'.eqv_trans _
      (parametricLocalizedSpinFoamWeight w 4 oddFineCubePhysical) _
      (oddFineCubeProjectedSummandBridge w).raw_eqv
      (Q'.eqv_trans _
        (parametricKPhysicalTerm w 1 4 oddFineCubePhysical) _
        (Q'.eqv_symm
          (parametricKPhysicalTerm_one_eqv_localized
            w 4 oddFineCubePhysical))
        (Q'.eqv_trans _
          (parametricKPhysicalTerm w 1 5
            timeReflectedOddFineCubePhysical) _
          (by
            simpa only [Nat.add_comm] using
              (parametricKPhysicalTerm_timeShift w
                (shift := 1) oddFineCubePhysical_mem_bounded))
          (parametricKPhysicalTerm_one_eqv_localized
            w 5 timeReflectedOddFineCubePhysical))))

def embeddedOddProjectedSummandBridge (w : Q') :
    ProjectedFineCubeSummandBridge w 5 where
  assignment := oddFineCubeSlotAssignment
  assignment_mem := oddFineCubeSlotAssignment_mem_closed
  physical := embeddedOddFineCubePhysical
  physical_mem := embeddedOddFineCubePhysical_mem
  raw_eqv := embeddedOddFineCube_raw_eqv_production w

def timeReflectedProjectedSummandBridge (w : Q') :
    ProjectedFineCubeSummandBridge w 5 where
  assignment := reflectedOddFineCubeSlotAssignment
  assignment_mem := reflectedOddFineCubeSlotAssignment_mem_closed
  physical := timeReflectedOddFineCubePhysical
  physical_mem := timeReflectedOddFineCubePhysical_mem
  raw_eqv := timeReflectedOddFineCube_raw_eqv_production w

def explicitReflectionSeparatedProjectedPair (w : Q') :
    LinkSeparatedProjectedFineCubePair w 5 where
  left := embeddedOddProjectedSummandBridge w
  right := timeReflectedProjectedSummandBridge w
  faceDisjoint := embeddedAndTimeReflected_faceDisjoint
  linkSeparated := embeddedAndTimeReflected_linkSeparated

theorem explicitReflectionSeparatedProjectedPair_unionProduction
    (w : Q') :
    bridgedProjectedTwoCubeRawProduct
        (explicitReflectionSeparatedProjectedPair w) ≈
      parametricLocalizedSpinFoamWeight w 5
        (binaryUnionLabel embeddedOddFineCubePhysical
          timeReflectedOddFineCubePhysical) :=
  bridgedProjectedTwoCubeRawProduct_eqv_unionProductionSummand
    (explicitReflectionSeparatedProjectedPair w)

/-! ## 4. Finite projected families and exact product composition -/

def projectedFineCubeRawProduct (w : Q') :
    List (ProjectedFineCubeSummandBridge w n) → Q'
  | [] => 1
  | head :: tail =>
      closedCubeFineSlotRawWeight w head.assignment *
        projectedFineCubeRawProduct w tail

structure LinkSeparatedProjectedFineCubeFamily
    (w : Q') (n : Nat) where
  bridges : List (ProjectedFineCubeSummandBridge w n)
  separated : LinkSeparatedFamily n (bridges.map fun bridge => bridge.physical)

theorem projectedBridgePhysicalFamily
    (w : Q') (n : Nat)
    (bridges : List (ProjectedFineCubeSummandBridge w n)) :
    PhysicalFamily n (bridges.map fun bridge => bridge.physical) := by
  intro physical hphysical
  obtain ⟨bridge, hbridge, heq⟩ := List.mem_map.mp hphysical
  rw [← heq]
  exact bridge.physical_mem

theorem projectedFineCubeRawProduct_eqv_physicalProduct
    (w : Q') (n : Nat) :
    ∀ bridges : List (ProjectedFineCubeSummandBridge w n),
    projectedFineCubeRawProduct w bridges ≈
      parametricLocalizedWeightProduct w n
        (bridges.map fun bridge => bridge.physical)
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      change
        closedCubeFineSlotRawWeight w head.assignment *
            projectedFineCubeRawProduct w tail ≈
          parametricLocalizedSpinFoamWeight w n head.physical *
            parametricLocalizedWeightProduct w n
              (tail.map fun bridge => bridge.physical)
      exact qmul_congr head.raw_eqv
        (projectedFineCubeRawProduct_eqv_physicalProduct w n tail)

theorem linkSeparatedProjectedFineCubeFamily_unionProduction
    {w : Q'} {n : Nat}
    (family : LinkSeparatedProjectedFineCubeFamily w n) :
    projectedFineCubeRawProduct w family.bridges ≈
      parametricLocalizedSpinFoamWeight w n
        (binaryUnionLabels
          (family.bridges.map fun bridge => bridge.physical)) := by
  exact Q'.eqv_trans _
    (parametricLocalizedWeightProduct w n
      (family.bridges.map fun bridge => bridge.physical)) _
    (projectedFineCubeRawProduct_eqv_physicalProduct
      w n family.bridges)
    (Q'.eqv_symm
      (parametricLocalizedSpinFoamWeight_unionLabels_factor
        w n (family.bridges.map fun bridge => bridge.physical)
        (projectedBridgePhysicalFamily w n family.bridges)
        family.separated))

private theorem hasExcitedB_zero :
    ∀ faces : List Nat, hasExcitedB zeroEdgeLabelling faces = false
  | [] => rfl
  | _ :: tail => by
      simp [hasExcitedB, zeroEdgeLabelling, hasExcitedB_zero tail]

private theorem faceDisjoint_zero_right
    (n : Nat) (physical : EdgeLabelling) :
    FaceDisjoint n physical zeroEdgeLabelling := by
  intro _ _
  exact Or.inr rfl

private theorem linkSeparated_zero_right
    (n : Nat) (physical : EdgeLabelling) :
    LinkSeparated n physical zeroEdgeLabelling := by
  intro indexed _ hboth
  have hzero : linkTouchesExcitationB n zeroEdgeLabelling indexed = false := by
    unfold linkTouchesExcitationB
    exact hasExcitedB_zero _
  rw [hzero] at hboth
  exact Bool.noConfusion hboth.2

def explicitReflectionProjectedFamily (w : Q') :
    LinkSeparatedProjectedFineCubeFamily w 5 where
  bridges :=
    [embeddedOddProjectedSummandBridge w,
      timeReflectedProjectedSummandBridge w]
  separated := by
    change
      FaceDisjoint 5 embeddedOddFineCubePhysical
          (binaryUnionLabels [timeReflectedOddFineCubePhysical]) ∧
        LinkSeparated 5 embeddedOddFineCubePhysical
            (binaryUnionLabels [timeReflectedOddFineCubePhysical]) ∧
          FaceDisjoint 5 timeReflectedOddFineCubePhysical
              (binaryUnionLabels []) ∧
            LinkSeparated 5 timeReflectedOddFineCubePhysical
                (binaryUnionLabels []) ∧ True
    have hsingleton :
        binaryUnionLabels [timeReflectedOddFineCubePhysical] =
          timeReflectedOddFineCubePhysical := by
      funext edge
      simp [binaryUnionLabels, binaryUnionLabel, zeroEdgeLabelling]
    rw [hsingleton]
    exact ⟨embeddedAndTimeReflected_faceDisjoint,
      embeddedAndTimeReflected_linkSeparated,
      faceDisjoint_zero_right 5 timeReflectedOddFineCubePhysical,
      linkSeparated_zero_right 5 timeReflectedOddFineCubePhysical,
      trivial⟩

theorem explicitReflectionProjectedFamily_unionProduction
    (w : Q') :
    projectedFineCubeRawProduct w
        (explicitReflectionProjectedFamily w).bridges ≈
      parametricLocalizedSpinFoamWeight w 5
        (binaryUnionLabels
          ((explicitReflectionProjectedFamily w).bridges.map
            fun bridge => bridge.physical)) :=
  linkSeparatedProjectedFineCubeFamily_unionProduction
    (explicitReflectionProjectedFamily w)

/-! ## 5. Exact overlap fence -/

/-- Reusing the same physical cube twice cannot satisfy even the face part of
the separation interface.  Product composition therefore cannot silently
identify overlapping translated copies as independent factors. -/
theorem oddFineCube_self_not_faceDisjoint :
    ¬ FaceDisjoint 4 oddFineCubePhysical oddFineCubePhysical := by
  intro hdisjoint
  have hfaceMem : 504 ∈ oddFineUnitCubeSupportIds := by
    exact List.mem_cons_self
  have hphysicalFace : 504 ∈ physicalFaceEdges 4 := by
    have hsupport := oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports
    unfold cutoffOneFaceSupports at hsupport
    exact mem_of_mem_sublists (physicalFaceEdges 4)
      oddFineUnitCubeSupportIds
      hsupport
      504 hfaceMem
  have hone : oddFineCubePhysical 504 = 1 :=
    (componentLabel_eq_one_iff).mpr hfaceMem
  have hzero := hdisjoint 504 hphysicalFace
  rw [hone] at hzero
  rcases hzero with hzero | hzero <;> omega

/-! ## Dependency gates -/

#print axioms embeddedOddFineCubePhysical_mem
#print axioms timeReflectedOddFineCubePhysical_mem
#print axioms timeShiftedOddFineUnitCubeSurface_same_reflected
#print axioms oddAndTimeShiftedFineCubeSurfaces_linkDisjoint
#print axioms embeddedAndTimeReflectedSupportIds_disjoint
#print axioms embeddedAndTimeReflectedSupportIds_separated
#print axioms embeddedAndTimeReflected_faceDisjoint
#print axioms embeddedAndTimeReflected_linkSeparated
#print axioms embeddedOddFineCube_raw_eqv_production
#print axioms timeReflectedOddFineCube_raw_eqv_production
#print axioms explicitReflectionSeparatedProjectedPair
#print axioms explicitReflectionSeparatedProjectedPair_unionProduction
#print axioms projectedFineCubeRawProduct_eqv_physicalProduct
#print axioms linkSeparatedProjectedFineCubeFamily_unionProduction
#print axioms explicitReflectionProjectedFamily
#print axioms explicitReflectionProjectedFamily_unionProduction
#print axioms oddFineCube_self_not_faceDisjoint

end YMGap.Continuum.Z4DyadicSlabCubeTranslatedProjectedComposition
