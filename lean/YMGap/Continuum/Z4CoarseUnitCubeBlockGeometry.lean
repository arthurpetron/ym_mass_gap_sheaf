/-
# The elementary cube as the coarse side of the dyadic block

The existing dyadic block geometry starts with the six faces of the unit
cube and refines each face into four plaquettes.  This module gives the
unrefined six-face boundary its own canonical polymer carrier.  The two
carriers can therefore be compared inside the same exact finite-support
language instead of identifying a geometric cube with an unrelated mode.

The result is purely geometric: both the coarse root and its 24-face dyadic
refinement are canonical connected supports.  No equality of their Gibbs
laws or renormalized couplings is asserted here.
-/

import YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry

namespace YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry

set_option maxRecDepth 10000

open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

private def z4ChainInTrans {support : List Z4Plaq} :
    {first middle last : Z4Plaq} →
      ChainIn z4Chain.toLattice support first middle →
      ChainIn z4Chain.toLattice support middle last →
      ChainIn z4Chain.toLattice support first last
  | _, _, _, .refl _, right => right
  | _, _, _, .step adjacent hnext rest, right =>
      .step adjacent hnext (z4ChainInTrans rest right)

private def z4ChainInReverse {support : List Z4Plaq} :
    {first last : Z4Plaq} →
      ChainIn z4Chain.toLattice support first last →
      first ∈ support →
      ChainIn z4Chain.toLattice support last first
  | _, _, .refl plaquette, _ => .refl plaquette
  | first, _, .step adjacent hmiddle rest, hfirst =>
      z4ChainInTrans (z4ChainInReverse rest hmiddle)
        (.step (adjacentSymm adjacent) hfirst
          (show ChainIn z4Chain.toLattice support first first from
            @ChainIn.refl z4Chain.toLattice support first))

/-! ## Five literal shared-link bridges between the six faces -/

def coarseBottomFrontAdjacent :
    z4Chain.toLattice.Adjacent
      (cubeFace .bottomXY) (cubeFace .frontXZ) := by
  refine { link := ((0, 0, 0, 0), .x0), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def coarseBottomLeftAdjacent :
    z4Chain.toLattice.Adjacent
      (cubeFace .bottomXY) (cubeFace .leftYZ) := by
  refine { link := ((0, 0, 0, 0), .x1), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def coarseBottomBackAdjacent :
    z4Chain.toLattice.Adjacent
      (cubeFace .bottomXY) (cubeFace .backXZ) := by
  refine { link := ((0, 1, 0, 0), .x0), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def coarseBottomRightAdjacent :
    z4Chain.toLattice.Adjacent
      (cubeFace .bottomXY) (cubeFace .rightYZ) := by
  refine { link := ((1, 0, 0, 0), .x1), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def coarseFrontTopAdjacent :
    z4Chain.toLattice.Adjacent
      (cubeFace .frontXZ) (cubeFace .topXY) := by
  refine { link := ((0, 0, 1, 0), .x0), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def coarseCubeHub : Z4Plaq := cubeFace .bottomXY

/-- A concrete path from every coarse face to the bottom-face hub. -/
def coarseCubeFaceToHub :
    ∀ face : CubeFaceIndex,
      ChainIn z4Chain.toLattice unitCubeSurface
        (cubeFace face) coarseCubeHub
  | .bottomXY => .refl _
  | .topXY =>
      .step (adjacentSymm coarseFrontTopAdjacent)
        (cubeFace_mem_unitCubeSurface .frontXZ)
        (.step (adjacentSymm coarseBottomFrontAdjacent)
          (cubeFace_mem_unitCubeSurface .bottomXY) (.refl _))
  | .frontXZ =>
      .step (adjacentSymm coarseBottomFrontAdjacent)
        (cubeFace_mem_unitCubeSurface .bottomXY) (.refl _)
  | .backXZ =>
      .step (adjacentSymm coarseBottomBackAdjacent)
        (cubeFace_mem_unitCubeSurface .bottomXY) (.refl _)
  | .leftYZ =>
      .step (adjacentSymm coarseBottomLeftAdjacent)
        (cubeFace_mem_unitCubeSurface .bottomXY) (.refl _)
  | .rightYZ =>
      .step (adjacentSymm coarseBottomRightAdjacent)
        (cubeFace_mem_unitCubeSurface .bottomXY) (.refl _)

def decodeCoarseCubeFace (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ unitCubeSurface) :
    Σ' face : CubeFaceIndex, cubeFace face = plaquette := by
  have hmap : plaquette ∈ cubeFaceIndices.map cubeFace := by
    rw [cubeFaceIndices_map]
    exact hplaquette
  obtain ⟨face, _, hface⟩ :=
    decodeMapMember cubeFace cubeFaceIndices plaquette hmap
  exact ⟨face, hface⟩

/-- The six unrefined faces form one shared-link connected support. -/
def unitCubeSurface_connected :
    connectedIn (L := z4Chain.toLattice) unitCubeSurface := by
  intro first last hfirst hlast
  obtain ⟨firstFace, hfirstEq⟩ := decodeCoarseCubeFace first hfirst
  obtain ⟨lastFace, hlastEq⟩ := decodeCoarseCubeFace last hlast
  rw [← hfirstEq, ← hlastEq]
  exact z4ChainInTrans
    (coarseCubeFaceToHub firstFace)
    (z4ChainInReverse (coarseCubeFaceToHub lastFace)
      (cubeFace_mem_unitCubeSurface lastFace))

/-! ## Exact coarse-boundary incidence -/

/-- One copy of each of the twelve links on the elementary cube boundary. -/
def coarseCubeBoundaryLinks : List Z4Link :=
  [((0, 0, 0, 0), .x0), ((0, 1, 0, 0), .x0),
   ((0, 0, 1, 0), .x0), ((0, 1, 1, 0), .x0),
   ((0, 0, 0, 0), .x1), ((1, 0, 0, 0), .x1),
   ((0, 0, 1, 0), .x1), ((1, 0, 1, 0), .x1),
   ((0, 0, 0, 0), .x2), ((1, 0, 0, 0), .x2),
   ((0, 1, 0, 0), .x2), ((1, 1, 0, 0), .x2)]

theorem coarseCubeBoundaryLinks_length :
    coarseCubeBoundaryLinks.length = 12 := by
  rfl

theorem coarseCubeBoundaryLinks_nodup : coarseCubeBoundaryLinks.Nodup := by
  simp [coarseCubeBoundaryLinks]

/-- The 24 raw boundary occurrences are exactly two copies of each of the
twelve distinct cube links. -/
theorem unitCubeBoundaryMultiplicity_eq_twice (link : Z4Link) :
    unitCubeBoundaryMultiplicity link =
      2 * occurrenceCount link coarseCubeBoundaryLinks := by
  simp only [unitCubeBoundaryMultiplicity, unitCubeSurface, edgesOf, dirsOf,
    addE, occurrenceCount, coarseCubeBoundaryLinks, List.flatMap_cons,
    List.flatMap_nil, occurrenceCount_append, Nat.zero_add]
  omega

private theorem occurrenceCount_pos_of_mem_local (link : Z4Link) :
    ∀ links : List Z4Link, link ∈ links →
      1 ≤ occurrenceCount link links
  | [], hmem => absurd hmem List.not_mem_nil
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp [occurrenceCount]
      · by_cases hhead : head = link
        · subst head
          simp [occurrenceCount]
        · simp only [occurrenceCount, if_neg hhead, Nat.zero_add]
          exact occurrenceCount_pos_of_mem_local link tail htail

/-- Every actually occurring coarse boundary link is used by exactly two
faces. -/
theorem unitCubeBoundaryMultiplicity_eq_two_of_mem
    {link : Z4Link} (hlink : link ∈ unitCubeSurface.flatMap edgesOf) :
    unitCubeBoundaryMultiplicity link = 2 := by
  have hpositive := occurrenceCount_pos_of_mem_local link
    (unitCubeSurface.flatMap edgesOf) hlink
  change 1 ≤ unitCubeBoundaryMultiplicity link at hpositive
  have htwice := unitCubeBoundaryMultiplicity_eq_twice link
  have hboundary : link ∈ coarseCubeBoundaryLinks := by
    by_cases hmem : link ∈ coarseCubeBoundaryLinks
    · exact hmem
    · have hzero := occurrenceCount_eq_zero_of_not_mem link
        coarseCubeBoundaryLinks hmem
      rw [htwice, hzero] at hpositive
      omega
  have hone := occurrenceCount_eq_one_of_mem_nodup link
    coarseCubeBoundaryLinks coarseCubeBoundaryLinks_nodup hboundary
  rw [htwice, hone]

private theorem geometricIncidentPlaquettes_length_eq_faceIncidenceCount_local
    (link : Z4Link) : ∀ faces : List Z4Plaq,
    (geometricIncidentPlaquettes faces link).length =
      faceIncidenceCount link faces
  | [] => rfl
  | plaquette :: rest => by
      have ih :=
        geometricIncidentPlaquettes_length_eq_faceIncidenceCount_local
          link rest
      unfold geometricIncidentPlaquettes at ih
      unfold geometricIncidentPlaquettes
      rw [List.filter_cons]
      by_cases hboundary : link ∈ edgesOf plaquette
      · simp [hboundary, faceIncidenceCount]
        rw [ih]
        omega
      · simp [hboundary, faceIncidenceCount]
        exact ih

/-- The geometric incidence list at every touched coarse-cube link has
length exactly two. -/
theorem unitCube_geometricIncidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks unitCubeSurface) :
    (geometricIncidentPlaquettes unitCubeSurface link).length = 2 := by
  have hraw : link ∈ unitCubeSurface.flatMap edgesOf := by
    unfold geometricTouchedLinks at hlink
    exact List.mem_eraseDups.mp hlink
  have htwo := unitCubeBoundaryMultiplicity_eq_two_of_mem hraw
  have hoccurrence := occurrenceCount_flatMap_edgesOf link unitCubeSurface
  have hfilter :=
    geometricIncidentPlaquettes_length_eq_faceIncidenceCount_local
      link unitCubeSurface
  unfold unitCubeBoundaryMultiplicity at htwo
  omega

/-! ## Canonical numerical carrier in the coarse box -/

def coarseUnitCubeSupportIds : List Nat :=
  geometricSupportIds 2 unitCubeSurface

theorem coarseUnitCubeSupportIds_length :
    coarseUnitCubeSupportIds.length = 6 := by
  have hsame : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 2 coarseUnitCubeSupportIds) unitCubeSurface := by
    unfold coarseUnitCubeSupportIds
    exact geometricSupportIds_sameSupport unitCubeSurface_subset_box_two
  have hlength := sameSupport_length_eq_of_nodup hsame
    (geometricPolymer_nodup
      (geometricSupportIds_mem_cutoffOneFaceSupports 2 unitCubeSurface))
    unitCubeSurface_nodup
  rw [geometricPolymer_length_eq_support_length] at hlength
  exact hlength.trans unitCubeSurface_length

theorem coarseUnitCubeSupportIds_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 2 coarseUnitCubeSupportIds) unitCubeSurface := by
  unfold coarseUnitCubeSupportIds
  exact geometricSupportIds_sameSupport unitCubeSurface_subset_box_two

/-- The unrefined closed cube is an actual canonical root, not merely a
physical labelling in a separate finite-graph enumeration. -/
theorem coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers :
    coarseUnitCubeSupportIds ∈ canonicalSurfacePolymers 2 := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · unfold coarseUnitCubeSupportIds
    exact geometricSupportIds_mem_cutoffOneFaceSupports 2 unitCubeSurface
  · have hhub : coarseCubeHub ∈
        geometricPolymer 2 coarseUnitCubeSupportIds :=
      coarseUnitCubeSupportIds_sameSupport.2 _
        (cubeFace_mem_unitCubeSurface .bottomXY)
    obtain ⟨identifier, hidentifier, _⟩ :=
      decodeMapMember (boxPlaquetteAt 2) coarseUnitCubeSupportIds
        coarseCubeHub hhub
    exact ⟨identifier, hidentifier⟩
  · unfold coarseUnitCubeSupportIds
    exact geometricSupportIds_connected
      unitCubeSurface_subset_box_two unitCubeSurface_connected

theorem dyadicUnitCubeSupportIds_eq_refine_coarse_surface :
    dyadicUnitCubeSupportIds =
      dyadicSupportIds 2 unitCubeSurface := by
  rfl

#print axioms unitCubeSurface_connected
#print axioms unitCubeBoundaryMultiplicity_eq_twice
#print axioms unitCubeBoundaryMultiplicity_eq_two_of_mem
#print axioms unitCube_geometricIncidentPlaquettes_length_eq_two
#print axioms coarseUnitCubeSupportIds_length
#print axioms coarseUnitCubeSupportIds_sameSupport
#print axioms coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers
#print axioms dyadicUnitCubeSupportIds_eq_refine_coarse_surface

end YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
