/-
# A gauge-closed dyadic unit-cube block

The four-cell refinement of one plaquette is connected but has an unpaired
boundary edge, so it cannot by itself be the physical block observable.  This
module applies the same exact dyadic carrier to all six faces of the elementary
cube.  The result is the 24-plaquette boundary of a cube of side two.

We prove constructively that this refined boundary is duplicate-free,
contained in the refined box, internally connected, and has even incidence at
every lattice link.  Its canonical numerical support is therefore a concrete
closed connected cylinder root.  Positivity of its interacting activity and a
coupling-indexed comparison with the coarse cube remain analytic RG steps.
-/

import YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## The six coarse faces and their refined support -/

inductive CubeFaceIndex
  | bottomXY
  | topXY
  | frontXZ
  | backXZ
  | leftYZ
  | rightYZ
  deriving DecidableEq

def cubeFace : CubeFaceIndex → Z4Plaq
  | .bottomXY => ((0, 0, 0, 0), .p01)
  | .topXY => ((0, 0, 1, 0), .p01)
  | .frontXZ => ((0, 0, 0, 0), .p02)
  | .backXZ => ((0, 1, 0, 0), .p02)
  | .leftYZ => ((0, 0, 0, 0), .p12)
  | .rightYZ => ((1, 0, 0, 0), .p12)

def cubeFaceIndices : List CubeFaceIndex :=
  [.bottomXY, .topXY, .frontXZ, .backXZ, .leftYZ, .rightYZ]

theorem cubeFaceIndices_map :
    cubeFaceIndices.map cubeFace = unitCubeSurface := by
  rfl

theorem cubeFace_mem_unitCubeSurface (face : CubeFaceIndex) :
    cubeFace face ∈ unitCubeSurface := by
  rw [← cubeFaceIndices_map]
  apply List.mem_map.mpr
  refine ⟨face, ?_, rfl⟩
  cases face <;> simp [cubeFaceIndices]

/-- The literal 24-cell boundary of the side-two cube. -/
def refinedUnitCubeSurface : List Z4Plaq :=
  dyadicSupportCells unitCubeSurface

theorem refinedUnitCubeSurface_length :
    refinedUnitCubeSurface.length = 24 := by
  unfold refinedUnitCubeSurface
  rw [dyadicSupportCells_length, unitCubeSurface_length]

theorem refinedUnitCubeSurface_nodup : refinedUnitCubeSurface.Nodup := by
  unfold refinedUnitCubeSurface
  exact dyadicSupportCells_nodup unitCubeSurface_nodup

theorem unitCubeSurface_subset_box_two :
    ∀ plaquette, plaquette ∈ unitCubeSurface →
      plaquette ∈ boxPlaquettes 2 := by
  intro plaquette hplaquette
  exact unitCubeSurface_mem_box (by omega) hplaquette

theorem refinedUnitCubeSurface_subset_box_four :
    ∀ plaquette, plaquette ∈ refinedUnitCubeSurface →
      plaquette ∈ boxPlaquettes 4 := by
  intro plaquette hplaquette
  exact dyadicSupportCells_subset_double_box
    unitCubeSurface_subset_box_two plaquette hplaquette

theorem refinedCubeCell_mem
    (face : CubeFaceIndex) (index : DyadicCellIndex) :
    dyadicCell (cubeFace face) index ∈ refinedUnitCubeSurface := by
  unfold refinedUnitCubeSurface
  apply (mem_dyadicSupportCells_iff unitCubeSurface _).mpr
  exact ⟨cubeFace face, cubeFace_mem_unitCubeSurface face,
    dyadicCell_mem_cells (cubeFace face) index⟩

/-! ## Internal-chain infrastructure -/

private def z4ChainInTrans {support : List Z4Plaq} :
    {first middle last : Z4Plaq} →
      ChainIn z4Chain.toLattice support first middle →
      ChainIn z4Chain.toLattice support middle last →
      ChainIn z4Chain.toLattice support first last
  | _, _, _, .refl _, right => right
  | _, _, _, .step adjacent hnext rest, right =>
      .step adjacent hnext (z4ChainInTrans rest right)

private def z4ChainInMono {small large : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ small → plaquette ∈ large) :
    {first last : Z4Plaq} →
      ChainIn z4Chain.toLattice small first last →
      ChainIn z4Chain.toLattice large first last
  | _, _, .refl plaquette => .refl plaquette
  | _, _, .step adjacent hnext rest =>
      .step adjacent (hsubset _ hnext) (z4ChainInMono hsubset rest)

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
            @YMGap.Continuum.PolymerModel.ChainIn.refl
              z4Chain.toLattice support first))

/-- Every pair of fine cells on one cube face is connected inside the full
refined cube boundary. -/
def refinedCubeWithinFaceChain
    (face : CubeFaceIndex) (startIndex endIndex : DyadicCellIndex) :
    ChainIn z4Chain.toLattice refinedUnitCubeSurface
      (dyadicCell (cubeFace face) startIndex)
      (dyadicCell (cubeFace face) endIndex) :=
  z4ChainInMono
    (fun plaquette hplaquette =>
      (mem_dyadicSupportCells_iff unitCubeSurface plaquette).mpr
        ⟨cubeFace face, cubeFace_mem_unitCubeSurface face, hplaquette⟩)
    (dyadicCellChain (cubeFace face) startIndex endIndex)

/-! ## Five explicit bridges joining the six refined faces -/

def refinedBottomFrontAdjacent :
    z4Chain.toLattice.Adjacent
      (dyadicCell (cubeFace .bottomXY) .origin)
      (dyadicCell (cubeFace .frontXZ) .origin) := by
  refine { link := ((0, 0, 0, 0), .x0), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def refinedBottomLeftAdjacent :
    z4Chain.toLattice.Adjacent
      (dyadicCell (cubeFace .bottomXY) .origin)
      (dyadicCell (cubeFace .leftYZ) .origin) := by
  refine { link := ((0, 0, 0, 0), .x1), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def refinedBottomSecondBackAdjacent :
    z4Chain.toLattice.Adjacent
      (dyadicCell (cubeFace .bottomXY) .second)
      (dyadicCell (cubeFace .backXZ) .origin) := by
  refine { link := ((0, 2, 0, 0), .x0), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def refinedBottomFirstRightAdjacent :
    z4Chain.toLattice.Adjacent
      (dyadicCell (cubeFace .bottomXY) .first)
      (dyadicCell (cubeFace .rightYZ) .origin) := by
  refine { link := ((2, 0, 0, 0), .x1), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def refinedFrontSecondTopAdjacent :
    z4Chain.toLattice.Adjacent
      (dyadicCell (cubeFace .frontXZ) .second)
      (dyadicCell (cubeFace .topXY) .origin) := by
  refine { link := ((0, 0, 2, 0), .x0), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def refinedCubeHub : Z4Plaq :=
  dyadicCell (cubeFace .bottomXY) .origin

/-- A concrete path from the origin cell of every refined face to the common
bottom-face hub. -/
def refinedCubeFaceOriginToHub :
    ∀ face : CubeFaceIndex,
      ChainIn z4Chain.toLattice refinedUnitCubeSurface
        (dyadicCell (cubeFace face) .origin) refinedCubeHub
  | .bottomXY => .refl _
  | .topXY =>
      .step (adjacentSymm refinedFrontSecondTopAdjacent)
        (refinedCubeCell_mem .frontXZ .second)
        (z4ChainInTrans
          (refinedCubeWithinFaceChain .frontXZ .second .origin)
          (.step (adjacentSymm refinedBottomFrontAdjacent)
            (refinedCubeCell_mem .bottomXY .origin) (.refl _)))
  | .frontXZ =>
      .step (adjacentSymm refinedBottomFrontAdjacent)
        (refinedCubeCell_mem .bottomXY .origin) (.refl _)
  | .backXZ =>
      .step (adjacentSymm refinedBottomSecondBackAdjacent)
        (refinedCubeCell_mem .bottomXY .second)
        (refinedCubeWithinFaceChain .bottomXY .second .origin)
  | .leftYZ =>
      .step (adjacentSymm refinedBottomLeftAdjacent)
        (refinedCubeCell_mem .bottomXY .origin) (.refl _)
  | .rightYZ =>
      .step (adjacentSymm refinedBottomFirstRightAdjacent)
        (refinedCubeCell_mem .bottomXY .first)
        (refinedCubeWithinFaceChain .bottomXY .first .origin)

def refinedCubeCellToHub
    (face : CubeFaceIndex) (index : DyadicCellIndex) :
    ChainIn z4Chain.toLattice refinedUnitCubeSurface
      (dyadicCell (cubeFace face) index) refinedCubeHub :=
  z4ChainInTrans (refinedCubeWithinFaceChain face index .origin)
    (refinedCubeFaceOriginToHub face)

def decodeRefinedCubeCell (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ refinedUnitCubeSurface) :
    Σ' face : CubeFaceIndex,
      Σ' index : DyadicCellIndex,
        dyadicCell (cubeFace face) index = plaquette := by
  unfold refinedUnitCubeSurface dyadicSupportCells at hplaquette
  obtain ⟨coarse, hcoarse, hlocal⟩ :=
    decodeFlatMapMember dyadicPlaquetteCells unitCubeSurface
      plaquette hplaquette
  have hcoarseMap : coarse ∈ cubeFaceIndices.map cubeFace := by
    rw [cubeFaceIndices_map]
    exact hcoarse
  obtain ⟨face, _, hface⟩ :=
    decodeMapMember cubeFace cubeFaceIndices coarse hcoarseMap
  rw [← hface] at hlocal
  unfold dyadicPlaquetteCells at hlocal
  obtain ⟨index, _, hindex⟩ :=
    decodeMapMember (dyadicCell (cubeFace face)) dyadicCellIndices
      plaquette hlocal
  exact ⟨face, index, hindex⟩

/-- The 24 refined cube faces form one genuine shared-link connected
polymer. -/
def refinedUnitCubeSurface_connected :
    connectedIn (L := z4Chain.toLattice) refinedUnitCubeSurface := by
  intro first last hfirst hlast
  obtain ⟨firstFace, firstIndex, hfirstEq⟩ :=
    decodeRefinedCubeCell first hfirst
  obtain ⟨lastFace, lastIndex, hlastEq⟩ :=
    decodeRefinedCubeCell last hlast
  rw [← hfirstEq, ← hlastEq]
  exact z4ChainInTrans
    (refinedCubeCellToHub firstFace firstIndex)
    (z4ChainInReverse (refinedCubeCellToHub lastFace lastIndex)
      (refinedCubeCell_mem lastFace lastIndex))

/-! ## Exact closed-boundary incidence -/

def refinedUnitCubeBoundaryMultiplicity (link : Z4Link) : Nat :=
  occurrenceCount link (refinedUnitCubeSurface.flatMap edgesOf)

/-- Every fine lattice link on the refined cube boundary occurs an even
number of times.  This is the exact gauge-closure fence missing from a single
dyadic plaquette patch. -/
theorem refinedUnitCubeBoundaryMultiplicity_even (link : Z4Link) :
    refinedUnitCubeBoundaryMultiplicity link % 2 = 0 := by
  simp [refinedUnitCubeBoundaryMultiplicity, refinedUnitCubeSurface,
    dyadicSupportCells, unitCubeSurface, dyadicPlaquetteCells,
    dyadicCellIndices, dyadicCell, dyadicVertex, edgesOf, dirsOf, addE,
    occurrenceCount]
  omega

/-- The 16 distinct side-two cube links parallel to coordinate zero. -/
def refinedCubeX0BoundaryLinks : List Z4Link :=
  [((0, 0, 0, 0), .x0), ((1, 0, 0, 0), .x0),
   ((0, 1, 0, 0), .x0), ((1, 1, 0, 0), .x0),
   ((0, 2, 0, 0), .x0), ((1, 2, 0, 0), .x0),
   ((0, 0, 1, 0), .x0), ((1, 0, 1, 0), .x0),
   ((0, 2, 1, 0), .x0), ((1, 2, 1, 0), .x0),
   ((0, 0, 2, 0), .x0), ((1, 0, 2, 0), .x0),
   ((0, 1, 2, 0), .x0), ((1, 1, 2, 0), .x0),
   ((0, 2, 2, 0), .x0), ((1, 2, 2, 0), .x0)]

/-- The 16 distinct side-two cube links parallel to coordinate one. -/
def refinedCubeX1BoundaryLinks : List Z4Link :=
  [((0, 0, 0, 0), .x1), ((1, 0, 0, 0), .x1),
   ((2, 0, 0, 0), .x1), ((0, 1, 0, 0), .x1),
   ((1, 1, 0, 0), .x1), ((2, 1, 0, 0), .x1),
   ((0, 0, 1, 0), .x1), ((0, 1, 1, 0), .x1),
   ((2, 0, 1, 0), .x1), ((2, 1, 1, 0), .x1),
   ((0, 0, 2, 0), .x1), ((1, 0, 2, 0), .x1),
   ((2, 0, 2, 0), .x1), ((0, 1, 2, 0), .x1),
   ((1, 1, 2, 0), .x1), ((2, 1, 2, 0), .x1)]

/-- The 16 distinct side-two cube links parallel to coordinate two. -/
def refinedCubeX2BoundaryLinks : List Z4Link :=
  [((0, 0, 0, 0), .x2), ((1, 0, 0, 0), .x2),
   ((2, 0, 0, 0), .x2), ((0, 0, 1, 0), .x2),
   ((1, 0, 1, 0), .x2), ((2, 0, 1, 0), .x2),
   ((0, 1, 0, 0), .x2), ((0, 1, 1, 0), .x2),
   ((2, 1, 0, 0), .x2), ((2, 1, 1, 0), .x2),
   ((0, 2, 0, 0), .x2), ((1, 2, 0, 0), .x2),
   ((2, 2, 0, 0), .x2), ((0, 2, 1, 0), .x2),
   ((1, 2, 1, 0), .x2), ((2, 2, 1, 0), .x2)]

/-- One copy of each of the 48 fine links on the side-two cube boundary. -/
def refinedCubeBoundaryLinks : List Z4Link :=
  refinedCubeX0BoundaryLinks ++
    refinedCubeX1BoundaryLinks ++ refinedCubeX2BoundaryLinks

theorem refinedCubeBoundaryLinks_length :
    refinedCubeBoundaryLinks.length = 48 := by
  rfl

theorem refinedCubeBoundaryLinks_nodup : refinedCubeBoundaryLinks.Nodup := by
  simp [refinedCubeBoundaryLinks, refinedCubeX0BoundaryLinks,
    refinedCubeX1BoundaryLinks, refinedCubeX2BoundaryLinks]

/-- The 96 raw boundary occurrences are exactly two copies of each of the 48
distinct fine links. -/
theorem refinedUnitCubeBoundaryMultiplicity_eq_twice (link : Z4Link) :
    refinedUnitCubeBoundaryMultiplicity link =
      2 * occurrenceCount link refinedCubeBoundaryLinks := by
  simp only [refinedUnitCubeBoundaryMultiplicity, refinedUnitCubeSurface,
    dyadicSupportCells, unitCubeSurface, dyadicPlaquetteCells,
    dyadicCellIndices, dyadicCell, dyadicVertex, edgesOf, dirsOf, addE,
    occurrenceCount, refinedCubeBoundaryLinks, refinedCubeX0BoundaryLinks,
    refinedCubeX1BoundaryLinks, refinedCubeX2BoundaryLinks,
    List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
    List.map_cons, List.map_nil, occurrenceCount_append,
    Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero,
    Nat.reduceAdd]
  omega

private theorem occurrenceCount_eq_zero_of_not_mem_local
    (link : Z4Link) : ∀ links : List Z4Link,
    link ∉ links → occurrenceCount link links = 0
  | [], _ => rfl
  | head :: tail, hnot => by
      have hhead : head ≠ link := by
        intro heq
        apply hnot
        rw [heq]
        exact List.mem_cons_self
      have htail : link ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      simp only [occurrenceCount, if_neg hhead, Nat.zero_add]
      exact occurrenceCount_eq_zero_of_not_mem_local link tail htail

private theorem occurrenceCount_le_one_of_nodup (link : Z4Link) :
    ∀ links : List Z4Link, links.Nodup →
      occurrenceCount link links ≤ 1
  | [], _ => by simp [occurrenceCount]
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hhead : head = link
      · subst head
        have hzero := occurrenceCount_eq_zero_of_not_mem_local
          link tail hparts.1
        simp only [occurrenceCount, hzero, if_true, Nat.add_zero]
        exact Nat.le_refl 1
      · simp only [occurrenceCount, if_neg hhead, Nat.zero_add]
        exact occurrenceCount_le_one_of_nodup link tail hparts.2

/-- No fine link is used by more than the two surface plaquettes that meet
there.  Together with evenness, every touched link therefore has incidence
exactly two. -/
theorem refinedUnitCubeBoundaryMultiplicity_le_two (link : Z4Link) :
    refinedUnitCubeBoundaryMultiplicity link ≤ 2 := by
  rw [refinedUnitCubeBoundaryMultiplicity_eq_twice]
  have hcount := occurrenceCount_le_one_of_nodup link
    refinedCubeBoundaryLinks refinedCubeBoundaryLinks_nodup
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

/-- Every actually occurring fine boundary link is used by exactly two
plaquettes. -/
theorem refinedUnitCubeBoundaryMultiplicity_eq_two_of_mem
    {link : Z4Link}
    (hlink : link ∈ refinedUnitCubeSurface.flatMap edgesOf) :
    refinedUnitCubeBoundaryMultiplicity link = 2 := by
  have hpositive := occurrenceCount_pos_of_mem_local link
    (refinedUnitCubeSurface.flatMap edgesOf) hlink
  have heven := refinedUnitCubeBoundaryMultiplicity_even link
  have hupper := refinedUnitCubeBoundaryMultiplicity_le_two link
  unfold refinedUnitCubeBoundaryMultiplicity at heven hupper ⊢
  omega

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

/-- The geometric incidence list at every touched refined-cube link has
length exactly two. -/
theorem refinedUnitCube_geometricIncidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks refinedUnitCubeSurface) :
    (geometricIncidentPlaquettes refinedUnitCubeSurface link).length = 2 := by
  have hraw : link ∈ refinedUnitCubeSurface.flatMap edgesOf := by
    unfold geometricTouchedLinks at hlink
    exact List.mem_eraseDups.mp hlink
  have htwo := refinedUnitCubeBoundaryMultiplicity_eq_two_of_mem hraw
  have hoccurrence := occurrenceCount_flatMap_edgesOf link
    refinedUnitCubeSurface
  have hfilter :=
    geometricIncidentPlaquettes_length_eq_faceIncidenceCount_local
      link refinedUnitCubeSurface
  unfold refinedUnitCubeBoundaryMultiplicity at htwo
  omega

/-! ## Canonical numerical carrier in the refined box -/

def dyadicUnitCubeSupportIds : List Nat :=
  dyadicSupportIds 2 unitCubeSurface

theorem dyadicUnitCubeSupportIds_length :
    dyadicUnitCubeSupportIds.length = 24 := by
  unfold dyadicUnitCubeSupportIds
  have hlength := dyadicSupportIds_length
    unitCubeSurface_subset_box_two unitCubeSurface_nodup
  rw [unitCubeSurface_length] at hlength
  exact hlength

theorem dyadicUnitCubeSupportIds_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 4 dyadicUnitCubeSupportIds)
      refinedUnitCubeSurface := by
  unfold dyadicUnitCubeSupportIds refinedUnitCubeSurface
  exact dyadicSupportIds_sameSupport unitCubeSurface_subset_box_two

/-- The closed connected side-two cube boundary is an actual canonical root
of the refined finite-box surface gas. -/
theorem dyadicUnitCubeSupportIds_mem_canonicalSurfacePolymers :
    dyadicUnitCubeSupportIds ∈ canonicalSurfacePolymers 4 := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · unfold dyadicUnitCubeSupportIds dyadicSupportIds
    exact geometricSupportIds_mem_cutoffOneFaceSupports
      4 refinedUnitCubeSurface
  · have hsame := dyadicUnitCubeSupportIds_sameSupport
    have hhub : refinedCubeHub ∈
        geometricPolymer 4 dyadicUnitCubeSupportIds :=
      hsame.2 _ (refinedCubeCell_mem .bottomXY .origin)
    obtain ⟨identifier, hidentifier, _⟩ :=
      decodeMapMember (boxPlaquetteAt 4) dyadicUnitCubeSupportIds
        refinedCubeHub hhub
    exact ⟨identifier, hidentifier⟩
  · unfold dyadicUnitCubeSupportIds dyadicSupportIds
    exact geometricSupportIds_connected
      refinedUnitCubeSurface_subset_box_four
      refinedUnitCubeSurface_connected

#print axioms cubeFace_mem_unitCubeSurface
#print axioms refinedUnitCubeSurface_length
#print axioms refinedUnitCubeSurface_nodup
#print axioms refinedUnitCubeSurface_subset_box_four
#print axioms refinedBottomFrontAdjacent
#print axioms refinedBottomSecondBackAdjacent
#print axioms refinedFrontSecondTopAdjacent
#print axioms refinedUnitCubeSurface_connected
#print axioms refinedUnitCubeBoundaryMultiplicity_even
#print axioms refinedCubeBoundaryLinks_nodup
#print axioms refinedUnitCubeBoundaryMultiplicity_eq_twice
#print axioms refinedUnitCubeBoundaryMultiplicity_le_two
#print axioms refinedUnitCubeBoundaryMultiplicity_eq_two_of_mem
#print axioms refinedUnitCube_geometricIncidentPlaquettes_length_eq_two
#print axioms dyadicUnitCubeSupportIds_length
#print axioms dyadicUnitCubeSupportIds_sameSupport
#print axioms dyadicUnitCubeSupportIds_mem_canonicalSurfacePolymers

end YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
