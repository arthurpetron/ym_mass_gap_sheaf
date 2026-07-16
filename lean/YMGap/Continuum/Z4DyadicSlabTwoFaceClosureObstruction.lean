/-
# The adjacent two-face slab component is not a closed physical block

The coupled two-face conditional law correctly postpones normalization until
after its one shared production link has been glued.  Geometrically, however,
the two incident plaquettes still have six unpaired boundary links.  This file
banks that obstruction as an exact incidence count.

It also identifies the first closed carrier already present in the local
geometry.  Among selections from the six faces of the elementary cube, the
even-incidence condition forces every selected face bit to agree.  Hence a
closed selection containing the coupled bottom/front pair is the complete
six-face cube boundary.  The minimality claim here is deliberately local to
subpackets of that explicit cube; no global classification of lattice
2-cycles is asserted.
-/

import YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
import YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry

namespace YMGap.Continuum.Z4DyadicSlabTwoFaceClosureObstruction

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. A literal adjacent pair and its dangling edge -/

/-- The same bottom/front adjacent pair represented by the two-face
shared-link component. -/
def adjacentTwoFaceSupport : List Z4Plaq :=
  [cubeFace .bottomXY, cubeFace .frontXZ]

def adjacentTwoFaceSharedLink : Z4Link :=
  ((0, 0, 0, 0), .x0)

def adjacentTwoFaceDanglingLink : Z4Link :=
  ((0, 1, 0, 0), .x0)

theorem adjacentTwoFaceSupport_length :
    adjacentTwoFaceSupport.length = 2 := by
  rfl

theorem adjacentTwoFaceSupport_nodup :
    adjacentTwoFaceSupport.Nodup := by
  simp [adjacentTwoFaceSupport, cubeFace]

/-- The intended gluing edge really has degree two in the pair. -/
theorem adjacentTwoFaceSharedLink_incidence_two :
    faceIncidenceCount adjacentTwoFaceSharedLink
      adjacentTwoFaceSupport = 2 := by
  rfl

/-- A displayed outer edge has degree one, so the other boundary links have
not disappeared merely because the common edge was glued. -/
theorem adjacentTwoFaceDanglingLink_incidence_one :
    faceIncidenceCount adjacentTwoFaceDanglingLink
      adjacentTwoFaceSupport = 1 := by
  rfl

theorem adjacentTwoFaceSupport_not_evenFaceIncidence :
    ¬ EvenFaceIncidence adjacentTwoFaceSupport := by
  intro hclosed
  have heven := hclosed adjacentTwoFaceDanglingLink
  rw [adjacentTwoFaceDanglingLink_incidence_one] at heven
  cases heven

/-! ## 2. Face selections inside the elementary cube -/

def selectedCubeFaces
    (selected : CubeFaceIndex → Bool) : List Z4Plaq :=
  (cubeFaceIndices.filter selected).map cubeFace

def selectedBit (selected : CubeFaceIndex → Bool)
    (face : CubeFaceIndex) : Nat :=
  if selected face then 1 else 0

private def selectedFaceIncidenceTerm
    (link : Z4Link) (selected : CubeFaceIndex → Bool)
    (face : CubeFaceIndex) : Nat :=
  if selected face then
    if link ∈ edgesOf (cubeFace face) then 1 else 0
  else 0

private def selectedFaceIncidenceSum
    (link : Z4Link) (selected : CubeFaceIndex → Bool) :
    List CubeFaceIndex → Nat
  | [] => 0
  | face :: rest =>
      selectedFaceIncidenceTerm link selected face +
        selectedFaceIncidenceSum link selected rest

private theorem faceIncidenceCount_map_filter_cubeFace
    (link : Z4Link) (selected : CubeFaceIndex → Bool) :
    ∀ faces : List CubeFaceIndex,
      faceIncidenceCount link ((faces.filter selected).map cubeFace) =
        selectedFaceIncidenceSum link selected faces
  | [] => rfl
  | face :: rest => by
      cases hselected : selected face <;>
        simp [hselected, faceIncidenceCount, selectedFaceIncidenceSum,
          selectedFaceIncidenceTerm,
          faceIncidenceCount_map_filter_cubeFace link selected rest]

private theorem faceIncidenceCount_selectedCubeFaces
    (link : Z4Link) (selected : CubeFaceIndex → Bool) :
    faceIncidenceCount link (selectedCubeFaces selected) =
      selectedFaceIncidenceSum link selected cubeFaceIndices := by
  exact faceIncidenceCount_map_filter_cubeFace link selected cubeFaceIndices

private theorem selectedBit_pair_even_iff
    (left right : Bool) :
    ((if left then 1 else 0) + (if right then 1 else 0)) % 2 = 0 ↔
      left = right := by
  cases left <;> cases right <;> simp

theorem selectedCubeFaces_bottomFront_incidence
    (selected : CubeFaceIndex → Bool) :
    faceIncidenceCount ((0, 0, 0, 0), .x0)
        (selectedCubeFaces selected) =
      selectedBit selected .bottomXY +
        selectedBit selected .frontXZ := by
  rw [faceIncidenceCount_selectedCubeFaces]
  simp [selectedFaceIncidenceSum, selectedFaceIncidenceTerm, selectedBit,
    cubeFaceIndices, cubeFace, edgesOf, dirsOf, addE]

theorem selectedCubeFaces_bottomLeft_incidence
    (selected : CubeFaceIndex → Bool) :
    faceIncidenceCount ((0, 0, 0, 0), .x1)
        (selectedCubeFaces selected) =
      selectedBit selected .bottomXY +
        selectedBit selected .leftYZ := by
  rw [faceIncidenceCount_selectedCubeFaces]
  simp [selectedFaceIncidenceSum, selectedFaceIncidenceTerm, selectedBit,
    cubeFaceIndices, cubeFace, edgesOf, dirsOf, addE]

theorem selectedCubeFaces_bottomBack_incidence
    (selected : CubeFaceIndex → Bool) :
    faceIncidenceCount ((0, 1, 0, 0), .x0)
        (selectedCubeFaces selected) =
      selectedBit selected .bottomXY +
        selectedBit selected .backXZ := by
  rw [faceIncidenceCount_selectedCubeFaces]
  simp [selectedFaceIncidenceSum, selectedFaceIncidenceTerm, selectedBit,
    cubeFaceIndices, cubeFace, edgesOf, dirsOf, addE]

theorem selectedCubeFaces_bottomRight_incidence
    (selected : CubeFaceIndex → Bool) :
    faceIncidenceCount ((1, 0, 0, 0), .x1)
        (selectedCubeFaces selected) =
      selectedBit selected .bottomXY +
        selectedBit selected .rightYZ := by
  rw [faceIncidenceCount_selectedCubeFaces]
  simp [selectedFaceIncidenceSum, selectedFaceIncidenceTerm, selectedBit,
    cubeFaceIndices, cubeFace, edgesOf, dirsOf, addE]

theorem selectedCubeFaces_frontTop_incidence
    (selected : CubeFaceIndex → Bool) :
    faceIncidenceCount ((0, 0, 1, 0), .x0)
        (selectedCubeFaces selected) =
      selectedBit selected .frontXZ +
        selectedBit selected .topXY := by
  rw [faceIncidenceCount_selectedCubeFaces]
  simp [selectedFaceIncidenceSum, selectedFaceIncidenceTerm, selectedBit,
    cubeFaceIndices, cubeFace, edgesOf, dirsOf, addE]
  omega

/-- Inside the elementary cube carrier, closure propagates one face choice
through the connected face-adjacency graph. -/
theorem evenFaceIncidence_selectedCubeFaces_all_equal
    (selected : CubeFaceIndex → Bool)
    (hclosed : EvenFaceIncidence (selectedCubeFaces selected)) :
    ∀ face, selected face = selected .bottomXY := by
  have hbottomFront :
      selected .bottomXY = selected .frontXZ := by
    have heven := hclosed ((0, 0, 0, 0), .x0)
    rw [selectedCubeFaces_bottomFront_incidence] at heven
    exact (selectedBit_pair_even_iff _ _).mp heven
  have hbottomLeft :
      selected .bottomXY = selected .leftYZ := by
    have heven := hclosed ((0, 0, 0, 0), .x1)
    rw [selectedCubeFaces_bottomLeft_incidence] at heven
    exact (selectedBit_pair_even_iff _ _).mp heven
  have hbottomBack :
      selected .bottomXY = selected .backXZ := by
    have heven := hclosed ((0, 1, 0, 0), .x0)
    rw [selectedCubeFaces_bottomBack_incidence] at heven
    exact (selectedBit_pair_even_iff _ _).mp heven
  have hbottomRight :
      selected .bottomXY = selected .rightYZ := by
    have heven := hclosed ((1, 0, 0, 0), .x1)
    rw [selectedCubeFaces_bottomRight_incidence] at heven
    exact (selectedBit_pair_even_iff _ _).mp heven
  have hfrontTop : selected .frontXZ = selected .topXY := by
    have heven := hclosed ((0, 0, 1, 0), .x0)
    rw [selectedCubeFaces_frontTop_incidence] at heven
    exact (selectedBit_pair_even_iff _ _).mp heven
  intro face
  cases face
  · rfl
  · exact Eq.trans hfrontTop.symm hbottomFront.symm
  · exact hbottomFront.symm
  · exact hbottomBack.symm
  · exact hbottomLeft.symm
  · exact hbottomRight.symm

/-- Any closed cube subpacket containing the adjacent pair contains every
cube face. -/
theorem closedCubeSelection_containing_pair_selects_all
    (selected : CubeFaceIndex → Bool)
    (hclosed : EvenFaceIncidence (selectedCubeFaces selected))
    (hbottom : selected .bottomXY = true)
    (hfront : selected .frontXZ = true) :
    ∀ face, selected face = true := by
  have hpresent : selected .bottomXY = true ∧
      selected .frontXZ = true := ⟨hbottom, hfront⟩
  intro face
  rw [evenFaceIncidence_selectedCubeFaces_all_equal selected hclosed face]
  exact hpresent.1

theorem closedCubeSelection_containing_pair_length_six
    (selected : CubeFaceIndex → Bool)
    (hclosed : EvenFaceIncidence (selectedCubeFaces selected))
    (hbottom : selected .bottomXY = true)
    (hfront : selected .frontXZ = true) :
    (selectedCubeFaces selected).length = 6 := by
  have hall := closedCubeSelection_containing_pair_selects_all
    selected hclosed hbottom hfront
  simp [selectedCubeFaces, cubeFaceIndices, hall]

/-! ## 3. The resulting closed carrier -/

theorem unitCubeSurface_is_closed_six_face_carrier :
    unitCubeSurface.length = 6 ∧
      unitCubeSurface.Nodup ∧
      EvenFaceIncidence unitCubeSurface := by
  exact ⟨unitCubeSurface_length, unitCubeSurface_nodup,
    unitCubeSurface_evenFaceIncidence⟩

#print axioms adjacentTwoFaceSharedLink_incidence_two
#print axioms adjacentTwoFaceDanglingLink_incidence_one
#print axioms adjacentTwoFaceSupport_not_evenFaceIncidence
#print axioms evenFaceIncidence_selectedCubeFaces_all_equal
#print axioms closedCubeSelection_containing_pair_selects_all
#print axioms closedCubeSelection_containing_pair_length_six
#print axioms unitCubeSurface_is_closed_six_face_carrier

end YMGap.Continuum.Z4DyadicSlabTwoFaceClosureObstruction
