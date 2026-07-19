/-
# Small closed fixed-face carriers in the radius-zero adjacent-even plane

This leaf banks two literal finite geometries for the next oriented
Haar-versus-spin comparison.

The first carrier is one elementary spatial cube at the fixed time slice.  It
has six fixed faces, twelve distinct touched links, and incidence two at every
touched link.

The second carrier is the union of two face-disjoint elementary cubes meeting
along one edge.  It has twelve fixed faces and twenty-three distinct touched
links.  The shared edge has incidence four and every other touched link has
incidence two.

All statements are small finite geometry.  They do not evaluate a density
polynomial or a state space, identify a Haar moment, assert a spin amplitude,
or prove that either carrier is minimal among all closed lattice surfaces.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
import YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceDensitySOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The elementary cube in the radius-zero fixed plane -/

/-- The six fixed-face identifiers of the elementary cube based at the
spatial origin of the radius-zero fixed slice. -/
def radiusZeroElementaryCubeFaceIds : List Nat :=
  [6, 7, 9, 21, 52, 144]

/-- The same six faces as literal fixed-time spatial plaquettes. -/
def radiusZeroElementaryCubeFaces : List Z4Plaq :=
  [((0, 0, 0, 1), .p01), ((0, 0, 0, 1), .p02),
   ((0, 0, 0, 1), .p12), ((0, 0, 1, 1), .p01),
   ((0, 1, 0, 1), .p02), ((1, 0, 0, 1), .p12)]

theorem radiusZeroElementaryCubeFaceIds_length :
    radiusZeroElementaryCubeFaceIds.length = 6 := by
  decide

theorem radiusZeroElementaryCubeFaceIds_nodup :
    radiusZeroElementaryCubeFaceIds.Nodup := by
  decide

theorem radiusZeroElementaryCubeFaces_length :
    radiusZeroElementaryCubeFaces.length = 6 := by
  decide

theorem radiusZeroElementaryCubeFaces_nodup :
    radiusZeroElementaryCubeFaces.Nodup := by
  decide

/-- Decoding the six audited identifiers through the production slab
enumeration gives exactly the displayed elementary-cube face list. -/
theorem radiusZeroElementaryCubeFaces_eq_decodeIds :
    radiusZeroElementaryCubeFaces =
      radiusZeroElementaryCubeFaceIds.map
        (slabPlaquetteAt (adjacentEvenExtent 0)) := by
  decide

/-- Every audited identifier is an actual production fixed-face identifier at
radius zero. -/
theorem radiusZeroElementaryCubeFaceId_fixed
    {id : Nat} (hid : id ∈ radiusZeroElementaryCubeFaceIds) :
    id ∈ adjacentEvenFixedFaceIds 0 := by
  simp only [radiusZeroElementaryCubeFaceIds, List.mem_cons,
    List.not_mem_nil, or_false] at hid
  rcases hid with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- Every literal elementary-cube face occurs in the production fixed-face
list. -/
theorem radiusZeroElementaryCubeFace_fixed
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ radiusZeroElementaryCubeFaces) :
    plaquette ∈ adjacentEvenFixedFacePlaquettes 0 := by
  rw [radiusZeroElementaryCubeFaces_eq_decodeIds] at hplaquette
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hplaquette
  unfold adjacentEvenFixedFacePlaquettes
  exact List.mem_map.mpr
    ⟨id, radiusZeroElementaryCubeFaceId_fixed hid, rfl⟩

/-- The duplicate-free physical-link support of the elementary cube. -/
def radiusZeroElementaryCubeTouchedLinks : List Z4Link :=
  geometricTouchedLinks radiusZeroElementaryCubeFaces

theorem radiusZeroElementaryCubeTouchedLinks_length :
    radiusZeroElementaryCubeTouchedLinks.length = 12 := by
  decide

theorem radiusZeroElementaryCubeTouchedLinks_nodup :
    radiusZeroElementaryCubeTouchedLinks.Nodup := by
  exact geometricTouchedLinks_nodup radiusZeroElementaryCubeFaces

/-- Every touched cube link lies in the production active-link carrier. -/
theorem radiusZeroElementaryCubeTouchedLink_active
    {link : Z4Link}
    (hlink : link ∈ radiusZeroElementaryCubeTouchedLinks) :
    link ∈ adjacentEvenActiveLinks 0 := by
  unfold radiusZeroElementaryCubeTouchedLinks at hlink
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hedge⟩ := hlink
  exact adjacentEvenFixedFacePlaquette_edge_mem_activeLinks
    (radiusZeroElementaryCubeFace_fixed hplaquette) hedge

/-- Every one of the twelve touched cube links is incident on exactly two of
the six selected fixed faces. -/
theorem radiusZeroElementaryCube_incidence_two
    {link : Z4Link}
    (hlink : link ∈ radiusZeroElementaryCubeTouchedLinks) :
    (geometricIncidentPlaquettes
      radiusZeroElementaryCubeFaces link).length = 2 := by
  unfold radiusZeroElementaryCubeTouchedLinks at hlink
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hedge⟩ := hlink
  simp only [radiusZeroElementaryCubeFaces, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl <;> decide

/-! ## 2. Two face-disjoint cubes sharing one fixed edge -/

/-- The twelve fixed-face identifiers of the two edge-touching cubes. -/
def radiusZeroEdgeTouchingDoubleCubeFaceIds : List Nat :=
  [6, 7, 9, 21, 52, 66, 67, 69, 81, 112, 144, 204]

/-- The corresponding twelve literal fixed-time spatial plaquettes. -/
def radiusZeroEdgeTouchingDoubleCubeFaces : List Z4Plaq :=
  [((0, 0, 0, 1), .p01), ((0, 0, 0, 1), .p02),
   ((0, 0, 0, 1), .p12), ((0, 0, 1, 1), .p01),
   ((0, 1, 0, 1), .p02), ((0, 1, 1, 1), .p01),
   ((0, 1, 1, 1), .p02), ((0, 1, 1, 1), .p12),
   ((0, 1, 2, 1), .p01), ((0, 2, 1, 1), .p02),
   ((1, 0, 0, 1), .p12), ((1, 1, 1, 1), .p12)]

theorem radiusZeroEdgeTouchingDoubleCubeFaceIds_length :
    radiusZeroEdgeTouchingDoubleCubeFaceIds.length = 12 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaceIds_nodup :
    radiusZeroEdgeTouchingDoubleCubeFaceIds.Nodup := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaces_length :
    radiusZeroEdgeTouchingDoubleCubeFaces.length = 12 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaces_nodup :
    radiusZeroEdgeTouchingDoubleCubeFaces.Nodup := by
  decide

/-- The production slab decoder sends the twelve audited identifiers to the
displayed double-cube face list. -/
theorem radiusZeroEdgeTouchingDoubleCubeFaces_eq_decodeIds :
    radiusZeroEdgeTouchingDoubleCubeFaces =
      radiusZeroEdgeTouchingDoubleCubeFaceIds.map
        (slabPlaquetteAt (adjacentEvenExtent 0)) := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaceId_fixed
    {id : Nat} (hid : id ∈ radiusZeroEdgeTouchingDoubleCubeFaceIds) :
    id ∈ adjacentEvenFixedFaceIds 0 := by
  simp only [radiusZeroEdgeTouchingDoubleCubeFaceIds, List.mem_cons,
    List.not_mem_nil, or_false] at hid
  rcases hid with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem radiusZeroEdgeTouchingDoubleCubeFace_fixed
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ radiusZeroEdgeTouchingDoubleCubeFaces) :
    plaquette ∈ adjacentEvenFixedFacePlaquettes 0 := by
  rw [radiusZeroEdgeTouchingDoubleCubeFaces_eq_decodeIds] at hplaquette
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hplaquette
  unfold adjacentEvenFixedFacePlaquettes
  exact List.mem_map.mpr
    ⟨id, radiusZeroEdgeTouchingDoubleCubeFaceId_fixed hid, rfl⟩

/-- The one edge common to both elementary-cube boundaries. -/
def radiusZeroEdgeTouchingDoubleCubeSharedLink : Z4Link :=
  ((0, 1, 1, 1), .x0)

/-- The duplicate-free physical-link support of the double cube. -/
def radiusZeroEdgeTouchingDoubleCubeTouchedLinks : List Z4Link :=
  geometricTouchedLinks radiusZeroEdgeTouchingDoubleCubeFaces

theorem radiusZeroEdgeTouchingDoubleCubeTouchedLinks_length :
    radiusZeroEdgeTouchingDoubleCubeTouchedLinks.length = 23 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeTouchedLinks_nodup :
    radiusZeroEdgeTouchingDoubleCubeTouchedLinks.Nodup := by
  exact geometricTouchedLinks_nodup
    radiusZeroEdgeTouchingDoubleCubeFaces

theorem radiusZeroEdgeTouchingDoubleCubeTouchedLink_active
    {link : Z4Link}
    (hlink : link ∈ radiusZeroEdgeTouchingDoubleCubeTouchedLinks) :
    link ∈ adjacentEvenActiveLinks 0 := by
  unfold radiusZeroEdgeTouchingDoubleCubeTouchedLinks at hlink
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hedge⟩ := hlink
  exact adjacentEvenFixedFacePlaquette_edge_mem_activeLinks
    (radiusZeroEdgeTouchingDoubleCubeFace_fixed hplaquette) hedge

theorem radiusZeroEdgeTouchingDoubleCubeSharedLink_mem_touched :
    radiusZeroEdgeTouchingDoubleCubeSharedLink ∈
      radiusZeroEdgeTouchingDoubleCubeTouchedLinks := by
  decide

/-- The common edge is incident on four selected faces. -/
theorem radiusZeroEdgeTouchingDoubleCubeSharedLink_incidence_four :
    (geometricIncidentPlaquettes
      radiusZeroEdgeTouchingDoubleCubeFaces
      radiusZeroEdgeTouchingDoubleCubeSharedLink).length = 4 := by
  decide

/-- Every touched edge other than the common edge is bivalent. -/
theorem radiusZeroEdgeTouchingDoubleCube_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈ radiusZeroEdgeTouchingDoubleCubeTouchedLinks)
    (hne : link ≠ radiusZeroEdgeTouchingDoubleCubeSharedLink) :
    (geometricIncidentPlaquettes
      radiusZeroEdgeTouchingDoubleCubeFaces link).length = 2 := by
  unfold radiusZeroEdgeTouchingDoubleCubeTouchedLinks at hlink
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hedge⟩ := hlink
  simp only [radiusZeroEdgeTouchingDoubleCubeFaces, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl <;>
      simp [radiusZeroEdgeTouchingDoubleCubeSharedLink, dirsOf, addE] at hne <;>
      decide

/-- Among touched links, incidence four uniquely identifies the displayed
common edge. -/
theorem radiusZeroEdgeTouchingDoubleCube_unique_incidence_four
    {link : Z4Link}
    (hlink : link ∈ radiusZeroEdgeTouchingDoubleCubeTouchedLinks)
    (hfour : (geometricIncidentPlaquettes
      radiusZeroEdgeTouchingDoubleCubeFaces link).length = 4) :
    link = radiusZeroEdgeTouchingDoubleCubeSharedLink := by
  by_cases heq : link = radiusZeroEdgeTouchingDoubleCubeSharedLink
  · exact heq
  · have htwo :=
      radiusZeroEdgeTouchingDoubleCube_other_incidence_two hlink heq
    omega

#print axioms radiusZeroElementaryCubeFaces_eq_decodeIds
#print axioms radiusZeroElementaryCubeFaceId_fixed
#print axioms radiusZeroElementaryCubeFace_fixed
#print axioms radiusZeroElementaryCubeTouchedLinks_length
#print axioms radiusZeroElementaryCubeTouchedLink_active
#print axioms radiusZeroElementaryCube_incidence_two
#print axioms radiusZeroEdgeTouchingDoubleCubeFaces_eq_decodeIds
#print axioms radiusZeroEdgeTouchingDoubleCubeFaceId_fixed
#print axioms radiusZeroEdgeTouchingDoubleCubeFace_fixed
#print axioms radiusZeroEdgeTouchingDoubleCubeTouchedLinks_length
#print axioms radiusZeroEdgeTouchingDoubleCubeTouchedLink_active
#print axioms radiusZeroEdgeTouchingDoubleCubeSharedLink_incidence_four
#print axioms radiusZeroEdgeTouchingDoubleCube_other_incidence_two
#print axioms radiusZeroEdgeTouchingDoubleCube_unique_incidence_four

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence
