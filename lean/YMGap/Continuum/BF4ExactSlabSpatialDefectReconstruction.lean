/-
# Original all-spin moments: spatial defects reconstruct temporal bits

The actual moment checker implies the odd-face charge equation at every
lattice link, including links outside the finite physical slab. Hence the
explicit temporal decoder applies without a fundamental-label or window
restriction. Equal spatial odd-face data determine all original physical
label parities; together with each label's quotient by two they determine
the labels themselves. This is an injective encoding, not a count of its
image, a Haar sign statement, or a bound on the short signed remainder.
-/

import YMGap.Continuum.Z4SpatialDefectTemporalDecoder
import YMGap.Continuum.BF4ExactSlabTubeSupportGeometry

namespace YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.BF4ExactSlabCenterCharge
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabMinimalMomentParity
open YMGap.Continuum.BF4ExactSlabTubeSupportGeometry

theorem moment_odd_geometry_parity (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hc : momentCheck margin lo hi state = true) (link : Z4Link) :
    (endpointCharge margin lo hi link +
      faceIncidenceCount link (oddFaces (responseExtent margin) state)) % 2 = 0 := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks (responseExtent margin)
  · have hh := List.all_eq_true.mp hc ((boundaryCompleteSlabLinks (responseExtent margin)).idxOf link)
      (List.mem_range.mpr (List.idxOf_lt_length_of_mem hl))
    have hp := of_decide_eq_true hh
    change (charges margin lo hi _ + totalCharge (responseExtent margin) _ state) % 2 = 0 at hp
    have hcharges : charges margin lo hi ((boundaryCompleteSlabLinks (responseExtent margin)).idxOf link) =
        endpointCharge margin lo hi link := by
      unfold charges endpointCharge
      rw [faceDegree_pin _ _ _ hl (slice_physical margin ⟨0,by decide⟩),
        faceDegree_pin _ _ _ hl (slice_physical margin ⟨3,by decide⟩)]
    rw [hcharges, Nat.add_mod, totalCharge_parity (responseExtent margin) state link hl] at hp
    rw [Nat.add_mod]
    exact hp
  · have h0 : link ∉ edgesOf (sliceFace margin 0) := fun h => hl
      ((mem_boundaryCompleteSlabLinks_iff _ _).mpr ⟨_,slice_physical margin ⟨0,by decide⟩,h⟩)
    have h3 : link ∉ edgesOf (sliceFace margin 3) := fun h => hl
      ((mem_boundaryCompleteSlabLinks_iff _ _).mpr ⟨_,slice_physical margin ⟨3,by decide⟩,h⟩)
    rw [incidence_outside (responseExtent margin) link hl _ (fun _ hf => oddFaces_physical hf)]
    cases lo <;> cases hi <;> simp [endpointCharge, h0, h3]

def spatialOddFaces (margin : Nat) (state : EdgeLabelling) : List Z4Plaq :=
  spatialFaces (oddFaces (responseExtent margin) state)

theorem moment_temporal_bit (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hc : momentCheck margin lo hi state = true) (link : Z4Link) (hd : link.2 ≠ .x3)
    (time : Nat) :
    cutCount time link (oddFaces (responseExtent margin) state) =
      temporalBit (fun t => endpointCharge margin lo hi (atTime t link))
        (fun t => faceIncidenceCount (atTime t link) (spatialOddFaces margin state)) time :=
  cutCount_decode _ link hd _ (oddFaces_nodup _ state)
    (fun t => moment_odd_geometry_parity margin lo hi state hc (atTime t link)) time

theorem cutEdge_spatial (face : Z4Plaq) : (cutEdge face).2 ≠ Dir4.x3 := by
  rcases face with ⟨v,p⟩
  cases p <;> dsimp only [cutEdge, dirsOf] <;> decide

theorem moment_temporal_face_iff (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hc : momentCheck margin lo hi state = true) (face : Z4Plaq)
    (ht : (dirsOf face.2).2 = Dir4.x3) :
    face ∈ oddFaces (responseExtent margin) state ↔
      temporalBit (fun t => endpointCharge margin lo hi (atTime t (cutEdge face)))
        (fun t => faceIncidenceCount (atTime t (cutEdge face)) (spatialOddFaces margin state))
        face.1.2.2.2 = 1 := by
  rw [temporal_face_mem_iff_count _ (oddFaces_nodup _ state) face ht,
    moment_temporal_bit margin lo hi state hc _ (cutEdge_spatial face)]

theorem spatial_odd_determine_membership (margin : Nat) (lo hi : Bool)
    (left right : EdgeLabelling)
    (hl : momentCheck margin lo hi left = true) (hr : momentCheck margin lo hi right = true)
    (hs : spatialOddFaces margin left = spatialOddFaces margin right) (face : Z4Plaq) :
    face ∈ oddFaces (responseExtent margin) left ↔ face ∈ oddFaces (responseExtent margin) right := by
  by_cases ht : (dirsOf face.2).2 = Dir4.x3
  · rw [moment_temporal_face_iff margin lo hi left hl face ht,
      moment_temporal_face_iff margin lo hi right hr face ht, hs]
  · constructor
    · intro hf
      have hm : face ∈ spatialOddFaces margin left := List.mem_filter.mpr ⟨hf,decide_eq_true ht⟩
      rw [hs] at hm
      exact (List.mem_filter.mp hm).1
    · intro hf
      have hm : face ∈ spatialOddFaces margin right := List.mem_filter.mpr ⟨hf,decide_eq_true ht⟩
      rw [← hs] at hm
      exact (List.mem_filter.mp hm).1

theorem spatial_odd_determine_face_parity (margin : Nat) (lo hi : Bool)
    (left right : EdgeLabelling)
    (hl : momentCheck margin lo hi left = true) (hr : momentCheck margin lo hi right = true)
    (hs : spatialOddFaces margin left = spatialOddFaces margin right) (face : Z4Plaq)
    (hf : face ∈ boundaryCompleteSlabPlaquettes (responseExtent margin)) :
    left ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) % 2 =
      right ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) % 2 := by
  have hm := spatial_odd_determine_membership margin lo hi left right hl hr hs face
  have ho : left ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) % 2 = 1 ↔
      right ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) % 2 = 1 := by
    constructor
    · intro h
      exact of_decide_eq_true (List.mem_filter.mp (hm.mp (List.mem_filter.mpr ⟨hf,decide_eq_true h⟩))).2
    · intro h
      exact of_decide_eq_true (List.mem_filter.mp (hm.mpr (List.mem_filter.mpr ⟨hf,decide_eq_true h⟩))).2
  by_cases h : left ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) % 2 = 1
  · exact h.trans (ho.mp h).symm
  · have hn : right ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) % 2 ≠ 1 :=
      fun h' => h (ho.mpr h')
    clear ho hm
    omega

/-- The spatial parity data plus the higher-label quotients encode the original labels injectively. -/
theorem spatial_and_higher_determine_face_label (margin : Nat) (lo hi : Bool)
    (left right : EdgeLabelling)
    (hl : momentCheck margin lo hi left = true) (hr : momentCheck margin lo hi right = true)
    (hs : spatialOddFaces margin left = spatialOddFaces margin right) (face : Z4Plaq)
    (hf : face ∈ boundaryCompleteSlabPlaquettes (responseExtent margin))
    (hq : left ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) / 2 =
      right ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) / 2) :
    left ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) =
      right ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) := by
  have hp := spatial_odd_determine_face_parity margin lo hi left right hl hr hs face hf
  omega

end YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction

#print axioms YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction.moment_odd_geometry_parity
#print axioms YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction.spatialOddFaces
#print axioms YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction.moment_temporal_bit
#print axioms YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction.cutEdge_spatial
#print axioms YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction.moment_temporal_face_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction.spatial_odd_determine_membership
#print axioms YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction.spatial_odd_determine_face_parity
#print axioms YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction.spatial_and_higher_determine_face_label
