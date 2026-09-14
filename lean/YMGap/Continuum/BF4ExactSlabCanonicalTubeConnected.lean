/-
# A literal three-face strip prevents every original separating cut

The tube contains three consecutive temporal faces on one boundary edge.
Any original separator must place the first face on the lower-probe side;
each shared edge forces the next face to that side. The last face meets
the upper probe, contradicting disjointness. This proves acceptance by the
actual finite separator search, not a substitute connectedness predicate.
-/

import YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport

namespace YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabTubeSupportGeometry
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

theorem force_left {extent : Nat} {left right : List Z4Link} {ids : List Nat}
    (S : Separator extent left right ids) (id : Nat) (hi : id ∈ ids) (link : Z4Link)
    (hl : link ∈ left ++ faceLinks extent (cutLeft ids S.cut))
    (hf : link ∈ edgesOf (slabPlaquetteAt extent id)) : id ∈ S.cut := by
  by_cases hc : id ∈ S.cut
  · exact hc
  · apply False.elim
    apply S.disjoint link hl
    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨id,
      List.mem_filter.mpr ⟨hi,by simp only [decide_eq_false hc,Bool.not_false]⟩,hf⟩))

def stripFace (margin time : Nat) : Z4Plaq := ((1+margin,1+margin,1+margin,margin+time),.p03)
def stripEdge (margin time : Nat) : Z4Link := ((1+margin,1+margin,1+margin,margin+time),.x0)

theorem strip_mem (margin time : Nat) (ht : time < 3) : stripFace margin time ∈ tubeSides margin := by
  apply (tube_mem_iff margin _).mpr
  constructor
  · have hc : crosses (margin+time) (stripFace margin time) = true := decide_eq_true ⟨rfl,rfl⟩
    have he : time = 0 ∨ time = 1 ∨ time = 2 := by
      by_cases h0 : time = 0
      · exact Or.inl h0
      · by_cases h1 : time = 1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (by omega))
    rcases he with rfl | rfl | rfl
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hc)))
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr hc)))
    · exact Bool.or_eq_true_iff.mpr (Or.inr hc)
  · exact List.mem_cons_self

theorem strip_bottom (margin time : Nat) : stripEdge margin time ∈ edgesOf (stripFace margin time) :=
  List.mem_cons_self

theorem strip_top (margin time : Nat) : stripEdge margin (time+1) ∈ edgesOf (stripFace margin time) := by
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_cons.mpr
  apply Or.inl
  simp only [stripEdge,stripFace,dirsOf,addE,Nat.add_assoc]

def stripId (margin time : Nat) : Nat :=
  (boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf (stripFace margin time)

theorem stripId_pin (margin time : Nat) (ht : time < 3) :
    slabPlaquetteAt (responseExtent margin) (stripId margin time) = stripFace margin time :=
  face_lookup (tubeSides_physical margin _ (strip_mem margin time ht))

theorem stripId_mem (margin time : Nat) (ht : time < 3) : stripId margin time ∈ tubeIds margin := by
  apply (tubeIds_mem_iff margin _).mpr
  refine ⟨List.mem_range.mpr (List.idxOf_lt_length_of_mem
    (tubeSides_physical margin _ (strip_mem margin time ht))), ?_⟩
  rw [stripId_pin margin time ht]
  exact strip_mem margin time ht

theorem strip_region (margin time : Nat) (ht : time < 3)
    (S : Separator (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (tubeIds margin)) (hc : stripId margin time ∈ S.cut) :
    stripEdge margin (time+1) ∈ edgesOf (sliceFace margin 0) ++
      faceLinks (responseExtent margin) (cutLeft (tubeIds margin) S.cut) := by
  apply List.mem_append.mpr
  apply Or.inr
  exact List.mem_flatMap.mpr ⟨stripId margin time,
    List.mem_filter.mpr ⟨stripId_mem margin time ht,decide_eq_true hc⟩,
    by rw [stripId_pin margin time ht]; exact strip_top margin time⟩

theorem tube_no_separator (margin : Nat)
    (S : Separator (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (tubeIds margin)) : False := by
  have hbottom : stripEdge margin 0 ∈ edgesOf (sliceFace margin 0) := List.mem_cons_self
  have htop : stripEdge margin 3 ∈ edgesOf (sliceFace margin 3) := List.mem_cons_self
  have h0 := force_left S _ (stripId_mem margin 0 (by decide)) (stripEdge margin 0)
    (List.mem_append.mpr (Or.inl hbottom))
    (by rw [stripId_pin margin 0 (by decide)]; exact strip_bottom margin 0)
  have h1 := force_left S _ (stripId_mem margin 1 (by decide)) (stripEdge margin 1)
    (strip_region margin 0 (by decide) S h0)
    (by rw [stripId_pin margin 1 (by decide)]; exact strip_bottom margin 1)
  have h2 := force_left S _ (stripId_mem margin 2 (by decide)) (stripEdge margin 2)
    (strip_region margin 1 (by decide) S h1)
    (by rw [stripId_pin margin 2 (by decide)]; exact strip_bottom margin 2)
  exact S.disjoint (stripEdge margin 3) (strip_region margin 2 (by decide) S h2)
    (List.mem_append.mpr (Or.inl htop))

theorem tube_connected_keep (margin : Nat) : keep (responseExtent margin)
    (edgesOf (sliceFace margin 0)) (edgesOf (sliceFace margin 3)) (tubeIds margin) = true := by
  cases he : findSeparator (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (tubeIds margin) with
  | none => simp only [keep,he,Option.isNone]
  | some S => exact False.elim (tube_no_separator margin S)

theorem tubeIds_connected (margin : Nat) : tubeIds margin ∈
    connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)) :=
  List.mem_filter.mpr ⟨tubeIds_selected margin,tube_connected_keep margin⟩

end YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected

#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.force_left
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.stripFace
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.stripEdge
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.strip_mem
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.strip_bottom
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.strip_top
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.stripId
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.stripId_pin
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.stripId_mem
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.strip_region
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.tube_no_separator
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.tube_connected_keep
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected.tubeIds_connected
