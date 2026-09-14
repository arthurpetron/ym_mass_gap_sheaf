/-
# Twelve selected faces, counting overlapping replicas only once

An occupied replica cut embeds in the selected support's cut. At each
of the three intervening times, original connectedness supplies an
occupied replica and its original leaf filter supplies four distinct
edges. Disjoint times give twelve selected faces, not merely twelve
replica occurrences. No coefficient sign or response floor is asserted.
-/

import YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport

namespace YMGap.Continuum.BF4ExactSlabRetainedSelectedArea

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabConnectedReplicaArea
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.PairedPositiveFaceLabellings

theorem positive_face_selected {extent : Nat} {selected : List Nat} {state : EdgeLabelling}
    (hz : ∀ id, id ∉ selected → state id = 0) {face : Z4Plaq}
    (hf : face ∈ positiveFaces extent state) : face ∈ selected.map (slabPlaquetteAt extent) := by
  have hp := of_decide_eq_true (List.mem_filter.mp hf).2
  have hi : (boundaryCompleteSlabPlaquettes extent).idxOf face ∈ selected := by
    by_cases hi : (boundaryCompleteSlabPlaquettes extent).idxOf face ∈ selected
    · exact hi
    · rw [hz _ hi] at hp
      exact False.elim (Nat.lt_irrefl 0 hp)
  exact List.mem_map.mpr ⟨_,hi,face_lookup (List.mem_filter.mp hf).1⟩

theorem positive_cut_length_le_selected {extent : Nat} {selected : List Nat} {state : EdgeLabelling}
    (hz : ∀ id, id ∉ selected → state id = 0) (time : Nat) :
    (cut time (positiveFaces extent state)).length ≤
      (cut time (selected.map (slabPlaquetteAt extent))).length := by
  apply CayleyPruferInjection.nodup_subset_length_le _ _ (cut_nodup time _ (positiveFaces_nodup _ _))
  intro edge he
  obtain ⟨face,hf,heq⟩ := List.mem_map.mp he
  exact List.mem_map.mpr ⟨face,List.mem_filter.mpr
    ⟨positive_face_selected hz (List.mem_filter.mp hf).1,(List.mem_filter.mp hf).2⟩,heq⟩

theorem selected_cut_minimum_four {K margin : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K selected) (hl : pairLeafKeep margin pair = true)
    (time : Nat) (hlo : margin ≤ time) (hhi : time < margin+3) :
    4 ≤ (cut time (selected.map (slabPlaquetteAt (responseExtent margin)))).length := by
  rcases retained_pair_crossing hs hp time hlo hhi with hleft | hright
  · exact Nat.le_trans (retained_cut_minimum_four (Bool.and_eq_true_iff.mp hl).1 time hleft)
      (positive_cut_length_le_selected (fun id hi => (outside K selected pair hp id hi).1) time)
  · exact Nat.le_trans (retained_cut_minimum_four (Bool.and_eq_true_iff.mp hl).2 time hright)
      (positive_cut_length_le_selected (fun id hi => (outside K selected pair hp id hi).2) time)

theorem connected_leaf_selected_minimum_twelve {K margin : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K selected) (hl : pairLeafKeep margin pair = true) : 12 ≤ selected.length := by
  have h0 := selected_cut_minimum_four hs hp hl margin (Nat.le_refl _) (by omega)
  have h1 := selected_cut_minimum_four hs hp hl (margin+1) (by omega) (by omega)
  have h2 := selected_cut_minimum_four hs hp hl (margin+2) (by omega) (by omega)
  have hb := three_cut_size_le margin (selected.map (slabPlaquetteAt (responseExtent margin)))
  rw [List.length_map] at hb
  omega

theorem original_retained_selected_minimum_twelve {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin))) :
    12 ≤ selected.length :=
  connected_leaf_selected_minimum_twelve hs (List.mem_filter.mp (List.mem_filter.mp hp).1).1
    (List.mem_filter.mp hp).2

end YMGap.Continuum.BF4ExactSlabRetainedSelectedArea

#print axioms YMGap.Continuum.BF4ExactSlabRetainedSelectedArea.positive_face_selected
#print axioms YMGap.Continuum.BF4ExactSlabRetainedSelectedArea.positive_cut_length_le_selected
#print axioms YMGap.Continuum.BF4ExactSlabRetainedSelectedArea.selected_cut_minimum_four
#print axioms YMGap.Continuum.BF4ExactSlabRetainedSelectedArea.connected_leaf_selected_minimum_twelve
#print axioms YMGap.Continuum.BF4ExactSlabRetainedSelectedArea.original_retained_selected_minimum_twelve
