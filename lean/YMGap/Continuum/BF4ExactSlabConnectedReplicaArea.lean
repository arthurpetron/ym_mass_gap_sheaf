/-
# Twelve positive-spin faces in each retained original replica pair

Connected selected support crosses all three intervening temporal cuts.
The exact replica labellings cover every selected face. Thus at least
one replica crosses each cut; the replica may change with the cut.
The all-spin leaf filter forces four faces on each occupied cut. The
three disjoint cuts give a combined area of at least twelve. These are
the actual retained terms of the complete original numerator expansion.
No Haar sign, heat-power factorization or positive response is inferred.
-/

import YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing
import YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum

namespace YMGap.Continuum.BF4ExactSlabConnectedReplicaArea

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.PairedPositiveFaceLabellings

theorem positive_cut_nonempty_of_index {extent time id : Nat} {state : EdgeLabelling}
    (hi : id ∈ slabPhysicalFaceEdges extent) (hc : crosses time (slabPlaquetteAt extent id) = true)
    (hp : 0 < state id) : cut time (positiveFaces extent state) ≠ [] := by
  have hf : slabPlaquetteAt extent id ∈ positiveFaces extent state := List.mem_filter.mpr
    ⟨slabPlaquetteAt_mem hi,decide_eq_true (by rw [idxOf_slabPlaquetteAt hi]; exact hp)⟩
  have hm : cutEdge (slabPlaquetteAt extent id) ∈ cut time (positiveFaces extent state) :=
    List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨hf,hc⟩,rfl⟩
  intro he
  rw [he] at hm
  exact List.not_mem_nil hm

theorem retained_pair_crossing {K margin : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K selected) (time : Nat) (hlo : margin ≤ time) (hhi : time < margin+3) :
    cut time (positiveFaces (responseExtent margin) pair.1) ≠ [] ∨
      cut time (positiveFaces (responseExtent margin) pair.2) ≠ [] := by
  have hn := shifted_probe_crossing_nonempty hs time hlo hhi
  cases he : crossingIds (responseExtent margin) time selected with
  | nil => exact False.elim (hn he)
  | cons id rest =>
    have hm : id ∈ crossingIds (responseExtent margin) time selected := by
      rw [he]; exact List.mem_cons_self
    have hi := (List.mem_filter.mp hm).1
    have hc := (List.mem_filter.mp hm).2
    have hphys := selected_mem (List.mem_filter.mp hs).1 id hi
    rcases covers K selected pair hp id hi with hl | hr
    · exact Or.inl (positive_cut_nonempty_of_index hphys hc hl)
    · exact Or.inr (positive_cut_nonempty_of_index hphys hc hr)

theorem connected_leaf_pair_minimum_twelve {K margin : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K selected) (hl : pairLeafKeep margin pair = true) :
    12 ≤ (positiveFaces (responseExtent margin) pair.1).length +
      (positiveFaces (responseExtent margin) pair.2).length :=
  retained_pair_three_cut_minimum_twelve hl margin
    (retained_pair_crossing hs hp margin (Nat.le_refl _) (by omega))
    (retained_pair_crossing hs hp (margin+1) (by omega) (by omega))
    (retained_pair_crossing hs hp (margin+2) (by omega) (by omega))

/-- Membership in the exact existing original-numerator filters supplies ALL premises. -/
theorem original_retained_pair_minimum_twelve {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin))) :
    12 ≤ (positiveFaces (responseExtent margin) pair.1).length +
      (positiveFaces (responseExtent margin) pair.2).length :=
  connected_leaf_pair_minimum_twelve hs (List.mem_filter.mp (List.mem_filter.mp hp).1).1
    (List.mem_filter.mp hp).2

end YMGap.Continuum.BF4ExactSlabConnectedReplicaArea

#print axioms YMGap.Continuum.BF4ExactSlabConnectedReplicaArea.positive_cut_nonempty_of_index
#print axioms YMGap.Continuum.BF4ExactSlabConnectedReplicaArea.retained_pair_crossing
#print axioms YMGap.Continuum.BF4ExactSlabConnectedReplicaArea.connected_leaf_pair_minimum_twelve
#print axioms YMGap.Continuum.BF4ExactSlabConnectedReplicaArea.original_retained_pair_minimum_twelve
