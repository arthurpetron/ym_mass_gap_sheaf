/-
# Original leading-power support is confined to three temporal layers

Every intervening cut costs at least four positive faces across the
replicas. Power 36 forces total area twelve, so both replicas saturate
the disjoint three-cut count. Every occupied face is therefore temporal
and based at margin, margin+1 or margin+2. No spatial plaquette or other
time layer remains in an original leading-power term.
-/

import YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
import YMGap.Continuum.Z4ThreeCutSaturation

namespace YMGap.Continuum.BF4ExactSlabMinimalPowerWindow

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabConnectedReplicaArea
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.PairedPositiveFaceLabellings

theorem retained_minimal_window {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair = 36) :
    (∀ f, f ∈ positiveFaces (responseExtent margin) pair.1 → window margin f = true) ∧
      (∀ f, f ∈ positiveFaces (responseExtent margin) pair.2 → window margin f = true) := by
  have ha := (retained_minimal_power_fundamental hs hp he).1
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  have hk := Bool.and_eq_true_iff.mp (List.mem_filter.mp hp).2
  have hb (t : Nat) (ht0 : margin ≤ t) (ht1 : t < margin+3) :
      4 ≤ (cut t (positiveFaces (responseExtent margin) pair.1)).length +
        (cut t (positiveFaces (responseExtent margin) pair.2)).length :=
    Z4LeaflessTemporalCutMinimum.pair_cut_minimum_four t _ _
      (positiveFaces_nodup _ _) (positiveFaces_nodup _ _)
      (retained_vertical_no_leaf hk.1) (retained_vertical_no_leaf hk.2)
      (retained_pair_crossing hs hm t ht0 ht1)
  have h0 := hb margin (Nat.le_refl _) (by omega)
  have h1 := hb (margin+1) (by omega) (by omega)
  have h2 := hb (margin+2) (by omega) (by omega)
  have hl := three_cut_size_le margin (positiveFaces (responseExtent margin) pair.1)
  have hr := three_cut_size_le margin (positiveFaces (responseExtent margin) pair.2)
  exact ⟨saturated_in_window margin _ (by omega),saturated_in_window margin _ (by omega)⟩

theorem positive_eq_odd (extent : Nat) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges extent → state id ≤ 1) :
    positiveFaces extent state = oddFaces extent state := by
  apply List.filter_congr
  intro f hf
  have hi := hs ((boundaryCompleteSlabPlaquettes extent).idxOf f)
    (List.mem_range.mpr (List.idxOf_lt_length_of_mem hf))
  by_cases hz : state ((boundaryCompleteSlabPlaquettes extent).idxOf f) = 0
  · simp [hz]
  · have ho : state ((boundaryCompleteSlabPlaquettes extent).idxOf f) = 1 := by omega
    simp [ho]

theorem retained_minimal_spatial_zero {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair = 36) (f : Z4Plaq)
    (hf : f ∈ boundaryCompleteSlabPlaquettes (responseExtent margin))
    (hd : (dirsOf f.2).2 ≠ Dir4.x3) :
    pair.1 ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf f) = 0 ∧
      pair.2 ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf f) = 0 := by
  have hw := retained_minimal_window hs hp he
  constructor
  · by_cases hz : pair.1 ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf f) = 0
    · exact hz
    · exact False.elim (hd (window_temporal (hw.1 f (List.mem_filter.mpr ⟨hf,decide_eq_true (by omega)⟩))))
  · by_cases hz : pair.2 ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf f) = 0
    · exact hz
    · exact False.elim (hd (window_temporal (hw.2 f (List.mem_filter.mpr ⟨hf,decide_eq_true (by omega)⟩))))

end YMGap.Continuum.BF4ExactSlabMinimalPowerWindow

#print axioms YMGap.Continuum.BF4ExactSlabMinimalPowerWindow.retained_minimal_window
#print axioms YMGap.Continuum.BF4ExactSlabMinimalPowerWindow.positive_eq_odd
#print axioms YMGap.Continuum.BF4ExactSlabMinimalPowerWindow.retained_minimal_spatial_zero
