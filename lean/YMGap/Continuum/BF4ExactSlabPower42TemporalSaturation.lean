/-
# Power-42 spatial defects saturate the three-cut temporal budget

The two spatial occupations leave exactly twelve temporal occupations.
Every intervening cut has exactly four occupations across the replicas;
all temporal occupations lie in those three layers. Since each nonempty
replica cut costs at least four, both replicas cannot occupy the same cut.
These statements concern the actual retained original label pairs.
-/

import YMGap.Continuum.BF4ExactSlabPower42SpatialBudget

namespace YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.BF4ExactSlabPower42SpatialBudget
open YMGap.Continuum.BF4ExactSlabSpatialHeatPower42
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabConnectedReplicaArea
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow (positive_eq_odd)
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem temporal_spatial_length : ∀ faces : List Z4Plaq,
    (temporalFaces faces).length+(spatialFaces faces).length=faces.length
  | [] => rfl
  | face::faces => by
    have ih := temporal_spatial_length faces
    by_cases ht : (dirsOf face.2).2 = Dir4.x3
    all_goals
      simp only [temporalFaces, spatialFaces, List.filter_cons, ht, ne_eq, not_true_eq_false,
        not_false_eq_true, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.length_cons] at ih ⊢
      omega

theorem spatial_budget_saturated_window (time : Nat) (faces : List Z4Plaq)
    (he : (cut time faces).length+(cut (time+1) faces).length+(cut (time+2) faces).length+
      (spatialFaces faces).length=faces.length)
    (face : Z4Plaq) (hf : face ∈ faces) (ht : (dirsOf face.2).2=Dir4.x3) :
    window time face=true := by
  have hs := temporal_spatial_length faces
  apply saturated_in_window time (temporalFaces faces) ?_ face
    (List.mem_filter.mpr ⟨hf,decide_eq_true ht⟩)
  rw [cut_temporalFaces, cut_temporalFaces, cut_temporalFaces]
  omega

theorem power42_cut_saturation {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hd : spatialDefectKeep margin pair=true) :
    ((cut margin (oddFaces (responseExtent margin) pair.1)).length+
      (cut (margin+1) (oddFaces (responseExtent margin) pair.1)).length+
      (cut (margin+2) (oddFaces (responseExtent margin) pair.1)).length+
      (spatialOddFaces margin pair.1).length=(oddFaces (responseExtent margin) pair.1).length) ∧
    ((cut margin (oddFaces (responseExtent margin) pair.2)).length+
      (cut (margin+1) (oddFaces (responseExtent margin) pair.2)).length+
      (cut (margin+2) (oddFaces (responseExtent margin) pair.2)).length+
      (spatialOddFaces margin pair.2).length=(oddFaces (responseExtent margin) pair.2).length) ∧
    (∀ t, margin ≤ t → t < margin+3 →
      (cut t (oddFaces (responseExtent margin) pair.1)).length+
        (cut t (oddFaces (responseExtent margin) pair.2)).length=4) := by
  have hf := retained_power42_fundamental hs hp he
  have hleft := positive_eq_odd _ _ (fun id hi => (hf.2 id hi).1)
  have hright := positive_eq_odd _ _ (fun id hi => (hf.2 id hi).2)
  have ha := hf.1
  rw [hleft, hright] at ha
  have hsp := power42_spatial_count_two hs hp he hne hd
  unfold pairSpatial at hsp
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  have hk := Bool.and_eq_true_iff.mp (List.mem_filter.mp hp).2
  have hcut (t : Nat) (hlo : margin ≤ t) (hhi : t < margin+3) :
      4 ≤ (cut t (oddFaces (responseExtent margin) pair.1)).length+
        (cut t (oddFaces (responseExtent margin) pair.2)).length := by
    rw [← hleft, ← hright]
    rcases retained_pair_crossing hs hm t hlo hhi with hl | hr
    · have h := retained_cut_minimum_four hk.1 t hl
      omega
    · have h := retained_cut_minimum_four hk.2 t hr
      omega
  have h0 := hcut margin (Nat.le_refl _) (by omega)
  have h1 := hcut (margin+1) (by omega) (by omega)
  have h2 := hcut (margin+2) (by omega) (by omega)
  have hl := three_cut_spatial_size_le margin (oddFaces (responseExtent margin) pair.1)
  have hr := three_cut_spatial_size_le margin (oddFaces (responseExtent margin) pair.2)
  change _+(spatialOddFaces margin pair.1).length ≤ _ at hl
  change _+(spatialOddFaces margin pair.2).length ≤ _ at hr
  constructor
  · omega
  constructor
  · omega
  intro t hlo hhi
  have ht : t=margin ∨ t=margin+1 ∨ t=margin+2 := by omega
  rcases ht with rfl | rfl | rfl <;> omega

theorem power42_temporal_window {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hd : spatialDefectKeep margin pair=true) :
    (∀ face, face ∈ oddFaces (responseExtent margin) pair.1 →
      (dirsOf face.2).2=Dir4.x3 → window margin face=true) ∧
    (∀ face, face ∈ oddFaces (responseExtent margin) pair.2 →
      (dirsOf face.2).2=Dir4.x3 → window margin face=true) := by
  have hc := power42_cut_saturation hs hp he hne hd
  exact ⟨spatial_budget_saturated_window margin _ hc.1,
    spatial_budget_saturated_window margin _ hc.2.1⟩

theorem power42_cuts_exclusive {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hd : spatialDefectKeep margin pair=true) (t : Nat) (hlo : margin ≤ t) (hhi : t < margin+3) :
    ¬(cut t (oddFaces (responseExtent margin) pair.1) ≠ [] ∧
      cut t (oddFaces (responseExtent margin) pair.2) ≠ []) := by
  rintro ⟨hl,hr⟩
  have hf := retained_power42_fundamental hs hp he
  have hk := Bool.and_eq_true_iff.mp (List.mem_filter.mp hp).2
  have ha := (power42_cut_saturation hs hp he hne hd).2.2 t hlo hhi
  rw [← positive_eq_odd _ _ (fun id hi => (hf.2 id hi).1)] at hl
  rw [← positive_eq_odd _ _ (fun id hi => (hf.2 id hi).2)] at hr
  have hleft := retained_cut_minimum_four hk.1 t hl
  have hright := retained_cut_minimum_four hk.2 t hr
  rw [positive_eq_odd _ _ (fun id hi => (hf.2 id hi).1)] at hleft
  rw [positive_eq_odd _ _ (fun id hi => (hf.2 id hi).2)] at hright
  omega

end YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation

#print axioms YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation.temporal_spatial_length
#print axioms YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation.spatial_budget_saturated_window
#print axioms YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation.power42_cut_saturation
#print axioms YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation.power42_temporal_window
#print axioms YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation.power42_cuts_exclusive
