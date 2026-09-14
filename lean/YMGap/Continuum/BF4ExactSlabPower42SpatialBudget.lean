/-
# Exactly two spatial odd faces in a nonzero power-42 spatial defect

The original retained pair crosses each of the three intervening cuts.
Each occupied replica cut contains at least four faces. These twelve
temporal occupations are disjoint from all spatial occupations.
At power 42 there are exactly fourteen fundamental occupations, while
the surviving spatial count is positive and even: it is exactly two.

The joint channel splits them as (2,0) or (0,2); the negative means
channel splits them as (1,1). This counts occupations, NOT configurations
or amplitudes. Their locations and aggregate signed weights remain open.
-/

import YMGap.Continuum.BF4ExactSlabSpatialHeatPower42

namespace YMGap.Continuum.BF4ExactSlabPower42SpatialBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.BF4ExactSlabSpatialHeatPower42
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabConnectedReplicaArea
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow (positive_eq_odd)
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabMomentFaceParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem disjoint_filter_length {A : Type} (p q : A → Bool)
    (hd : ∀ x, p x=true → q x=false) : ∀ xs : List A,
    (xs.filter p).length+(xs.filter q).length ≤ xs.length
  | [] => Nat.le_refl 0
  | x::xs => by
    have ih := disjoint_filter_length p q hd xs
    cases hp : p x <;> cases hq : q x
    · simpa only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        using Nat.le_trans ih (Nat.le_succ _)
    · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have hf := hd x hp
      rw [hq] at hf
      cases hf

theorem three_cut_spatial_size_le (time : Nat) (faces : List Z4Plaq) :
    (cut time faces).length+(cut (time+1) faces).length+(cut (time+2) faces).length+
      (spatialFaces faces).length ≤ faces.length := by
  rw [← window_count]
  exact disjoint_filter_length (window time) (fun face => decide ((dirsOf face.2).2 ≠ Dir4.x3))
    (fun face hf => decide_eq_false (fun hn => hn (window_temporal hf))) faces

theorem original_temporal_spatial_budget {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin))) :
    12+(spatialFaces (positiveFaces (responseExtent margin) pair.1)).length+
      (spatialFaces (positiveFaces (responseExtent margin) pair.2)).length ≤
    (positiveFaces (responseExtent margin) pair.1).length+(positiveFaces (responseExtent margin) pair.2).length := by
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  have hleaf := Bool.and_eq_true_iff.mp (List.mem_filter.mp hp).2
  have hcut (t : Nat) (hlo : margin ≤ t) (hhi : t < margin+3) :
      4 ≤ (cut t (positiveFaces (responseExtent margin) pair.1)).length+
        (cut t (positiveFaces (responseExtent margin) pair.2)).length := by
    rcases retained_pair_crossing hs hm t hlo hhi with hl | hr
    · have h := retained_cut_minimum_four hleaf.1 t hl
      omega
    · have h := retained_cut_minimum_four hleaf.2 t hr
      omega
  have h0 := hcut margin (Nat.le_refl _) (by omega)
  have h1 := hcut (margin+1) (by omega) (by omega)
  have h2 := hcut (margin+2) (by omega) (by omega)
  have hl := three_cut_spatial_size_le margin (positiveFaces (responseExtent margin) pair.1)
  have hr := three_cut_spatial_size_le margin (positiveFaces (responseExtent margin) pair.2)
  omega

theorem power42_spatial_count_two {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hd : spatialDefectKeep margin pair=true) : pairSpatial margin pair=2 := by
  have hf := retained_power42_fundamental hs hp he
  have hb := original_temporal_spatial_budget hs hp
  rw [hf.1, positive_eq_odd _ _ (fun id hi => (hf.2 id hi).1),
    positive_eq_odd _ _ (fun id hi => (hf.2 id hi).2)] at hb
  have hlo := nonzero_spatial_minimum_two margin pair hne (spatialDefectKeep_nonempty hd)
  change 12+(spatialOddFaces margin pair.1).length+(spatialOddFaces margin pair.2).length ≤ 14 at hb
  unfold pairSpatial at hlo ⊢
  omega

theorem power42_spatial_distribution {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hd : spatialDefectKeep margin pair=true) :
    if jointCheck margin pair then
      ((spatialOddFaces margin pair.1).length=2 ∧ (spatialOddFaces margin pair.2).length=0) ∨
        ((spatialOddFaces margin pair.1).length=0 ∧ (spatialOddFaces margin pair.2).length=2)
    else (spatialOddFaces margin pair.1).length=1 ∧ (spatialOddFaces margin pair.2).length=1 := by
  have hsum := power42_spatial_count_two hs hp he hne hd
  unfold pairSpatial at hsum
  have hc := nonzero_pair_channel_checks margin pair hne
  have hl := (moment_face_parities margin true (jointCheck margin pair) pair.1 hc.1).2
  have hr := (moment_face_parities margin false (!(jointCheck margin pair)) pair.2 hc.2).2
  cases hj : jointCheck margin pair <;>
    simp only [hj, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at hl hr ⊢
  · constructor <;> omega
  · by_cases hz : (spatialOddFaces margin pair.1).length=0
    · exact Or.inr ⟨hz,by omega⟩
    · exact Or.inl ⟨by omega,by omega⟩

end YMGap.Continuum.BF4ExactSlabPower42SpatialBudget

#print axioms YMGap.Continuum.BF4ExactSlabPower42SpatialBudget.three_cut_spatial_size_le
#print axioms YMGap.Continuum.BF4ExactSlabPower42SpatialBudget.original_temporal_spatial_budget
#print axioms YMGap.Continuum.BF4ExactSlabPower42SpatialBudget.power42_spatial_count_two
#print axioms YMGap.Continuum.BF4ExactSlabPower42SpatialBudget.power42_spatial_distribution
