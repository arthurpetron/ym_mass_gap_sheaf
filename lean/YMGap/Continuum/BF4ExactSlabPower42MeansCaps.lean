/-
# Power-42 means-channel caps coincide at one of four original slices

The actual nonzero means channel has one spatial odd face per replica.
Each is aligned with the original probe. The saturated temporal window
puts both cap times between the two endpoints, inclusively. Distinct cap
times would leave either a missing intervening cut or a doubly occupied
cut, both impossible. Their common slice index is computed in 0..3.

This classifies the spatial data. It does not assert that all four cases
have nonzero Haar weight, evaluate their weights, or bound higher powers.
-/

import YMGap.Continuum.BF4ExactSlabSingleCapDecoder
import YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation

namespace YMGap.Continuum.BF4ExactSlabPower42MeansCaps

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.BF4ExactSlabSingleSpatialCap
open YMGap.Continuum.BF4ExactSlabSingleCapDecoder
open YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation
open YMGap.Continuum.BF4ExactSlabPower42SpatialBudget
open YMGap.Continuum.BF4ExactSlabSpatialHeatPower42
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabConnectedReplicaArea
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow (positive_eq_odd)
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem nonempty_window_cut_time (margin : Nat) (faces : List Z4Plaq)
    (hw : ∀ face, face ∈ faces → (dirsOf face.2).2=Dir4.x3 → window margin face=true)
    (time : Nat) (hne : cut time faces ≠ []) : margin ≤ time ∧ time < margin+3 := by
  cases he : cut time faces with
  | nil => exact False.elim (hne he)
  | cons link rest =>
    obtain ⟨face,hf,_⟩ := List.mem_map.mp (show link ∈ cut time faces from he ▸ List.mem_cons_self)
    have hm := List.mem_filter.mp hf
    have hx := of_decide_eq_true hm.2
    have ht := window_times (hw face hm.1 hx.1)
    have heq := hx.2
    constructor <;> omega

theorem single_cap_time_bounds (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (hs : (spatialOddFaces margin state).length=1)
    (hc : momentCheck margin lo (!lo) state=true)
    (hw : ∀ face, face ∈ oddFaces (responseExtent margin) state →
      (dirsOf face.2).2=Dir4.x3 → window margin face=true) :
    margin ≤ singleCapTime margin state ∧ singleCapTime margin state ≤ margin+3 := by
  have he : margin ≤ endpointTime margin lo ∧ endpointTime margin lo ≤ margin+3 := by
    cases lo <;> simp only [endpointTime, Bool.false_eq_true, ↓reduceIte]
    all_goals constructor <;> omega
  constructor
  · by_cases h : margin ≤ singleCapTime margin state
    · exact h
    · have hb : between (endpointTime margin lo) (singleCapTime margin state) (singleCapTime margin state) :=
        Or.inr ⟨Nat.le_refl _,by omega⟩
      have hx := nonempty_window_cut_time margin _ hw _
        ((single_cap_cut_nonempty_iff margin lo state hs hc _).mpr hb)
      omega
  · by_cases h : singleCapTime margin state ≤ margin+3
    · exact h
    · have hb : between (endpointTime margin lo) (singleCapTime margin state) (margin+3) :=
        Or.inl ⟨he.2,by omega⟩
      have hx := nonempty_window_cut_time margin _ hw _
        ((single_cap_cut_nonempty_iff margin lo state hs hc _).mpr hb)
      omega

theorem power42_means_common_cap {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hd : spatialDefectKeep margin pair=true) (hj : jointCheck margin pair=false) :
    singleCapTime margin pair.1=singleCapTime margin pair.2 ∧
      margin ≤ singleCapTime margin pair.1 ∧ singleCapTime margin pair.1 ≤ margin+3 := by
  have hc := nonzero_pair_channel_checks margin pair hne
  simp only [hj, Bool.not_false] at hc
  have hsp := power42_spatial_distribution hs hp he hne hd
  simp only [hj, Bool.false_eq_true, ↓reduceIte] at hsp
  have hw := power42_temporal_window hs hp he hne hd
  have hl := single_cap_time_bounds margin true pair.1 hsp.1 hc.1 hw.1
  have hr := single_cap_time_bounds margin false pair.2 hsp.2 hc.2 hw.2
  have hle : singleCapTime margin pair.1 ≤ singleCapTime margin pair.2 := by
    by_cases h : singleCapTime margin pair.1 ≤ singleCapTime margin pair.2
    · exact h
    · have hbl : between (endpointTime margin true) (singleCapTime margin pair.1) (singleCapTime margin pair.2) :=
        Or.inl ⟨hr.1,by omega⟩
      have hbr : between (endpointTime margin false) (singleCapTime margin pair.2) (singleCapTime margin pair.2) :=
        Or.inr ⟨Nat.le_refl _,by change _ < margin+3; omega⟩
      exact False.elim (power42_cuts_exclusive hs hp he hne hd _ hr.1 (by omega)
        ⟨(single_cap_cut_nonempty_iff margin true pair.1 hsp.1 hc.1 _).mpr hbl,
          (single_cap_cut_nonempty_iff margin false pair.2 hsp.2 hc.2 _).mpr hbr⟩)
  have hge : singleCapTime margin pair.2 ≤ singleCapTime margin pair.1 := by
    by_cases h : singleCapTime margin pair.2 ≤ singleCapTime margin pair.1
    · exact h
    · have hf := retained_power42_fundamental hs hp he
      have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
      have hx := retained_pair_crossing hs hm (singleCapTime margin pair.1) hl.1 (by omega)
      rw [positive_eq_odd _ _ (fun id hi => (hf.2 id hi).1),
        positive_eq_odd _ _ (fun id hi => (hf.2 id hi).2)] at hx
      rcases hx with hx | hx
      · have hb := (single_cap_cut_nonempty_iff margin true pair.1 hsp.1 hc.1 _).mp hx
        change between margin (singleCapTime margin pair.1) (singleCapTime margin pair.1) at hb
        rcases hb with hb | hb <;> omega
      · have hb := (single_cap_cut_nonempty_iff margin false pair.2 hsp.2 hc.2 _).mp hx
        change between (margin+3) (singleCapTime margin pair.2) (singleCapTime margin pair.1) at hb
        rcases hb with hb | hb <;> omega
  exact ⟨Nat.le_antisymm hle hge,hl⟩

def meansCapIndex (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  singleCapTime margin pair.1-margin

theorem power42_means_four_slices {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hd : spatialDefectKeep margin pair=true) (hj : jointCheck margin pair=false) :
    meansCapIndex margin pair < 4 ∧
      spatialOddFaces margin pair.1=[sliceFace margin (meansCapIndex margin pair)] ∧
      spatialOddFaces margin pair.2=[sliceFace margin (meansCapIndex margin pair)] := by
  have ht := power42_means_common_cap hs hp he hne hd hj
  have hc := nonzero_pair_channel_checks margin pair hne
  simp only [hj, Bool.not_false] at hc
  have hsp := power42_spatial_distribution hs hp he hne hd
  simp only [hj, Bool.false_eq_true, ↓reduceIte] at hsp
  have heq : capFace margin (singleCapTime margin pair.1)=sliceFace margin (meansCapIndex margin pair) := by
    unfold capFace sliceFace meansCapIndex
    have htime : margin+(singleCapTime margin pair.1-margin)=singleCapTime margin pair.1 := by omega
    rw [htime]
  constructor
  · unfold meansCapIndex
    omega
  constructor
  · rw [single_spatial_cap_pin margin true pair.1 hsp.1 hc.1,heq]
  · rw [single_spatial_cap_pin margin false pair.2 hsp.2 hc.2,← ht.1,heq]

end YMGap.Continuum.BF4ExactSlabPower42MeansCaps

#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCaps.nonempty_window_cut_time
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCaps.single_cap_time_bounds
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCaps.power42_means_common_cap
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCaps.meansCapIndex
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCaps.power42_means_four_slices
