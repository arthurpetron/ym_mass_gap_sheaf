/-
# Every original leading pair has amplitude zero or one

The original dimension products equal 4096 at combined minimal power.
If both original mixed/partition center checks pass, the actual Haar
moments are the literal tube moment and one. Their amplitude is exactly
one by the original carrier contraction. Otherwise the pair is zero.
The number of accepted pairs in the full expansion is not assumed.
-/

import YMGap.Continuum.BF4ExactSlabBareTubeEvaluation

namespace YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow
open YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation
open YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin
open YMGap.Continuum.BF4ExactSlabBareTubeEvaluation
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

theorem fundamental_dimensions (state : Nat → Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → state id ≤ 1) →
    dimensionProduct state ids ≈ qpow (2 : Q') (positiveCount state ids)
  | [], _ => Q'.eqv_refl _
  | id::ids, h => by
    have hb := h id List.mem_cons_self
    have ht := fundamental_dimensions state ids (fun i hi => h i (List.mem_cons_of_mem id hi))
    by_cases hz : state id = 0
    · have hc : positiveCount state (id::ids) = positiveCount state ids := by simp [positiveCount,hz]
      rw [hc]
      change dimQ (state id) * dimensionProduct state ids ≈ _
      rw [hz]
      exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ht
    · have ho : state id = 1 := by omega
      have hc : positiveCount state (id::ids) = positiveCount state ids + 1 := by simp [positiveCount,ho]
      rw [hc]
      change dimQ (state id) * dimensionProduct state ids ≈ _
      rw [ho]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ht) (Q'.mul_comm_eqv _ _)

theorem retained_dimensions {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair = 36) :
    dimensionProduct pair.1 (slabPhysicalFaceEdges (responseExtent margin)) *
      dimensionProduct pair.2 (slabPhysicalFaceEdges (responseExtent margin)) ≈ (4096 : Q') := by
  have h := retained_minimal_power_fundamental hs hp he
  have ha := h.1
  rw [positiveFaces_length,positiveFaces_length] at ha
  have hl := fundamental_dimensions pair.1 _ (fun id hi => (h.2 id hi).1)
  have hr := fundamental_dimensions pair.2 _ (fun id hi => (h.2 id hi).2)
  have hm := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hl) (Q'.mul_eqv_congr_left _ _ _ hr)
  have hpow := HeatKernelRGStep.qpow_add (2 : Q')
    (positiveCount pair.1 (slabPhysicalFaceEdges (responseExtent margin)))
    (positiveCount pair.2 (slabPhysicalFaceEdges (responseExtent margin)))
  rw [ha] at hpow
  exact Q'.eqv_trans _ _ _ hm (Q'.eqv_trans _ _ _ (Q'.eqv_symm hpow) (by decide +kernel))

def amplitudeKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  momentCheck margin true true pair.1 && momentCheck margin false false pair.2

theorem retained_amplitude_bit {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair = 36) :
    signedAmplitude margin pair ≈ (if amplitudeKeep margin pair then 1 else 0) := by
  have hb := (retained_minimal_power_fundamental hs hp he).2
  have hw := retained_minimal_window hs hp he
  have hpin : signedAmplitude margin pair ≈ (4096 : Q') *
      (moment margin true true pair.1 * moment margin false false pair.2) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (retained_dimensions hs hp he))
      (Q'.mul_eqv_congr_left _ _ _ (retained_minimal_pairTerm hs hp he))
  cases hl : momentCheck margin true true pair.1 with
  | false =>
    simp only [amplitudeKeep,hl,Bool.false_and,Bool.false_eq_true,↓reduceIte]
    have hz : moment margin true true pair.1 * moment margin false false pair.2 ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (moment_rejected margin true true pair.1 hl)) (Q'.zero_mul_eqv _)
    exact Q'.eqv_trans _ _ _ hpin (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _))
  | true =>
    cases hr : momentCheck margin false false pair.2 with
    | false =>
      simp only [amplitudeKeep,hl,hr,Bool.true_and,Bool.false_eq_true,↓reduceIte]
      have hz : moment margin true true pair.1 * moment margin false false pair.2 ≈ 0 :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (moment_rejected margin false false pair.2 hr)) (Q'.mul_zero_eqv _)
      exact Q'.eqv_trans _ _ _ hpin (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _))
    | true =>
      simp only [amplitudeKeep,hl,hr,Bool.true_and,↓reduceIte]
      have hm := accepted_mixed_moment_pin margin pair.1 (fun id hi => (hb id hi).1) hw.1 hl
      have hp1 := accepted_partition_one margin pair.2 (fun id hi => (hb id hi).2) hw.2 hr
      have ht := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp1) (Q'.mul_one_eqv _))
      exact Q'.eqv_trans _ _ _ hpin (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ht) (dimension_times_tube margin))

end YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude

#print axioms YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude.fundamental_dimensions
#print axioms YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude.retained_dimensions
#print axioms YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude.amplitudeKeep
#print axioms YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude.retained_amplitude_bit
