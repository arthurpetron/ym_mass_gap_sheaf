/-
# Every original non-tube connected coefficient has a w^39 cofactor

The original leading-pair uniqueness pins its selected support, not just
the total leading count. Hence each non-tube core has zero amplitude at
power 36. The all-spin Casimir gap eliminates powers 37 and 38. Extracting
w^39 on the unchanged retained representation carrier is division-free,
including at zero or negative rational nome. All original signed Haar
amplitudes and dimensions remain in the explicit cofactor.

No magnitude estimate or positive full response is asserted.
-/

import YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness
import YMGap.Continuum.BF4ExactSlabShortSupportCancellation
import YMGap.Continuum.SU2FiniteCasimirFirstExcess

namespace YMGap.Continuum.BF4ExactSlabNonTubeHeatPower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteCasimirFirstExcess
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabConnectedReplicaArea
open YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness
open YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount
open YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabMinimalMixedTube
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion
open YMGap.Continuum.BF4ExactSlabShortSupportCancellation
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

section Retained

variable {K margin time : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
  (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
    (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
  (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
include hs hp

theorem retained_sub39_power36 (he : pairPower margin pair < 39) : pairPower margin pair = 36 := by
  have ha := original_retained_pair_minimum_twelve hs hp
  rw [positiveFaces_length,positiveFaces_length] at ha
  exact paired_small_power_eq36 pair.1 pair.2 _ ha he

/-- The accepted leading pair has the literal tube's ORIGINAL ordered selected support. -/
theorem leading_support_pin (hK : 1 ≤ K) (hk : leadingKeep margin pair = true) : ids = tubeIds margin := by
  have he := leading_pair_pin (List.mem_filter.mpr
    ⟨List.mem_flatMap.mpr ⟨ids,hs,hp⟩,hk⟩ : pair ∈ (retainedPairs K margin time).filter (leadingKeep margin))
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  have ht := tubePair_enumerated K margin hK
  change (tubeLabelling margin, SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling) ∈
    labels K (tubeIds margin) at ht
  rw [← he] at ht
  exact selected_support_eq (CayleyParentInj.range_nodup _) (List.mem_filter.mp hs).1 (tubeIds_selected margin) hm ht

theorem nonTube_leading_amplitude_zero (hK : 1 ≤ K) (hne : ids ≠ tubeIds margin)
    (he : pairPower margin pair = 36) : signedAmplitude margin pair ≈ 0 := by
  have hfalse : amplitudeKeep margin pair = false := by
    cases hk : amplitudeKeep margin pair with
    | false => rfl
    | true =>
      have hl : leadingKeep margin pair = true := by
        simp only [leadingKeep,he,decide_true,Bool.true_and,hk]
      exact False.elim (hne (leading_support_pin hs hp hK hl))
  simpa only [hfalse,Bool.false_eq_true,↓reduceIte] using retained_amplitude_bit hs hp he

theorem nonTube_sub39_amplitude_zero (hK : 1 ≤ K) (hne : ids ≠ tubeIds margin)
    (he : pairPower margin pair < 39) : signedAmplitude margin pair ≈ 0 :=
  nonTube_leading_amplitude_zero hs hp hK hne (retained_sub39_power36 hs hp he)

end Retained

def nonTubePairResidual (w : Q') (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  signedAmplitude margin pair * qpow w (pairPower margin pair - 39)

theorem nonTube_pair_factorization (w : Q') {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hK : 1 ≤ K)
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (hne : ids ≠ tubeIds margin) :
    weightedPairTerm w K margin pair ≈ qpow w 39 * nonTubePairResidual w margin pair := by
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  refine Q'.eqv_trans _ _ _ (original_pair_power w K margin pair (fun id _ => bounded K ids pair hm id)) ?_
  by_cases hfloor : 39 ≤ pairPower margin pair
  · exact extract_floor w (signedAmplitude margin pair) 39 (pairPower margin pair) hfloor
  · have hz := nonTube_sub39_amplitude_zero hs hp hK hne (by omega)
    have hl := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (qpow w (pairPower margin pair)) hz) (Q'.zero_mul_eqv _)
    have hr := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (qpow w 39) _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (qpow w (pairPower margin pair-39)) hz) (Q'.zero_mul_eqv _)))
      (Q'.mul_zero_eqv _)
    exact Q'.eqv_trans _ _ _ hl (Q'.eqv_symm hr)

def nonTubeCoefficientResidual (w : Q') (K margin time : Nat) (ids : List Nat) : Q' :=
  listQSum (nonTubePairResidual w margin)
    (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin))

/-- All original dimensions, signed amplitudes and retained labels remain in the cofactor. -/
theorem nonTube_coefficient_factorization (w : Q') (K margin time : Nat) (ids : List Nat) (hK : 1 ≤ K)
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hne : ids ≠ tubeIds margin) :
    connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids ≈
      qpow w 39 * nonTubeCoefficientResidual w K margin time ids := by
  refine Q'.eqv_trans _ _ _ (coefficient_leaf_filtered w K margin time ids
    (selected_nodup (CayleyParentInj.range_nodup _) (List.mem_filter.mp hs).1)
    (fun id hi => selected_mem (List.mem_filter.mp hs).1 id hi)) ?_
  exact Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun pair hp => nonTube_pair_factorization w hK hs hp hne))
    (listQSum_mul_left (qpow w 39) (nonTubePairResidual w margin) _)

end YMGap.Continuum.BF4ExactSlabNonTubeHeatPower

#print axioms YMGap.Continuum.BF4ExactSlabNonTubeHeatPower.retained_sub39_power36
#print axioms YMGap.Continuum.BF4ExactSlabNonTubeHeatPower.leading_support_pin
#print axioms YMGap.Continuum.BF4ExactSlabNonTubeHeatPower.nonTube_leading_amplitude_zero
#print axioms YMGap.Continuum.BF4ExactSlabNonTubeHeatPower.nonTube_sub39_amplitude_zero
#print axioms YMGap.Continuum.BF4ExactSlabNonTubeHeatPower.nonTubePairResidual
#print axioms YMGap.Continuum.BF4ExactSlabNonTubeHeatPower.nonTube_pair_factorization
#print axioms YMGap.Continuum.BF4ExactSlabNonTubeHeatPower.nonTubeCoefficientResidual
#print axioms YMGap.Continuum.BF4ExactSlabNonTubeHeatPower.nonTube_coefficient_factorization
