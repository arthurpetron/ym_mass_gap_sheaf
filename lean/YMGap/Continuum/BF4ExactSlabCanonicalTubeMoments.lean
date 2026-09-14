/-
# The explicit original tube has a nonzero connected Haar term

Evaluate the actual full-carrier mixed moment directly from the explicit
labels, without assuming any moment or replica filter. The zero replica
has partition moment one. Nonzero original moments then force acceptance
by the existing charge, odd-cut and leaf filters. This is one term of the
full expansion, not positivity of the full interacting response.
-/

import YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport

namespace YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabMinimalMixedTube
open YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin
open YMGap.Continuum.BF4ExactSlabBareTubeEvaluation
open YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation
open YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

theorem tube_mixed_moment (margin : Nat) :
    moment margin true true (tubeLabelling margin) ≈ bareTubeMoment margin := by
  have hp := (fundamental_integrand _ (tubeLabelling margin) (fun id _ => tube_small margin id)).trans
    (polynomialProduct_perm _ (tube_positive_perm margin))
  apply haar_of_coeff
  change RatPolyCoeffEqv (polyMul (insertion margin true true) _) _
  unfold insertion
  rw [lower_shifted_probe_pin,upper_shifted_probe_pin]
  exact ((RatPolyCoeffEqv.refl _).mul hp).trans
    (endpoints_product (fundamentalCharacter (responseExtent margin)) _ _ _)

theorem zero_positive (extent : Nat) : positiveFaces extent zeroEdgeLabelling = [] := by
  unfold positiveFaces
  simp only [zeroEdgeLabelling,Nat.lt_irrefl,decide_false]
  induction Z4HalfTimeReflectionGeometry.boundaryCompleteSlabPlaquettes extent with
  | nil => rfl
  | cons f fs ih => exact ih

theorem zero_partition_moment (margin : Nat) : moment margin false false zeroEdgeLabelling ≈ 1 := by
  have hp := fundamental_integrand (responseExtent margin) zeroEdgeLabelling (fun _ _ => Nat.zero_le 1)
  rw [zero_positive] at hp
  have h : RatPolyCoeffEqv (polyMul (insertion margin false false)
      (exactCorrectedSlabSpinNetworkIntegrand (responseExtent margin) zeroEdgeLabelling)) polyOne :=
    ((RatPolyCoeffEqv.one_mul polyOne).mul hp).trans (RatPolyCoeffEqv.one_mul polyOne)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff h) (QPolyHaarPositiveSubstitution.haar_one _)

theorem tube_pair_moment (margin : Nat) :
    pairTerm margin (tubePair margin).1 (tubePair margin).2 ≈ bareTubeMoment margin := by
  have hz := one_endpoint_zero margin true false (tubeLabelling margin) (by decide)
    (fun id _ => tube_small margin id) (tube_positive_window margin)
  have hprod : moment margin true false (tubeLabelling margin) * moment margin false true zeroEdgeLabelling ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hz) (Q'.zero_mul_eqv _)
  have hneg : -(moment margin true false (tubeLabelling margin) * moment margin false true zeroEdgeLabelling) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hprod) (by decide)
  have hmain : moment margin true true (tubeLabelling margin) * moment margin false false zeroEdgeLabelling ≈
      bareTubeMoment margin :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (tube_mixed_moment margin))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (zero_partition_moment margin)) (Q'.mul_one_eqv _))
  exact Q'.eqv_trans _ _ _ (pairTerm_pin margin _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hmain hneg) (Q'.eqv_of_eq (Q'.add_zero' _)))

theorem bareTube_nonzero (margin : Nat) : ¬bareTubeMoment margin ≈ 0 := by
  intro hz
  have h : (1 : Q') ≈ 0 := Q'.eqv_trans _ _ _ (Q'.eqv_symm (dimension_times_tube margin))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _))
  exact (by decide : ¬(1 : Q') ≈ 0) h

theorem tube_pair_nonzero (margin : Nat) : ¬pairTerm margin (tubePair margin).1 (tubePair margin).2 ≈ 0 :=
  fun hz => bareTube_nonzero margin (Q'.eqv_trans _ _ _ (Q'.eqv_symm (tube_pair_moment margin)) hz)

theorem tube_momentCheck (margin : Nat) : momentCheck margin true true (tubeLabelling margin) = true := by
  cases hc : momentCheck margin true true (tubeLabelling margin) with
  | true => rfl
  | false => exact False.elim (bareTube_nonzero margin
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (tube_mixed_moment margin)) (moment_rejected margin true true _ hc)))

theorem zero_momentCheck (margin : Nat) : momentCheck margin false false zeroEdgeLabelling = true := by
  cases hc : momentCheck margin false false zeroEdgeLabelling with
  | true => rfl
  | false =>
    have h : (1 : Q') ≈ 0 := Q'.eqv_trans _ _ _ (Q'.eqv_symm (zero_partition_moment margin))
      (moment_rejected margin false false _ hc)
    exact False.elim ((by decide : ¬(1 : Q') ≈ 0) h)

theorem tube_amplitudeKeep (margin : Nat) : amplitudeKeep margin (tubePair margin) = true :=
  Bool.and_eq_true_iff.mpr ⟨tube_momentCheck margin,zero_momentCheck margin⟩

theorem tube_pairKeep (margin time : Nat) : pairKeep margin time (tubePair margin) = true := by
  cases hk : pairKeep margin time (tubePair margin) with
  | true => rfl
  | false => exact False.elim (tube_pair_nonzero margin (pair_rejected margin time _ hk))

theorem tube_pairLeafKeep (margin : Nat) : pairLeafKeep margin (tubePair margin) = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · cases hk : leafKeep margin (tubeLabelling margin) with
    | true => exact hk
    | false => exact False.elim (tube_pair_nonzero margin (pair_left_leaf_rejected margin _ _ hk))
  · cases hk : leafKeep margin zeroEdgeLabelling with
    | true => exact hk
    | false => exact False.elim (tube_pair_nonzero margin (pair_right_leaf_rejected margin _ _ hk))

end YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments

#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.tube_mixed_moment
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.zero_positive
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.zero_partition_moment
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.tube_pair_moment
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.bareTube_nonzero
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.tube_pair_nonzero
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.tube_momentCheck
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.zero_momentCheck
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.tube_amplitudeKeep
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.tube_pairKeep
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments.tube_pairLeafKeep
