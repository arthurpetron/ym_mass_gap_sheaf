/-
# Explicit volume rate for the SAME thermodynamic connected covariance

The original mean caps, valid at every slab, make the product error
Lipschitz with computed constants. Together with the three constructed
moment errors this gives one geometric covariance error and a Type-level
volume modulus. The nome is fixed at 1/1024; spacing and observable support
are not removed. The rate concerns receding boundaries, not time separation.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance
import YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression (reflectedProduct)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit (meanSequence meanLimit)
open YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit (rate rate_pos rate_le_half)
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay (boxSize)
open YMGap.Continuum.RegularLinearGeometricModulus

private theorem ofPointwise {a b : CReal} (h : ∀ n, a.approx n ≤ b.approx n) : leEv a b := by
  intro epsilon he
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _ (h n)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

private theorem abs_le_of_twoSides {x : CReal} {B : Q'}
    (hp : leEv x (ofQ' B)) (hn : leEv (CReal.neg x) (ofQ' B)) :
    leEv (CReal.abs x) (ofQ' B) := by
  intro epsilon he
  obtain ⟨Np, hNp⟩ := hp epsilon he
  obtain ⟨Nn, hNn⟩ := hn epsilon he
  refine ⟨max Np Nn, fun n h => ?_⟩
  exact Q'.abs_le
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg (hNn n (Nat.le_trans (Nat.le_max_right _ _) h)))
      (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
    (hNp n (Nat.le_trans (Nat.le_max_left _ _) h))

def meanCap {base : Nat} (e : PlaquetteExpression base) : Q' :=
  BF4ExactSlabPlaquetteUniformSquareBound.bound e + 1

theorem meanCap_nonnegative {base : Nat} (e : PlaquetteExpression base) : (0 : Q') ≤ meanCap e :=
  Q'.zero_le_add _ _ (BF4ExactSlabPlaquetteUniformSquareBound.bound_nonnegative e) Q'.zero_le_one

theorem meanSequence_abs_le {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (meanSequence e margin)) (ofQ' (meanCap e)) := by
  rw [← lowerMeanSequence_pin]
  exact abs_le_of_twoSides
    (BF4ExactSlabPlaquetteUniformMomentBound.bulk_mean_upper nome nome_pos nome_lt_one
      margin ⟨0, Nat.zero_lt_succ _⟩ e)
    (BF4ExactSlabPlaquetteUniformMomentBound.bulk_neg_mean_upper nome nome_pos nome_lt_one
      margin ⟨0, Nat.zero_lt_succ _⟩ e)

theorem meanLimit_abs_le {base : Nat} (e : PlaquetteExpression base) :
    leEv (CReal.abs (meanLimit e)) (ofQ' (meanCap e)) :=
  leEv_of_convergesTo_le
    (convergesTo_abs (BF4ExactSlabExpressionThermodynamicLimit.meanLimit_converges e))
    (convergesTo_const _) (meanSequence_abs_le e)

private theorem covarianceDifference_le (a b u v U V : Q') :
    Q'.abs ((a + -(u*v)) + -(b + -(U*V))) ≤
      Q'.abs (a + -b) + (Q'.abs u * Q'.abs (v + -V) + Q'.abs V * Q'.abs (u + -U)) := by
  have hid : Q'.eqv ((a + -(u*v)) + -(b + -(U*V)))
      ((a + -b) + -(u*(v + -V) + V*(u + -U))) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.var 2) (.var 3))))
        (.neg (.add (.var 1) (.neg (.mul (.var 4) (.var 5))))))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.mul (.var 2) (.add (.var 3) (.neg (.var 5))))
          (.mul (.var 5) (.add (.var 2) (.neg (.var 4)))))))
      (by decide) (fun | 0 => a | 1 => b | 2 => u | 3 => v | 4 => U | _ => V)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hid))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add_left _ _ _
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
          (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
            (Q'.add_le_add (ExpNeg.abs_mul_le _ _) (ExpNeg.abs_mul_le _ _))))))

private theorem abs_product_bound {u v : CReal} {U V : Q'}
    (hU : (0 : Q') ≤ U) (hu : leEv (CReal.abs u) (ofQ' U)) (hv : leEv (CReal.abs v) (ofQ' V)) :
    leEv (CReal.mul (CReal.abs u) (CReal.abs v)) (ofQ' (U*V)) := by
  have hv0 : leEv czero (CReal.abs v) :=
    leEv_ofQ'_of_approx_ge (fun n => Q'.abs_nonneg (v.approx n))
  have hU0 : leEv czero (ofQ' U) := leEv_ofQ'_of_approx_ge (fun _ => hU)
  have h1 : leEv (CReal.mul (CReal.abs u) (CReal.abs v)) (CReal.mul (CReal.abs v) (CReal.abs u)) :=
    leEv_of_equiv (CRealAlg.cmul_comm (CReal.abs u) (CReal.abs v))
  have h2 : leEv (CReal.mul (CReal.abs v) (CReal.abs u)) (CReal.mul (CReal.abs v) (ofQ' U)) :=
    leEv_mul_nonneg_left hv0 hu
  have h3 : leEv (CReal.mul (CReal.abs v) (ofQ' U)) (CReal.mul (ofQ' U) (CReal.abs v)) :=
    leEv_of_equiv (CRealAlg.cmul_comm (CReal.abs v) (ofQ' U))
  have h4 : leEv (CReal.mul (ofQ' U) (CReal.abs v)) (CReal.mul (ofQ' U) (ofQ' V)) :=
    leEv_mul_nonneg_left hU0 hv
  have h5 : leEv (CReal.mul (ofQ' U) (ofQ' V)) (ofQ' (U*V)) :=
    ofPointwise (fun _ => Q'.le_refl' (U*V))
  exact leEv_trans h1 (leEv_trans h2 (leEv_trans h3 (leEv_trans h4 h5)))

/-- Three input moment errors, combined with the computed original mean caps. -/
def covarianceAmplitude {base : Nat} (e f : PlaquetteExpression base) : Q' :=
  BF4ExactSlabSpacetimeThermodynamicLimit.amplitude (reflectedProduct e f) +
    (meanCap e * BF4ExactSlabExpressionThermodynamicLimit.amplitude f +
      meanCap f * BF4ExactSlabExpressionThermodynamicLimit.amplitude e)

theorem covarianceAmplitude_nonnegative {base : Nat} (e f : PlaquetteExpression base) :
    (0 : Q') ≤ covarianceAmplitude e f :=
  Q'.zero_le_add _ _ (BF4ExactSlabSpacetimeThermodynamicLimit.amplitude_nonnegative (reflectedProduct e f))
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (meanCap_nonnegative e) (BF4ExactSlabExpressionThermodynamicLimit.amplitude_nonnegative f))
      (Q'.mul_nonneg _ _ (meanCap_nonnegative f) (BF4ExactSlabExpressionThermodynamicLimit.amplitude_nonnegative e)))

theorem covariance_geometric_bound {base : Nat} (e f : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (covarianceLimit e f) (covarianceSequence e f margin)))
      (ofQ' (covarianceAmplitude e f * rate^(margin+1-boxSize base))) := by
  have hpin := covarianceSequence_pin e f margin
  rw [lowerMeanSequence_pin, lowerMeanSequence_pin] at hpin
  refine leEv_trans (leEv_of_equiv (abs_equiv_congr (CReal.sub_congr_right hpin))) ?_
  have hdecomp : leEv
      (CReal.abs (CReal.sub (covarianceLimit e f)
        (CReal.sub (formSequence e f margin) (CReal.mul (meanSequence e margin) (meanSequence f margin)))))
      (CReal.add (CReal.abs (CReal.sub (formLimit e f) (formSequence e f margin)))
        (CReal.add
          (CReal.mul (CReal.abs (meanLimit e)) (CReal.abs (CReal.sub (meanLimit f) (meanSequence f margin))))
          (CReal.mul (CReal.abs (meanSequence f margin)) (CReal.abs (CReal.sub (meanLimit e) (meanSequence e margin)))))) :=
    ofPointwise (fun n => covarianceDifference_le
    ((formLimit e f).approx n) ((formSequence e f margin).approx n)
    ((meanLimit e).approx n) ((meanLimit f).approx n)
    ((meanSequence e margin).approx n) ((meanSequence f margin).approx n))
  have he := BF4ExactSlabExpressionThermodynamicLimit.meanLimit_geometric_bound e margin
  have hf := BF4ExactSlabExpressionThermodynamicLimit.meanLimit_geometric_bound f margin
  have hsum := leEv_add (form_geometric_bound e f margin)
    (leEv_add (abs_product_bound (meanCap_nonnegative e) (meanLimit_abs_le e) hf)
      (abs_product_bound (meanCap_nonnegative f) (meanSequence_abs_le f margin) he))
  refine leEv_trans hdecomp (leEv_trans hsum ?_)
  apply leEv_of_equiv
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 5))
      (.add (.mul (.var 1) (.mul (.var 2) (.var 5)))
        (.mul (.var 3) (.mul (.var 4) (.var 5)))))
    (.mul (.add (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))) (.var 5))
    (by decide)
    (fun | 0 => BF4ExactSlabSpacetimeThermodynamicLimit.amplitude (reflectedProduct e f)
         | 1 => meanCap e | 2 => BF4ExactSlabExpressionThermodynamicLimit.amplitude f
         | 3 => meanCap f | 4 => BF4ExactSlabExpressionThermodynamicLimit.amplitude e
         | _ => rate^(margin+1-boxSize base))

def covarianceVolumeModulus {base : Nat} (e f : PlaquetteExpression base) (epsilon : Q') : Nat :=
  boxSize base + geoOuterModulus (covarianceAmplitude e f) epsilon

theorem covariance_coefficient_small {base : Nat} (e f : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hm : covarianceVolumeModulus e f epsilon ≤ margin) :
    covarianceAmplitude e f * rate^(margin+1-boxSize base) ≤ epsilon := by
  have hC := covarianceAmplitude_nonnegative e f
  have htwo : covarianceAmplitude e f ≤ Q'.ofNat 2 * covarianceAmplitude e f :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hC)
      (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) (by decide)
        (fun _ => covarianceAmplitude e f)))
  have hm' : geoOuterModulus (covarianceAmplitude e f) epsilon ≤ margin+1-boxSize base := by
    change boxSize base + geoOuterModulus (covarianceAmplitude e f) epsilon ≤ margin at hm
    omega
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (TotalMajorantClose.pow_le_pow_base (Q'.le_of_lt rate_pos) rate_le_half _) hC)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ htwo (Q'.pow_nonneg _ HalfPow.half_nonneg _))
      (geoTail_le_of_modulus (covarianceAmplitude e f) hC epsilon he _ hm'))

theorem covariance_error_le {base : Nat} (e f : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hm : covarianceVolumeModulus e f epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (covarianceLimit e f) (covarianceSequence e f margin))) (ofQ' epsilon) :=
  leEv_trans (covariance_geometric_bound e f margin)
    (leEv_le_ofQ'_of_approx_le (fun _ => covariance_coefficient_small e f epsilon he margin hm))

end YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.meanCap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.meanCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.meanSequence_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.meanLimit_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.covarianceAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.covarianceAmplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.covariance_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.covarianceVolumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.covariance_coefficient_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate.covariance_error_le
