/-
# Closed all-degree Haar moments of the ORIGINAL quaternion translations

The proved Gaussian formula converts to sphere moments by head homogeneity
and cancellation of an explicit positive radial denominator. Odd total
degree vanishes before tail integration. Both original Hamilton orders and
every exponent quadruple are covered, with every tail coefficient retained.

The final theorem uses the EXISTING expectedTranslatedHeadMoment, without
its executable moment-check premise. Full selected-polynomial translation
and reflected slab gluing are downstream consumers, not asserted here.
-/

import YMGap.Continuum.SU2QuaternionPartialSphereGaussian
import YMGap.Continuum.SU2QuaternionTranslationGaussianMoments

namespace YMGap.Continuum.SU2QuaternionTranslationHaarMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionTranslationGaussianMoments

local infix:50 " ≈ " => Q'.eqv

private theorem power_head_degree {p : RatPoly} (h : HasQuaternionBlockDegree 0 1 p) :
    ∀ n : Nat, HasQuaternionBlockDegree 0 n (ratPolyPow p n)
  | 0 => hasQuaternionBlockDegree_one 0
  | n + 1 => (power_head_degree h n).mul h

/-- Syntactic head homogeneity of the actual Hamilton-product coordinates. -/
theorem translatedQuaternion_head_degree (right : Bool) :
    HasPolyQuaternionBlockDegree 0 1
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) := by
  cases right
  · simpa only [leftTranslatedHeadQuaternion, if_pos, if_neg, Nat.zero_add, Nat.reduceAdd, Bool.false_eq_true]
      using (hasPolyQuaternionBlockDegree_coordinateVariable 1 0).mul
        (hasPolyQuaternionBlockDegree_coordinateVariable 0 0)
  · simpa only [rightTranslatedHeadQuaternion, if_pos, if_neg, Nat.add_zero, Nat.reduceAdd]
      using (hasPolyQuaternionBlockDegree_coordinateVariable 0 0).mul
        (hasPolyQuaternionBlockDegree_coordinateVariable 1 0)

/-- Every monomial term has the stated head degree, at all exponents. -/
theorem translatedHeadMonomial_head_degree (right : Bool) (e0 e1 e2 e3 : Nat) :
    HasQuaternionBlockDegree 0 (e0 + e1 + e2 + e3)
      (translatedHeadMonomial
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) e0 e1 e2 e3) := by
  have h := translatedQuaternion_head_degree right
  exact HasQuaternionBlockDegree.relabel (by omega)
    ((power_head_degree h.scalar e0).mul
      ((power_head_degree h.iPart e1).mul ((power_head_degree h.jPart e2).mul (power_head_degree h.kPart e3))))

private theorem ledger_degree (e0 e1 e2 e3 : Nat) :
    quaternionBlockDegree (headExponentLedger e0 e1 e2 e3) 0 = e0 + e1 + e2 + e3 := rfl

/-- Exact partial Haar moment, with the retained radius still explicit.
No unit-radius, moment-check, degree bound, or analytic hypothesis. -/
theorem translatedHeadMonomial_haar_closed (right : Bool) (e0 e1 e2 e3 : Nat) :
    RatPolyCoeffEqv (partialHaarHead (translatedHeadMonomial
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) e0 e1 e2 e3))
      (polySmul (headQuaternionMoment (headExponentLedger e0 e1 e2 e3))
        (ratPolyPow (quaternionRadiusPolynomial 0) ((e0 + e1 + e2 + e3) / 2))) := by
  have hd := translatedHeadMonomial_head_degree right e0 e1 e2 e3
  by_cases heven : (e0 + e1 + e2 + e3) % 2 = 0
  · have heq : e0 + e1 + e2 + e3 = 2 * ((e0 + e1 + e2 + e3) / 2) := by omega
    have hr := partialHaarHead_mul_radial _ _ (HasQuaternionBlockDegree.relabel heq hd)
    have hm := headMoment_mul_commonRadialDenominator
      (headExponentLedger e0 e1 e2 e3) ((e0 + e1 + e2 + e3) / 2)
      ((ledger_degree e0 e1 e2 e3).trans heq)
    have hm' : Q'.ofNat (sphereFourDenominator ((e0 + e1 + e2 + e3) / 2)) *
        headQuaternionMoment (headExponentLedger e0 e1 e2 e3) ≈ gaussianMoment4 e0 e1 e2 e3 :=
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) hm
    apply coeffEqv_of_positive_smul (radialDenominator_positive ((e0 + e1 + e2 + e3) / 2))
    exact hr.trans ((translatedHeadMonomial_gaussian_closed right e0 e1 e2 e3).trans
      ((RatPolyCoeffEqv.smul_assoc _ _ _).trans (RatPolyCoeffEqv.smul_coefficient hm' _)).symm)
  · have ho : HeadQuaternionOdd (translatedHeadMonomial
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) e0 e1 e2 e3) := by
      intro term ht
      have htdegree := hd term ht
      change headQuaternionDegree term.1 = e0 + e1 + e2 + e3 at htdegree
      rw [htdegree]
      omega
    have hm : headQuaternionMoment (headExponentLedger e0 e1 e2 e3) = 0 :=
      headQuaternionMoment_eq_zero_of_odd (by change (e0 + e1 + e2 + e3) % 2 = 1; omega)
    rw [hm]
    exact (partialHaarHead_eq_zero_of_odd _ ho).trans (RatPolyCoeffEqv.zero_smul _).symm

theorem radius_power_eq_iter (block : Nat) : ∀ n : Nat,
    ratPolyPow (quaternionRadiusPolynomial block) n = quaternionRadiusIter block n polyOne
  | 0 => rfl
  | n + 1 => congrArg (fun p => polyMul p (quaternionRadiusPolynomial block)) (radius_power_eq_iter block n)

/-- The exact moment equality required by the original translation API,
now at all degrees without an executable-check hypothesis. -/
theorem translatedHeadMonomial_haar_expected (right : Bool) (e0 e1 e2 e3 : Nat) :
    RatPolyCoeffEqv (partialHaarHead (translatedHeadMonomial
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) e0 e1 e2 e3))
      (expectedTranslatedHeadMoment e0 e1 e2 e3) := by
  simpa only [radius_power_eq_iter, expectedTranslatedHeadMoment]
    using translatedHeadMonomial_haar_closed right e0 e1 e2 e3

end YMGap.Continuum.SU2QuaternionTranslationHaarMoments

#print axioms YMGap.Continuum.SU2QuaternionTranslationHaarMoments.translatedQuaternion_head_degree
#print axioms YMGap.Continuum.SU2QuaternionTranslationHaarMoments.translatedHeadMonomial_head_degree
#print axioms YMGap.Continuum.SU2QuaternionTranslationHaarMoments.translatedHeadMonomial_haar_closed
#print axioms YMGap.Continuum.SU2QuaternionTranslationHaarMoments.radius_power_eq_iter
#print axioms YMGap.Continuum.SU2QuaternionTranslationHaarMoments.translatedHeadMonomial_haar_expected
