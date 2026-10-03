/-
# Original shared-output square and energy heat interpolation

The finite functions are C_(w/r)[V(r)^2] and C_(w/r)[Gamma(V(r))],
where V is the original saturated input heat flow. Their Euler data are
literal pderiv of the explicit common-denominator coefficient rows.
Both generator/product/chain joins are proved under every surviving Haar
insertion, with the original retained output and all shared spectators.
No kernel positivity, conditional variance, interacting estimate or
continuum/physical mass-gap statement is asserted by these identities.
-/

import YMGap.Continuum.SU2QuaternionConditionalLaurentRows
import YMGap.Continuum.SU2QuaternionHeadHeatCurves

namespace YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian (partialHaarHead_congr)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration (partialHaarHead_smul)
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionConditionalHeatComposition (conditionalHeat_carrier)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarExposedHeatCasimir (angularLaplacian_carrier)
open YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy (angularLaplacian_square)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.SU2QuaternionAngularBochner (mixedGamma gamma2)
open YMGap.Continuum.SU2QuaternionHeadHeatGenerator (finiteNomeFlow)
open YMGap.Continuum.SU2QuaternionHeadHeatCurves
open YMGap.Continuum.RatPolyNomeRows
open YMGap.Continuum.SU2QuaternionConditionalLaurentRows

/-- Actual common-denominator square interpolation, not a surrogate. -/
def squareInterpolation (tail : Nat) (w : Q') (K : Nat) (p : RatPoly) (r : Q') : RatPoly :=
  conditionalLaurentValue w K (squareNomeRows tail p) r

/-- Actual common-denominator angular-energy interpolation. -/
def angularInterpolation (tail : Nat) (w : Q') (K : Nat) (p : RatPoly) (r : Q') : RatPoly :=
  conditionalLaurentValue w K (angularNomeRows tail p) r

/-- Literal finite numerator Euler derivative divided by its original power. -/
def squareInterpolationEuler (tail : Nat) (w : Q') (K : Nat) (p : RatPoly) (r : Q') : RatPoly :=
  conditionalLaurentEuler w K (squareNomeRows tail p) r

/-- Literal finite numerator Euler derivative for the SAME energy function. -/
def angularInterpolationEuler (tail : Nat) (w : Q') (K : Nat) (p : RatPoly) (r : Q') : RatPoly :=
  conditionalLaurentEuler w K (angularNomeRows tail p) r

private theorem conditional_coeff (w : Q') (K : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (conditionalHeat w K p) (conditionalHeat w K q) :=
  partialHaarHead_congr (h.mul_left (relativeHeat w K))

private theorem conditional_smul (w c : Q') (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat w K (polySmul c p)) (polySmul c (conditionalHeat w K p)) :=
  (partialHaarHead_congr (RatPolyCoeffEqv.polyMul_smul_right c (relativeHeat w K) p)).trans
    (partialHaarHead_smul c _)

theorem squareInterpolation_original_pin (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (r : Q') (hr : (0 : Q') < r) :
    RatPolyCoeffEqv (squareInterpolation tail w K p r)
      (conditionalHeat (w*Q'.recip r) K
        (polyMul (finiteNomeFlow tail p r) (finiteNomeFlow tail p r))) :=
  (conditionalLaurentValue_original_pin w K (squareNomeRows tail p) r hr).trans
    (conditional_coeff _ _ (squareNomeRows_eval tail p r))

theorem angularInterpolation_original_pin (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (r : Q') (hr : (0 : Q') < r) :
    RatPolyCoeffEqv (angularInterpolation tail w K p r)
      (conditionalHeat (w*Q'.recip r) K (angularSquare (finiteNomeFlow tail p r))) :=
  (conditionalLaurentValue_original_pin w K (angularNomeRows tail p) r hr).trans
    (conditional_coeff _ _ (angularNomeRows_eval tail p r))

private theorem add_cancel (a b : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polyAdd a b) (polyNeg b)) a :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
    (by decide) (fun | 0 => a | _ => b)

private theorem scale_neg (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul c (polyNeg p)) (polyNeg (polySmul c p)) :=
  ((neg_smul p).smul c).trans
    ((RatPolyCoeffEqv.smul_assoc c (-1) p).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv c (-1)) p).trans
        ((RatPolyCoeffEqv.smul_assoc (-1) c p).symm.trans (neg_smul _).symm)))

private theorem one_scale (p : RatPoly) : RatPolyCoeffEqv (polySmul 1 p) p :=
  (cap_mul_left 1 p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const 1) (.var 0)) (.var 0)
      (by decide) (fun _ => p))

private theorem gamma2_twice (p : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (angularLaplacian (angularSquare p))
        (polyNeg (polySmul 2 (mixedGamma p (angularLaplacian p)))))
      (polySmul 2 (gamma2 p)) := by
  have hh : RatPolyCoeffEqv
      (polySmul 2 (polySmul HalfPow.half (angularLaplacian (angularSquare p))))
      (angularLaplacian (angularSquare p)) :=
    (RatPolyCoeffEqv.smul_assoc 2 HalfPow.half _).trans
      ((RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv ((2 : Q')*HalfPow.half) 1) _).trans
        (one_scale _))
  exact ((RatPolyCoeffEqv.smul_add 2 _ _).trans
    (hh.add (scale_neg 2 _))).symm

/-- Exact square product/chain cancellation on the ORIGINAL conditional
carrier: r F'(r)=2 C_(w/r)[Gamma(V(r))]. Euler means literal pderiv rows. -/
theorem squareInterpolation_euler (tail : Nat) (ht : 0 < tail) (w : Q') (K : Nat)
    (p : RatPoly) (r : Q') (hr : (0 : Q') < r)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv tail (squareInterpolationEuler tail w K p r)
      (polySmul 2 (conditionalHeat (w*Q'.recip r) K (angularSquare (finiteNomeFlow tail p r)))) := by
  let V := finiteNomeFlow tail p r
  have hL := angularLaplacian_carrier (Nat.zero_lt_succ tail)
    (RatPolyCoeffEqv.haarCarrier (squareNomeRows_eval tail p r))
  have hD : HaarCarrierEqv (tail+1)
      (polySmul r (evalRows (derivativeRows (squareNomeRows tail p)) r))
      (polyNeg (polySmul 2 (polyMul V (angularLaplacian V)))) :=
    squareNomeCurve_formal_generator tail p r hp
  have hc : RatPolyCoeffEqv
      (polyAdd (angularLaplacian (polyMul V V))
        (polyNeg (polySmul 2 (polyMul V (angularLaplacian V)))))
      (polySmul 2 (angularSquare V)) :=
    ((angularLaplacian_square V).add (RatPolyCoeffEqv.refl _)).trans (add_cancel _ _)
  exact (conditionalLaurentEuler_input_generator tail ht w K (squareNomeRows tail p) r hr).trans
    ((conditionalHeat_carrier tail _ K
      ((hL.add hD).trans (RatPolyCoeffEqv.haarCarrier hc))).trans
        (RatPolyCoeffEqv.haarCarrier (conditional_smul _ 2 K _)))

/-- Exact iterated-energy product/chain join on the SAME original carrier:
r G'(r)=2 C_(w/r)[Gamma2(V(r))], before any positivity/order claim. -/
theorem angularInterpolation_euler (tail : Nat) (ht : 0 < tail) (w : Q') (K : Nat)
    (p : RatPoly) (r : Q') (hr : (0 : Q') < r)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv tail (angularInterpolationEuler tail w K p r)
      (polySmul 2 (conditionalHeat (w*Q'.recip r) K (gamma2 (finiteNomeFlow tail p r)))) := by
  let V := finiteNomeFlow tail p r
  have hL := angularLaplacian_carrier (Nat.zero_lt_succ tail)
    (RatPolyCoeffEqv.haarCarrier (angularNomeRows_eval tail p r))
  have hD : HaarCarrierEqv (tail+1)
      (polySmul r (evalRows (derivativeRows (angularNomeRows tail p)) r))
      (polyNeg (polySmul 2 (mixedGamma V (angularLaplacian V)))) :=
    angularNomeCurve_formal_generator tail p r hp
  exact (conditionalLaurentEuler_input_generator tail ht w K (angularNomeRows tail p) r hr).trans
    ((conditionalHeat_carrier tail _ K
      ((hL.add hD).trans (RatPolyCoeffEqv.haarCarrier (gamma2_twice V)))).trans
        (RatPolyCoeffEqv.haarCarrier (conditional_smul _ 2 K _)))

end YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation

#print axioms YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation.squareInterpolation
#print axioms YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation.angularInterpolation
#print axioms YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation.squareInterpolationEuler
#print axioms YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation.angularInterpolationEuler
#print axioms YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation.squareInterpolation_original_pin
#print axioms YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation.angularInterpolation_original_pin
#print axioms YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation.squareInterpolation_euler
#print axioms YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation.angularInterpolation_euler
