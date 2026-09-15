/-
# Collar-dressed tests approximate ORIGINAL OS vectors

The correction is used on TEST expressions, never as an operator on the
OS null quotient. Their actual normalized reflected norms have a cap
bound(e)*4, independent of correction cutoff and degree. More importantly,
H*(e*G_n)-e has original OS squared norm at most bound(e)*2^(-2n).
Thus collar-dressed tests approximate the unchanged original test vector,
with an explicit order and no reciprocal-partition ceiling.

H and G_n use the fixed nome 1/1024. The certificate can be evaluated in
any of the existing original finite-slab cutoff-limit actions 0<w<1;
this is a size/approximation bound, NOT a coupling-uniform spectral gap.
No thermodynamic separation, OS multiplier or time-transfer inverse follows
without the respective additional construction and same-object pins.
-/

import YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector
import YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound

namespace YMGap.Continuum.BF4ExactSlabCollarTestNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression
open YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient (subtract)
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin
open YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "hw" => Q'.le_of_lt nome_pos

private def squareOfInterval {blockCount : Nat} {p : RatPoly} {c : Q'} (P : Interval blockCount p c) :
    SquareBound blockCount p (c*c) where
  support := P.support
  nonnegative := Q'.mul_nonneg _ _ P.nonnegative P.nonnegative
  certificate := (P.mul P).upper

def correctedLowerSquare (K n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    SquareBound (blocks half) (lower (correctedExpression K n e)) (bound e * 4) :=
  (lowerBound e).mul ((squareOfInterval (correctionLowerInterval K half n)).changeCap (by decide))

def correctedUpperSquare (K n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    SquareBound (blocks half) (upper (correctedExpression K n e)) (bound e * 4) :=
  (upperBound e).mul ((squareOfInterval (correctionUpperInterval K half n)).changeCap (by decide))

/-- The reference cap depends on the source expression, not its correction degree. -/
theorem corrected_form_bound (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    leEv (form w hw0 hw1 (correctedExpression K n e) (correctedExpression K n e)) (ofQ' (bound e * 4)) :=
  expectation_upper w hw0 hw1 half _ _ ((correctedUpperSquare K n e).cross (correctedLowerSquare K n e))

theorem unchanged_pairing_bound (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K n : Nat) {half : Nat} (e f : PlaquetteExpression half) :
    leEv (CReal.mul (form w hw0 hw1 e (correctedExpression K n f)) (form w hw0 hw1 e (correctedExpression K n f)))
      (CReal.mul (form w hw0 hw1 e e) (ofQ' (bound f * 4))) :=
  leEv_trans (form_cauchySchwarz w hw0 hw1 e _)
    (leEv_mul_nonneg_left (form_nonnegative w hw0 hw1 e) (corrected_form_bound w hw0 hw1 K n f))

/-- In the image of multiplication by H on expressions, without quotient descent. -/
def collarApproximation (K n : Nat) {half : Nat} (e : PlaquetteExpression half) : PlaquetteExpression half :=
  .mul (collarExpression nome K half) (correctedExpression K n e)

def approximationError (K n : Nat) {half : Nat} (e : PlaquetteExpression half) : PlaquetteExpression half :=
  subtract (collarApproximation K n e) e

private theorem error_coeff {p H H' G G' : RatPoly} (hH : RatPolyCoeffEqv H H') (hG : RatPolyCoeffEqv G G') :
    RatPolyCoeffEqv (polyAdd (polyMul H (polyMul p G)) (polySmul (-1) p))
      (polyMul p (polyAdd (polyMul H' G') (polyNeg polyOne))) :=
  ((hH.mul ((RatPolyCoeffEqv.refl p).mul hG)).add (cap_mul_left (-1) p).symm).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 1) (.mul (.var 0) (.var 2))) (.mul (.const (-1)) (.var 0)))
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.const 1))))
      (by decide) (fun | 0 => p | 1 => H' | _ => G'))

theorem approximationError_lower (K n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    RatPolyCoeffEqv (lower (approximationError K n e))
      (polyMul (lower e) (defect (collarHeat nome K half)
        (productPerturbation nome (centralExtent half) K (lowerCollar half)) n)) :=
  error_coeff (collarExpression_lower nome K half) (correctionExpression_lower K half n)

theorem approximationError_upper (K n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    RatPolyCoeffEqv (upper (approximationError K n e))
      (polyMul (upper e) (defect (upperCollarHeat nome K half) (collarRemainder K half) n)) :=
  error_coeff (collarExpression_upper nome K half) (correctionExpression_upper K half n)

def errorLowerSquare (K n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    SquareBound (blocks half) (lower (approximationError K n e)) (bound e * (HalfPow.half^n * HalfPow.half^n)) :=
  .ofCoeff (lower_supported _) (approximationError_lower K n e)
    ((lowerBound e).mul (squareOfInterval (defectInterval (product_eq_one_add nome (centralExtent half) K _)
      (BF4ExactSlabFaceLinkLocality.heatProduct_supported nome K _ _) (collarInterval hw (Q'.le_of_lt nome_lt_one) existingNome_guards.1 K half)
      collar_cap_half n)))

def errorUpperSquare (K n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    SquareBound (blocks half) (upper (approximationError K n e)) (bound e * (HalfPow.half^n * HalfPow.half^n)) :=
  .ofCoeff (upper_supported _) (approximationError_upper K n e)
    ((upperBound e).mul (squareOfInterval (defectInterval (collar_heat_pin K half)
      (upperCollarHeat_supported nome K half) (collarRemainderInterval K half) collar_cap_half n)))

/-- A bound in the actual normalized reflected form, not only ordinary Haar L2. -/
theorem approximation_error_bound (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    leEv (form w hw0 hw1 (approximationError K n e) (approximationError K n e))
      (ofQ' (bound e * (HalfPow.half^n * HalfPow.half^n))) :=
  expectation_upper w hw0 hw1 half _ _ ((errorUpperSquare K n e).cross (errorLowerSquare K n e))

private theorem half_power_le_one : ∀ n : Nat, HalfPow.half^n ≤ (1 : Q')
  | 0 => Q'.le_refl' _
  | n+1 => Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (half_power_le_one n) HalfPow.half_nonneg)
      (by decide : HalfPow.half*1 ≤ (1 : Q'))

/-- Computes the degree from the source test and a squared-distance tolerance. -/
def approximationOrder {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  correctionOrder (bound e) (bound_nonnegative e) epsilon

theorem approximation_order_budget {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon) :
    bound e * (HalfPow.half^(approximationOrder e epsilon) * HalfPow.half^(approximationOrder e epsilon)) ≤ epsilon := by
  let n := approximationOrder e epsilon
  have h : HalfPow.half^n * HalfPow.half^n ≤ HalfPow.half^n :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (half_power_le_one n)
      (Q'.pow_nonneg _ HalfPow.half_nonneg n)) (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h (bound_nonnegative e))
    (correctionOrder_budget (bound e) (bound_nonnegative e) epsilon he)

theorem approximation_error_atOrder (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K : Nat) {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon) :
    leEv (form w hw0 hw1 (approximationError K (approximationOrder e epsilon) e)
      (approximationError K (approximationOrder e epsilon) e)) (ofQ' epsilon) :=
  leEv_trans (approximation_error_bound w hw0 hw1 K _ e)
    (leEv_ofQ'_of_approx_ge (fun _ => approximation_order_budget e epsilon he))

end YMGap.Continuum.BF4ExactSlabCollarTestNorm

#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.correctedLowerSquare
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.correctedUpperSquare
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.corrected_form_bound
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.unchanged_pairing_bound
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.collarApproximation
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.approximationError
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.approximationError_lower
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.approximationError_upper
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.errorLowerSquare
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.errorUpperSquare
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.approximation_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.approximationOrder
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.approximation_order_budget
#print axioms YMGap.Continuum.BF4ExactSlabCollarTestNorm.approximation_error_atOrder
