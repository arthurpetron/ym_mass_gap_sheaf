/-
# Finite reciprocal-corrected cross comparison

The denominators remain actual positive polynomials. A finite geometric
corrector is multiplied into the denominator-cleared certificate, and both
residuals are retained with their constructive signs. No configurationwise
division, limiting inverse, or replica-specific hypothesis is used.
-/

import YMGap.Continuum.QuaternionHaarCrossNormalizedComparison
import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini

namespace YMGap.Continuum.QuaternionHaarReciprocalCrossComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarCrossNormalizedComparison
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini

/-- Positivity of the finite corrector follows from the certified sign of
the geometric remainder; this is not inferred from an interval alone. -/
def correctorCertificate {n : Nat} {R : RatPoly}
    (negative : Certificate n (polyNeg R)) :
    (k : Nat) → Certificate n (corrector R k)
  | 0 => .ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (.constant n 0 (by decide))
  | k + 1 => (Certificate.one n).add (negative.mul (correctorCertificate negative k))

/-- The actual finite reciprocal polynomial is nonnegative on every
supported Haar square insertion. -/
def reciprocalCertificate {n : Nat} {D : RatPoly} (U : Q')
    (hU : (0 : Q') < U)
    (DCap : Certificate n (polyAdd (cap U) (polyNeg D))) (k : Nat) :
    Certificate n (reciprocal D U hU k) :=
  .smul (scale U hU) (Q'.le_of_lt (scale_positive U hU))
    (correctorCertificate (remainderNegative hU DCap) k)

private theorem residual_as_sub (D G e : RatPoly)
    (h : RatPolyCoeffEqv (polyAdd (polyMul D G) e) polyOne) :
    RatPolyCoeffEqv e (polyAdd polyOne (polyNeg (polyMul D G))) :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.var 0) (.add (.add (.var 1) (.var 0)) (.neg (.var 1)))
    (by decide) (fun | 0 => e | _ => polyMul D G)).trans
    (RatPolyCoeffEqv.add h (RatPolyCoeffEqv.refl _))

private theorem eval_congr (left right : Nat → RatPoly)
    (h : ∀ i, RatPolyCoeffEqv (left i) (right i)) :
    ∀ expression : PolyExpr,
      RatPolyCoeffEqv (coeffEvalExpr left expression) (coeffEvalExpr right expression)
  | .const _ => RatPolyCoeffEqv.refl _
  | .var i => h i
  | .add a b => RatPolyCoeffEqv.add (eval_congr left right h a) (eval_congr left right h b)
  | .mul a b => RatPolyCoeffEqv.mul (eval_congr left right h a) (eval_congr left right h b)
  | .neg a => RatPolyCoeffEqv.neg (eval_congr left right h a)
  | .pow a k => coeffPolyPow_congr (eval_congr left right h a) k

private def diffExpr (a b : PolyExpr) : PolyExpr := .add a (.neg b)

-- Variables: p=0, q=1, D=2, E=3, G_D=4, G_E=5,
-- e_D=6, e_E=7, U²=8, ell²=9, rho^k=10, unit=11.
private def leftExpr : PolyExpr :=
  diffExpr
    (.mul (.mul (.var 8) (.mul (.var 0) (.var 4))) (.var 11))
    (.mul (.var 9)
      (.mul (diffExpr (.var 11) (.var 10))
        (.mul (.var 1) (.var 5))))

private def rightExpr (ed ee : PolyExpr) : PolyExpr :=
  .add
    (.add
      (.mul
        (diffExpr
          (.mul (.var 8) (.mul (.var 0) (.var 3)))
          (.mul (.var 9) (.mul (.var 1) (.var 2))))
        (.mul (.var 4) (.var 5)))
      (.mul (.var 8) (.mul (.var 0) (.mul (.var 4) ee))))
    (.mul (.var 9)
      (.mul (.var 1)
        (.mul (.var 5) (diffExpr (.var 10) ed))))

private theorem corrected_cross_ring :
    normalize leftExpr =
      normalize (rightExpr
        (diffExpr (.var 11) (.mul (.var 2) (.var 4)))
        (diffExpr (.var 11) (.mul (.var 3) (.var 5)))) := by decide

/-- Actual finite reciprocal comparison with its residual retained.

Writing `G_D,G_E` for the finite reciprocal polynomials and
`rho=radius ell U`, the certificate says
`U² p G_D ≥ ell² (1-rho^k) q G_E` under every supported Haar square
insertion. The correction factor is written as the literal polynomial
`1 - cap(rho^k)` so no division or scalar-order transport is hidden. -/
def reciprocalCrossComparisonOfCross {n : Nat} (p q D E : RatPoly) (ell U : Q')
    (hell : (0 : Q') < ell) (hU : (0 : Q') < U) (hle : ell ≤ U)
    (hD : SupportedQuaternionBlocks n D)
    (P : Certificate n p) (Q : Certificate n q)
    (H : Certificate n
      (polyAdd (polyMul (cap (U*U)) (polyMul p E))
        (polyNeg (polyMul (cap (ell*ell)) (polyMul q D)))))
    (DCap : Certificate n (polyAdd (cap U) (polyNeg D)))
    (DFloor : Certificate n (polyAdd D (polyNeg (cap ell))))
    (ECap : Certificate n (polyAdd (cap U) (polyNeg E)))
    (k : Nat) :
    let GD := reciprocal D U hU k
    let GE := reciprocal E U hU k
    let rho := radius ell U hU
    Certificate n
      (polyAdd
        (polyMul (cap (U*U)) (polyMul p GD))
        (polyNeg (polyMul (cap (ell*ell))
          (polyMul (polyAdd polyOne (polyNeg (cap (rho^k))))
            (polyMul q GE))))) := by
  let GD := reciprocal D U hU k
  let GE := reciprocal E U hU k
  let eD := residual (remainder D U hU) k
  let eE := residual (remainder E U hU) k
  let r := (radius ell U hU)^k
  let A := cap (U*U)
  let B := cap (ell*ell)
  let C := polyAdd (polyMul A (polyMul p E))
    (polyNeg (polyMul B (polyMul q D)))
  have hGD : Certificate n GD := reciprocalCertificate U hU DCap k
  have hGE : Certificate n GE := reciprocalCertificate U hU ECap k
  have heE : Certificate n eE :=
    residualCertificate (remainderNegative hU ECap) k
  have heDcap : Certificate n (polyAdd (cap r) (polyNeg eD)) :=
    (residualInterval (remainderInterval hD hU hle DFloor DCap) k).upper
  have hC : Certificate n C := H
  have hpositive : Certificate n
      (polyAdd
        (polyAdd
          (polyMul C (polyMul GD GE))
          (polyMul A (polyMul p (polyMul GD eE))))
        (polyMul B
          (polyMul q (polyMul GE (polyAdd (cap r) (polyNeg eD)))))) :=
    ((hC.mul (hGD.mul hGE)).add
      ((Certificate.constant n (U*U)
        (Q'.mul_nonneg U U (Q'.le_of_lt hU) (Q'.le_of_lt hU))).mul
        (P.mul (hGD.mul heE)))).add
      ((Certificate.constant n (ell*ell)
        (Q'.mul_nonneg ell ell (Q'.le_of_lt hell) (Q'.le_of_lt hell))).mul
        (Q.mul (hGE.mul heDcap)))
  have hresD : RatPolyCoeffEqv eD
      (polyAdd polyOne (polyNeg (polyMul D GD))) :=
    residual_as_sub D GD eD (reciprocal_cancellation D U hU k)
  have hresE : RatPolyCoeffEqv eE
      (polyAdd polyOne (polyNeg (polyMul E GE))) :=
    residual_as_sub E GE eE (reciprocal_cancellation E U hU k)
  let common : Nat → RatPoly
    | 0 => p | 1 => q | 2 => D | 3 => E | 4 => GD | 5 => GE
    | 8 => A | 9 => B | 10 => cap r | _ => polyOne
  let actual : Nat → RatPoly := fun i =>
    if i = 6 then eD else if i = 7 then eE else common i
  let substituted : Nat → RatPoly := fun i =>
    if i = 6 then polyAdd polyOne (polyNeg (polyMul D GD))
    else if i = 7 then polyAdd polyOne (polyNeg (polyMul E GE))
    else common i
  have henv (i : Nat) : RatPolyCoeffEqv (actual i) (substituted i) := by
    by_cases h6 : i = 6
    · simpa only [actual, substituted, if_pos h6] using hresD
    · by_cases h7 : i = 7
      · simpa only [actual, substituted, if_neg h6, if_pos h7] using hresE
      · simpa only [actual, substituted, if_neg h6, if_neg h7] using
          (RatPolyCoeffEqv.refl (common i))
  have hring : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul A (polyMul p GD)) polyOne)
        (polyNeg (polyMul B
          (polyMul (polyAdd polyOne (polyNeg (cap r))) (polyMul q GE)))))
      (polyAdd
        (polyAdd
          (polyMul C (polyMul GD GE))
          (polyMul A (polyMul p (polyMul GD eE))))
        (polyMul B
          (polyMul q (polyMul GE (polyAdd (cap r) (polyNeg eD)))))) := by
    have hpure := coeffEvalExpr_eqv_of_normalize_eq
      leftExpr
      (rightExpr
        (diffExpr (.var 11) (.mul (.var 2) (.var 4)))
        (diffExpr (.var 11) (.mul (.var 3) (.var 5))))
      corrected_cross_ring actual
    have hreplace := eval_congr actual substituted henv
      (rightExpr (.var 6) (.var 7))
    change RatPolyCoeffEqv (coeffEvalExpr actual leftExpr)
      (coeffEvalExpr actual (rightExpr (.var 6) (.var 7)))
    exact hpure.trans hreplace.symm
  have hleft : RatPolyCoeffEqv
      (polyAdd (polyMul A (polyMul p GD))
        (polyNeg (polyMul B
          (polyMul (polyAdd polyOne (polyNeg (cap r))) (polyMul q GE)))))
      (polyAdd (polyMul (polyMul A (polyMul p GD)) polyOne)
        (polyNeg (polyMul B
          (polyMul (polyAdd polyOne (polyNeg (cap r))) (polyMul q GE))))) :=
    RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_one _).symm (RatPolyCoeffEqv.refl _)
  exact .ofCoeff (hleft.trans hring) hpositive

/-- Convenience constructor when the raw cross comparison follows just from
four independent lower/upper factor certificates. -/
def reciprocalCrossComparison {n : Nat} (p q D E : RatPoly) (ell U : Q')
    (hell : (0 : Q') < ell) (hU : (0 : Q') < U) (hle : ell ≤ U)
    (hD : SupportedQuaternionBlocks n D)
    (P : Certificate n p) (Q : Certificate n q)
    (DD : Certificate n D) (EE : Certificate n E)
    (pFloor : Certificate n (polyAdd p (polyNeg (cap ell))))
    (EFloor : Certificate n (polyAdd E (polyNeg (cap ell))))
    (qCap : Certificate n (polyAdd (cap U) (polyNeg q)))
    (DCap : Certificate n (polyAdd (cap U) (polyNeg D)))
    (DFloor : Certificate n (polyAdd D (polyNeg (cap ell))))
    (ECap : Certificate n (polyAdd (cap U) (polyNeg E)))
    (k : Nat) :
    let GD := reciprocal D U hU k
    let GE := reciprocal E U hU k
    let rho := radius ell U hU
    Certificate n
      (polyAdd
        (polyMul (cap (U*U)) (polyMul p GD))
        (polyNeg (polyMul (cap (ell*ell))
          (polyMul (polyAdd polyOne (polyNeg (cap (rho^k))))
            (polyMul q GE))))) :=
  reciprocalCrossComparisonOfCross p q D E ell U hell hU hle hD P Q
    (crossProductComparison p q D E ell U
      (Q'.le_of_lt hell) (Q'.le_of_lt hU)
      P Q DD EE pFloor EFloor qCap DCap)
    DCap DFloor ECap k

#print axioms correctorCertificate
#print axioms reciprocalCertificate
#print axioms reciprocalCrossComparisonOfCross
#print axioms reciprocalCrossComparison

end YMGap.Continuum.QuaternionHaarReciprocalCrossComparison
