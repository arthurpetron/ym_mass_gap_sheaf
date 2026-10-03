/-
# Literal Haar-weighted nome coefficient polynomials

The numerator is a finite padd/pscale fold of the actual Haar pairings of
each polynomial-valued row. Its derivative is the literal QPoly pderiv.
Evaluation, Euler and Laurent pins retain the SAME arbitrary output weight.
No positivity, support, nonzero-nome or endpoint-order premise is used here.
The consumer is the original heat interpolation under certified output
weights; these algebraic pins alone assert no derivative sign or variance
estimate, and no changing-family or physical conclusion.
-/

import YMGap.Continuum.RatPolyNomeRows
import YMGap.Continuum.RationalLaurentIntervalOrder
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.QuaternionHaarNomeRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar quaternionHaarMono)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.RatPolyNomeRows
open YMGap.Continuum.RationalLaurentIntervalOrder (laurent)

local infix:50 " ≈ " => Q'.eqv

/-- Finite coefficient polynomial, with the original Haar weight inserted
before each row is integrated. -/
def weightedNumerator (blocks : Nat) (W : RatPoly) : Rows → Poly
  | [] => []
  | a::A => padd
      (pscale (quaternionHaar blocks (polyMul W a.2)) a.1)
      (weightedNumerator blocks W A)

private theorem weighted_add (blocks : Nat) (W p q : RatPoly) :
    quaternionHaar blocks (polyMul W (polyAdd p q)) ≈
      quaternionHaar blocks (polyMul W p) + quaternionHaar blocks (polyMul W q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks)
    (RatPolyCoeffEqv.mul_add_right W p q))
    (quaternionHaar_append blocks _ _)

/-- Exact evaluation at every rational nome, including zero and signed nomes. -/
theorem weightedNumerator_eval (blocks : Nat) (W : RatPoly) (A : Rows) (r : Q') :
    QPoly.eval (weightedNumerator blocks W A) r ≈
      quaternionHaar blocks (polyMul W (evalRows A r)) := by
  induction A with
  | nil =>
      exact Q'.eqv_symm (haar_of_coeff (blocks := blocks)
        (RatPolyCoeffEqv.mul_zero_right W))
  | cons a A ih =>
      change QPoly.eval (padd (pscale (quaternionHaar blocks (polyMul W a.2)) a.1)
        (weightedNumerator blocks W A)) r ≈
        quaternionHaar blocks (polyMul W
          (polyAdd (polySmul (QPoly.eval a.1 r) a.2) (evalRows A r)))
      exact Q'.eqv_trans _ _ _ (eval_padd _ _ r)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ (eval_pscale _ a.1 r)
              (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
                (Q'.eqv_symm (quaternionHaar_polyMul_smul_right blocks _ W a.2)))) ih)
          (Q'.eqv_symm (weighted_add blocks W _ _)))

private theorem weightedNumerator_derivative_coeff (blocks : Nat) (W : RatPoly)
    (A : Rows) :
    CoeffEqv (pderiv (weightedNumerator blocks W A))
      (weightedNumerator blocks W (derivativeRows A)) := by
  induction A with
  | nil => exact .refl _
  | cons a A ih =>
      change CoeffEqv
        (pderiv (padd (pscale (quaternionHaar blocks (polyMul W a.2)) a.1)
          (weightedNumerator blocks W A)))
        (padd (pscale (quaternionHaar blocks (polyMul W a.2)) (pderiv a.1))
          (weightedNumerator blocks W (derivativeRows A)))
      exact (pderiv_padd _ _).trans ((pderiv_pscale _ _).padd ih)

/-- The actual formal derivative of the literal coefficient fold evaluates
to the Haar pairing of the literal row derivatives. -/
theorem weightedNumerator_derivative_eval (blocks : Nat) (W : RatPoly)
    (A : Rows) (r : Q') :
    QPoly.eval (pderiv (weightedNumerator blocks W A)) r ≈
      quaternionHaar blocks (polyMul W (evalRows (derivativeRows A) r)) :=
  Q'.eqv_trans _ _ _
    (coefficient_eval (weightedNumerator_derivative_coeff blocks W A) r)
    (weightedNumerator_eval blocks W (derivativeRows A) r)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -quaternionHaar blocks p
  | [] => by change (0 : Q') ≈ -0; decide
  | a::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv a.2 (quaternionHaarMono blocks a.1))
        (haar_neg blocks p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem weighted_neg (blocks : Nat) (W p : RatPoly) :
    quaternionHaar blocks (polyMul W (polyNeg p)) ≈
      -quaternionHaar blocks (polyMul W p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks)
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => W | _ => p)))
    (haar_neg blocks _)

/-- Literal cleared Euler derivative, with the SAME weight and shared
polynomial variables. No denominator is inverted in this identity. -/
theorem weightedNumerator_euler_eval (blocks : Nat) (W : RatPoly)
    (A : Rows) (E : Nat) (r : Q') :
    r * QPoly.eval (pderiv (weightedNumerator blocks W A)) r -
        Q'.ofNat E * QPoly.eval (weightedNumerator blocks W A) r ≈
      quaternionHaar blocks (polyMul W (evalRows (eulerRows E A) r)) := by
  have hp := haar_of_coeff (blocks := blocks)
    (RatPolyCoeffEqv.mul_left W (evalRows_euler_pin E A r))
  have he : quaternionHaar blocks (polyMul W (evalRows (eulerRows E A) r)) ≈
      r * quaternionHaar blocks (polyMul W (evalRows (derivativeRows A) r)) +
        -(Q'.ofNat E * quaternionHaar blocks (polyMul W (evalRows A r))) :=
    Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (weighted_add blocks W _ _)
        (Q'.add_eqv_congr'
          (quaternionHaar_polyMul_smul_right blocks r W _)
          (Q'.eqv_trans _ _ _ (weighted_neg blocks W _)
            (Q'.neg_eqv_congr _ _ (quaternionHaar_polyMul_smul_right blocks (Q'.ofNat E) W _)))))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left r _ _ (weightedNumerator_derivative_eval blocks W A r))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat E) _ _ (weightedNumerator_eval blocks W A r))))
    (Q'.eqv_symm he)

/-- The original Laurent value equals the original weighted row evaluation.
Total reciprocal is used identically on both sides, so even r=0 is included. -/
theorem weightedNumerator_laurent_pin (blocks : Nat) (W : RatPoly)
    (A : Rows) (E : Nat) (r : Q') :
    laurent (weightedNumerator blocks W A) E r ≈
      quaternionHaar blocks
        (polyMul W (polySmul (Q'.recip (RGTransport.qpow r E)) (evalRows A r))) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (weightedNumerator_eval blocks W A r))
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.eqv_symm (quaternionHaar_polyMul_smul_right blocks _ W _)))

end YMGap.Continuum.QuaternionHaarNomeRows

#print axioms YMGap.Continuum.QuaternionHaarNomeRows.weightedNumerator
#print axioms YMGap.Continuum.QuaternionHaarNomeRows.weightedNumerator_eval
#print axioms YMGap.Continuum.QuaternionHaarNomeRows.weightedNumerator_derivative_eval
#print axioms YMGap.Continuum.QuaternionHaarNomeRows.weightedNumerator_euler_eval
#print axioms YMGap.Continuum.QuaternionHaarNomeRows.weightedNumerator_laurent_pin
