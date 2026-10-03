/-
Actual finite coefficient data for the truncated series
`sum_{k<n} p^(k+1)/(k+1)`.  Its FORMAL derivative is the finite geometric
polynomial multiplied by `p'`.  This is a polynomial identity over the rational
setoid; no analytic logarithm, infinite series, or operator identification is
assumed.
-/

import YMGap.Constructive.QPolyFiniteGeometric

namespace YMGap.Constructive.QPolyFiniteLogDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyFiniteGeometric
open YMGap.Constructive.RationalTail

/-- Computed finite truncated logarithmic series in an arbitrary polynomial. -/
def finiteLog (p : Poly) : Nat → Poly
  | 0 => []
  | n + 1 => padd (finiteLog p n)
      (pscale (Q'.invSucc n) (polynomialPower p (n + 1)))

private theorem inverse_cancel (n : Nat) :
    (Q'.invSucc n * Q'.ofNat (n + 1)).eqv 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.ofNat_succ_mul_invSucc n)

/-- Exact coefficientwise derivative of the ACTUAL finite truncated series. -/
theorem finiteLog_derivative (p : Poly) (n : Nat) :
    CoeffEqv (pderiv (finiteLog p n))
      (pmul (pderiv p) (geometricPolynomial p n)) := by
  induction n with
  | zero => exact (coeffEqv_pmul_comm (pderiv p) []).symm
  | succ n ih =>
      have hterm :
          CoeffEqv
            (pderiv (pscale (Q'.invSucc n) (polynomialPower p (n + 1))))
            (pmul (pderiv p) (polynomialPower p n)) :=
        (pderiv_pscale _ _).trans
          (((power_derivative_succ p n).pscale (Q'.invSucc n)).trans
            ((coeffEqv_pscale_comp _ _ _).trans
              ((coeffEqv_pscale_scalar (inverse_cancel n) _).trans
                (coeffEqv_pscale_one _))))
      exact (pderiv_padd _ _).trans
        ((CoeffEqv.padd ih hterm).trans
          (coeffEqv_pmul_padd_right (pderiv p)
            (geometricPolynomial p n) (polynomialPower p n)).symm)

/-- Evaluation is precisely the original finite rational sum, with its
inclusive positive power and reciprocal-successor coefficients. -/
theorem finiteLog_eval (p : Poly) (n : Nat) (h : Q') :
    (eval (finiteLog p n) h).eqv
      (finSum (fun k => Q'.invSucc k * (eval p h) ^ (k + 1)) n) := by
  induction n with
  | zero => exact Q'.eqv_refl 0
  | succ n ih =>
      exact Q'.eqv_trans _ _ _ (eval_padd _ _ h)
        (q_add_congr ih
          (Q'.eqv_trans _ _ _ (eval_pscale _ _ h)
            (Q'.mul_eqv_congr_left (Q'.invSucc n) _ _
              (polynomialPower_eval p (n + 1) h))))

end YMGap.Constructive.QPolyFiniteLogDerivative

#print axioms YMGap.Constructive.QPolyFiniteLogDerivative.finiteLog
#print axioms YMGap.Constructive.QPolyFiniteLogDerivative.finiteLog_derivative
#print axioms YMGap.Constructive.QPolyFiniteLogDerivative.finiteLog_eval
