/-
# Finite geometric sums in the actual rational polynomial carrier

The coefficient-level telescope is valid even at exponent zero, and uses
neither an inverse nor a scalar evaluation identity in place of coefficient
equality. The evaluation pin uses the constructive left-fold `Q'.pow`.
These are finite algebra producers; no positivity or operator lift is claimed.
-/

import YMGap.Constructive.QPolyPositivePrimitive
import YMGap.Constructive.Geometric

namespace YMGap.Constructive.QPolyFiniteGeometric

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower)

/-- The literal sum of powers with exponents strictly below n. -/
def geometricPolynomial (p : Poly) : Nat → Poly
  | 0 => []
  | n + 1 => padd (geometricPolynomial p n) (polynomialPower p n)

private theorem complement_product (p q : Poly) :
    CoeffEqv (pmul (psub [1] p) q) (psub q (pmul p q)) :=
  (coeffEqv_padd_pmul_left [1] (pneg p) q).trans
    (CoeffEqv.padd (coeffEqv_pmul_one_left q)
      (coeffEqv_pscale_pmul (-1) p q))

/-- Exact finite geometric telescoping at every padded coefficient. No
nonzero-denominator or interval premise is needed, including n=0. -/
theorem geometric_telescope (p : Poly) (n : Nat) :
    CoeffEqv (pmul (psub [1] p) (geometricPolynomial p n))
      (psub [1] (polynomialPower p n)) := by
  induction n with
  | zero =>
      exact (coeffEqv_pmul_comm (psub [1] p) []).trans
        (coeffEqv_padd_pneg_self [1]).symm
  | succ n ih =>
      exact (coeffEqv_pmul_padd_right (psub [1] p)
        (geometricPolynomial p n) (polynomialPower p n)).trans
        ((CoeffEqv.padd ih (complement_product p (polynomialPower p n))).trans
          (coeffEqv_padd_pneg_cancel [1] (polynomialPower p n)
            (pneg (pmul p (polynomialPower p n)))))

/-- Evaluation of the ACTUAL polynomial power, with the original constructive
rational power convention (left multiplication at each successor). -/
theorem polynomialPower_eval (p : Poly) (n : Nat) (h : Q') :
    (eval (polynomialPower p n) h).eqv ((eval p h)^n) := by
  induction n with
  | zero =>
      change (1 + h*0).eqv 1
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 1 _ 0 (q_mul_zero h)) (q_add_zero_eqv 1)
  | succ n ih =>
      exact Q'.eqv_trans _ _ _
        (eval_pmul p (polynomialPower p n) h)
        (Q'.mul_eqv_congr_left (eval p h) _ _ ih)

#print axioms geometricPolynomial
#print axioms geometric_telescope
#print axioms polynomialPower_eval

end YMGap.Constructive.QPolyFiniteGeometric
