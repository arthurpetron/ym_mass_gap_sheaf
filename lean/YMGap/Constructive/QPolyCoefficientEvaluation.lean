/-
Evaluation respects padded coefficient equivalence for finite rational
polynomials.  The proof uses only the Horner recursion and does not require
a degree bound or a normalization of rational representatives.
-/

import YMGap.Constructive.QPolyFormalDerivative

namespace YMGap.Constructive.QPolyCoefficientEvaluation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative

local infix:50 " ~q " => Q'.eqv

private theorem eval_zero_of_coeff : forall (p : Poly),
    CoeffEqv p [] -> forall h : Q', (eval p h).eqv 0
  | [], _, h => Q'.eqv_refl 0
  | a :: p, hc, h => by
      have ha : a.eqv 0 := hc 0
      have htail : CoeffEqv p [] := fun i => hc (i + 1)
      have hp : (eval p h).eqv 0 := eval_zero_of_coeff p htail h
      change (a + h * eval p h).eqv 0
      exact Q'.eqv_trans _ (a + h * 0) _
        (q_add_congr (Q'.eqv_refl a)
          (Q'.mul_eqv_congr_left h _ _ hp))
        (Q'.eqv_trans _ (a + 0) _
          (Q'.add_eqv_congr_left a (h * 0) 0 (QPoly.q_mul_zero h))
          (Q'.eqv_trans _ a _ (q_add_zero_eqv a) ha))

/-- Coefficientwise equality of the actual zero-padded coefficients implies
equivalent Horner evaluations at every rational argument. -/
theorem coefficient_eval : forall {p q : Poly}, CoeffEqv p q -> forall h : Q',
    (eval p h).eqv (eval q h)
  | [], [], _, h => Q'.eqv_refl 0
  | [], a :: q, hc, h => by
      have ha : (0 : Q').eqv a := hc 0
      have htail : CoeffEqv [] q := fun i => hc (i + 1)
      have hq : (eval q h).eqv 0 :=
        eval_zero_of_coeff q htail.symm h
      change (0 : Q').eqv (a + h * eval q h)
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.eqv_symm (q_zero_add_eqv (0 : Q')))
        (Q'.eqv_trans _ (a + 0) _
          (q_add_congr ha (Q'.eqv_refl 0))
          (Q'.add_eqv_congr_left a 0 (h * eval q h)
            (Q'.eqv_symm
              (Q'.eqv_trans _ (h * 0) _
                (Q'.mul_eqv_congr_left h _ _ hq)
                (QPoly.q_mul_zero h)))))
  | a :: p, [], hc, h => by
      exact eval_zero_of_coeff (a :: p) hc h
  | a :: p, b :: q, hc, h => by
      have hab : a.eqv b := hc 0
      have htail : CoeffEqv p q := fun i => hc (i + 1)
      have hrec := coefficient_eval htail h
      change (a + h * eval p h).eqv (b + h * eval q h)
      exact q_add_congr hab (Q'.mul_eqv_congr_left h _ _ hrec)

#print axioms coefficient_eval

end YMGap.Constructive.QPolyCoefficientEvaluation
