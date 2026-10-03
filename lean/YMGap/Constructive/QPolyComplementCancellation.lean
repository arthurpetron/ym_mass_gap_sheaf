/-
# Coefficient-level cancellation of the literal complement polynomial

Multiplication by `[1,-1]` preserves the constant coefficient and takes each
later coefficient to its difference with the preceding coefficient. Induction
therefore recovers the actual original coefficient row. No rational inverse,
evaluation-only equality, degree guard or interval premise is used.
-/

import YMGap.Constructive.QPolyPositivePrimitive

namespace YMGap.Constructive.QPolyComplementCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive (complement)

private theorem complement_coefficient_zero (p : Poly) :
    (coeff (pmul complement p) 0).eqv (coeff p 0) :=
  Q'.eqv_trans _ _ _ (coeff_pmul_pair_left_zero 1 (-1) p)
    (Q'.one_mul_eqv _)

private theorem complement_coefficient_succ (p : Poly) (n : Nat) :
    (coeff (pmul complement p) (n+1)).eqv
      (coeff p (n+1) + -(coeff p n)) :=
  Q'.eqv_trans _ _ _ (coeff_pmul_pair_left_succ 1 (-1) p n)
    (q_add_congr (Q'.one_mul_eqv _)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

private theorem difference_restore (a b : Q') :
    ((a + -b) + b).eqv a :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a _ 0 (Q'.neg_add_self_eqv b))
      (q_add_zero_eqv a))

/-- Multiplication by the ACTUAL `1-h` coefficient list is injective over
coefficientwise rational equality, including zero and padded coefficient rows.
This permits cancellation of a polynomial factor at the endpoints too. -/
theorem complement_mul_injective {p q : Poly}
    (h : CoeffEqv (pmul complement p) (pmul complement q)) : CoeffEqv p q := by
  intro n
  induction n with
  | zero =>
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (complement_coefficient_zero p))
        (Q'.eqv_trans _ _ _ (h 0) (complement_coefficient_zero q))
  | succ n ih =>
      have hd : (coeff p (n+1) + -(coeff p n)).eqv
          (coeff q (n+1) + -(coeff q n)) :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm (complement_coefficient_succ p n))
          (Q'.eqv_trans _ _ _ (h (n+1)) (complement_coefficient_succ q n))
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm (difference_restore (coeff p (n+1)) (coeff p n)))
        (Q'.eqv_trans _ _ _ (q_add_congr hd ih)
          (difference_restore (coeff q (n+1)) (coeff q n)))

#print axioms complement_mul_injective

end YMGap.Constructive.QPolyComplementCancellation
