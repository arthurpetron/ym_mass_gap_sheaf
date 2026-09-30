/-
# Finite polynomial approximants for the scalar complement root

This module packages the scalar recursion
`p₀ = 0`, `pₙ₊₁ = (pvar + pₙ²)/2` as coefficient lists in `QPoly`.
It proves coefficient nonnegativity, coefficientwise monotonicity, and the
exact evaluation pin to `ComplementRootMass.mass`.  These are scalar
polynomial facts only: no operator square root or time evolution is asserted.
-/

import YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound
import YMGap.Constructive.HalfPow
import YMGap.Constructive.CRealMulMono
import YMGap.Continuum.ComplementRootMass

namespace YMGap.Continuum.ComplementRootPolynomial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
open YMGap.Constructive.CRealArtanhEulerPositiveCompanion
open YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound
open YMGap.Constructive.HalfPow
open YMGap.Continuum.ComplementRootMass

/-- The finite polynomial approximants to the complementary square root. -/
def polynomial : Nat → Poly
  | 0 => []
  | n + 1 =>
      pscale HalfPow.half
        (padd pvar (pmul (polynomial n) (polynomial n)))

/-- The variable polynomial has nonnegative coefficients. -/
theorem pvar_coeffNonnegative : CoeffNonnegative pvar := by
  intro index
  cases index with
  | zero => exact Q'.le_refl' 0
  | succ index =>
      cases index with
      | zero => exact Q'.zero_le_one
      | succ index => exact Q'.le_refl' 0

/-- Every approximant has nonnegative coefficients. -/
theorem polynomial_coeffNonnegative :
    ∀ n, CoeffNonnegative (polynomial n)
  | 0 => coeffNonnegative_empty
  | n + 1 => by
      exact coeffNonnegative_pscale HalfPow.half_nonneg
        (coeffNonnegative_padd pvar_coeffNonnegative
          (coeffNonnegative_pmul
            (polynomial_coeffNonnegative n)
            (polynomial_coeffNonnegative n)))

/-- Adjacent approximants are ordered coefficient by coefficient. -/
theorem polynomial_coeffLe_succ :
    ∀ n, CoeffLe (polynomial n) (polynomial (n + 1))
  | 0 => by
      intro index
      exact polynomial_coeffNonnegative 1 index
  | n + 1 => by
      have hsq :
          CoeffLe (pmul (polynomial n) (polynomial n))
            (pmul (polynomial (n + 1)) (polynomial (n + 1))) :=
        coeffLe_pmul (polynomial_coeffLe_succ n)
          (polynomial_coeffLe_succ n)
          (polynomial_coeffNonnegative n)
          (polynomial_coeffNonnegative (n + 1))
      have hadd :
          CoeffLe
            (padd pvar
              (pmul (polynomial n) (polynomial n)))
            (padd pvar
              (pmul (polynomial (n + 1)) (polynomial (n + 1)))) :=
        coeffLe_padd (coeffLe_refl pvar) hsq
      exact coeffLe_pscale HalfPow.half HalfPow.half_nonneg hadd

/-- Monotonicity for any two ordered recursion depths. -/
theorem polynomial_coeffLe {m n : Nat} (hmn : m ≤ n) :
    CoeffLe (polynomial m) (polynomial n) := by
  induction n generalizing m with
  | zero =>
      have : m = 0 := by omega
      subst m
      exact coeffLe_refl _
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · exact coeffLe_trans (ih hmn') (polynomial_coeffLe_succ n)
      · have hm : m = n + 1 := by omega
        subst m
        exact coeffLe_refl _

/-- The coefficientwise difference between ordered approximants is
nonnegative.  This is the scalar positive-remainder certificate. -/
theorem ordered_difference_nonnegative {m n : Nat} (hmn : m ≤ n) :
    CoeffNonnegative (psub (polynomial n) (polynomial m)) := by
  intro index
  have hcoeff := polynomial_coeffLe hmn index
  have hneg :
      ((-1 : Q') * coeff (polynomial m) index).eqv
        (-(coeff (polynomial m) index)) := by
    exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))
  have hsub :
      (coeff (psub (polynomial n) (polynomial m)) index).eqv
        (coeff (polynomial n) index - coeff (polynomial m) index) := by
    exact Q'.eqv_trans _ _ _ (coeff_psub _ _ _)
      (Q'.add_eqv_congr_left _ _ _ hneg)
  exact Q'.le_trans' _
      (coeff (polynomial n) index - coeff (polynomial m) index) _
      (Q'.sub_nonneg_of_le hcoeff)
      (Q'.ge_of_eqv hsub)

/-- Evaluation at one follows the companion scalar mass recursion exactly. -/
theorem eval_polynomial_one :
    ∀ n, (eval (polynomial n) 1).eqv (ComplementRootMass.mass n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      have ih := eval_polynomial_one n
      have hmul :
          (eval (pmul (polynomial n) (polynomial n)) 1).eqv
            (ComplementRootMass.mass n * ComplementRootMass.mass n) := by
        apply Q'.eqv_trans _ _ _
          (eval_pmul (polynomial n) (polynomial n) 1)
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (eval (polynomial n) 1)
            (ComplementRootMass.mass n) (eval (polynomial n) 1) ih)
          (Q'.mul_eqv_congr_left (ComplementRootMass.mass n)
            (eval (polynomial n) 1) (ComplementRootMass.mass n) ih)
      have hadd :
          (eval (padd pvar
            (pmul (polynomial n) (polynomial n))) 1).eqv
            (1 + ComplementRootMass.mass n * ComplementRootMass.mass n) := by
        exact Q'.eqv_trans _ _ _
          (eval_padd pvar
            (pmul (polynomial n) (polynomial n)) 1)
          (q_add_congr (eval_pvar 1) hmul)
      exact Q'.eqv_trans _ _ _
        (eval_pscale HalfPow.half
          (padd pvar (pmul (polynomial n) (polynomial n))) 1)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left HalfPow.half _ _ hadd)
          (Q'.eqv_refl _))

/-- The positive difference polynomial has the corresponding scalar mass
difference at one. -/
theorem eval_difference_one (m n : Nat) :
    (eval (psub (polynomial n) (polynomial m)) 1).eqv
      (ComplementRootMass.mass n - ComplementRootMass.mass m) := by
  exact Q'.eqv_trans _ _ _
    (eval_psub (polynomial n) (polynomial m) 1)
    (q_add_congr (eval_polynomial_one n)
      (Q'.neg_eqv_congr _ _ (eval_polynomial_one m)))

#print axioms polynomial_coeffNonnegative
#print axioms polynomial_coeffLe_succ
#print axioms polynomial_coeffLe
#print axioms ordered_difference_nonnegative
#print axioms eval_polynomial_one
#print axioms eval_difference_one

end YMGap.Continuum.ComplementRootPolynomial
