/-
# Positive finite square errors for the complement-root iteration

The square error is twice the adjacent polynomial difference. Its
nonnegative coefficients therefore follow from the existing monotonicity,
without a new nonlinear error iteration. Its mass is exactly the already
controlled scalar residual squared. This is the finite certificate needed
when nesting the root approximation in the ORIGINAL transfer defect.
-/

import YMGap.Continuum.ComplementRootPolynomial

namespace YMGap.Continuum.ComplementRootError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
open YMGap.Constructive.CRealArtanhEulerPositiveCompanion
open YMGap.Continuum.ComplementRootPolynomial
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Exact finite square error, kept as a positive coefficient certificate. -/
def errorPolynomial (n : Nat) : Poly :=
  pscale 2 (psub (polynomial (n+1)) (polynomial n))

theorem error_coeffNonnegative (n : Nat) :
    CoeffNonnegative (errorPolynomial n) :=
  coeffNonnegative_pscale (by decide : (0 : Q') ≤ 2)
    (ordered_difference_nonnegative (Nat.le_succ n))

theorem eval_polynomial_succ (n : Nat) (t : Q') :
    eval (polynomial (n+1)) t ≈
      HalfPow.half * (t + eval (polynomial n) t * eval (polynomial n) t) := by
  exact Q'.eqv_trans _ _ _ (eval_pscale _ _ _)
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (eval_padd _ _ _)
        (q_add_congr (eval_pvar t) (eval_pmul _ _ _))))

private theorem double_half (s : Q') : 2*(HalfPow.half*s) ≈ s :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : 2*HalfPow.half ≈ (1 : Q')))
      (Q'.one_mul_eqv s))

private theorem scalar_square_error (t a : Q') :
    2*(HalfPow.half*(t+a*a)-a) ≈ (1-a)*(1-a)-(1-t) :=
  Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (q_add_congr (double_half _) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.var 1) (.var 1)))
          (.mul (.const 2) (.neg (.var 1))))
        (.add (.mul (.add (.const 1) (.neg (.var 1)))
          (.add (.const 1) (.neg (.var 1))))
          (.neg (.add (.const 1) (.neg (.var 0)))))
        (by decide) (fun | 0 => t | _ => a)))

/-- The positive polynomial is exactly the finite root-square defect. -/
theorem eval_error (n : Nat) (t : Q') :
    eval (errorPolynomial n) t ≈
      (1-eval (polynomial n) t)*(1-eval (polynomial n) t)-(1-t) := by
  exact Q'.eqv_trans _ _ _ (eval_pscale _ _ _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (eval_psub _ _ _)
          (q_add_congr (eval_polynomial_succ n t) (Q'.eqv_refl _))))
      (scalar_square_error t (eval (polynomial n) t)))

private theorem square_congr {a b : Q'} (h : a ≈ b) : a*a ≈ b*b :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ h)

/-- No hidden rate: the error mass is the explicit scalar residual squared. -/
theorem error_mass (n : Nat) :
    eval (errorPolynomial n) 1 ≈
      ComplementRootMass.residual n * ComplementRootMass.residual n := by
  have hp : 1-eval (polynomial n) 1 ≈ ComplementRootMass.residual n :=
    q_add_congr (Q'.eqv_refl 1)
      (Q'.neg_eqv_congr _ _ (eval_polynomial_one n))
  exact Q'.eqv_trans _ _ _ (eval_error n 1)
    (Q'.eqv_trans _ _ _
      (q_add_congr (square_congr hp) (by decide : -((1 : Q')-1) ≈ (0 : Q')))
      (q_add_zero_eqv _))

/-- Squared error-mass bound at a supplied positive scalar precision. -/
theorem error_mass_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : ComplementRootMass.tailModulus epsilon ≤ n) :
    eval (errorPolynomial n) 1 ≤ epsilon*epsilon := by
  have h := ComplementRootMass.residual_small he hn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (error_mass n))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h
        (ComplementRootMass.residual_nonnegative n))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h (Q'.le_of_lt he)))

#print axioms error_coeffNonnegative
#print axioms eval_polynomial_succ
#print axioms eval_error
#print axioms error_mass
#print axioms error_mass_small

end YMGap.Continuum.ComplementRootError
