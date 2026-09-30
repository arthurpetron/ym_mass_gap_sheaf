/-
# Explicit fixed-depth mass modulus for nested complement roots

Every nested approximant still has nonnegative coefficients and mass at
most one. Its mass deficit tends to zero with a depth-indexed rational
modulus. The square-error certificate supplies the induction step; no
scalar or operator root is selected. This controls convergence, not a
physical spectral gap, and the modulus is not asserted to be efficient.
-/

import YMGap.Continuum.ComplementRootComposition
import YMGap.Continuum.ComplementRootError
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.ComplementRootNestedMass

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
open YMGap.Constructive.CRealArtanhEulerPositiveCompanion
open YMGap.Continuum.ComplementRootPolynomial
open YMGap.Continuum.ComplementRootComposition
open YMGap.Continuum.ComplementRootError
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra (eval_compose)

local infix:50 " ≈ " => Q'.eqv

theorem eval_nonnegative (p : Poly) (hp : CoeffNonnegative p)
    (t : Q') (ht : (0 : Q') ≤ t) : (0 : Q') ≤ eval p t := by
  induction p with
  | nil => exact Q'.le_refl' 0
  | cons a p ih =>
      exact Q'.zero_le_add _ _ (hp 0)
        (Q'.mul_nonneg _ _ ht (ih (fun i => hp (i+1))))

theorem eval_monotone (p : Poly) (hp : CoeffNonnegative p)
    {s t : Q'} (hs : (0 : Q') ≤ s) (hst : s ≤ t) :
    eval p s ≤ eval p t := by
  induction p with
  | nil => exact Q'.le_refl' 0
  | cons a p ih =>
      have hp' : CoeffNonnegative p := fun i => hp (i+1)
      exact Q'.add_le_add_left a _ _ (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hst (eval_nonnegative p hp' s hs))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (ih hp') (Q'.le_trans' _ _ _ hs hst)))

theorem eval_polynomial_le_one (n : Nat) (t : Q')
    (ht : (0 : Q') ≤ t) (ht1 : t ≤ (1 : Q')) :
    eval (polynomial n) t ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (eval_monotone _ (polynomial_coeffNonnegative n) ht ht1)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_polynomial_one n))
      (ComplementRootMass.mass_le_one n))

def mass (k n : Nat) : Q' := eval (nested k n) 1
def residual (k n : Nat) : Q' := 1-mass k n

theorem mass_nonnegative (k n : Nat) : (0 : Q') ≤ mass k n :=
  eval_nonnegative _ (nested_coeffNonnegative k n) 1 Q'.zero_le_one

theorem mass_le_one : ∀ k n : Nat, mass k n ≤ (1 : Q')
  | 0, n => Q'.le_of_eqv (eval_pvar 1)
  | k+1, n =>
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_compose (nested k n) 1 (polynomial n)))
        (eval_polynomial_le_one n (mass k n) (mass_nonnegative k n) (mass_le_one k n))

theorem residual_nonnegative (k n : Nat) : (0 : Q') ≤ residual k n :=
  Q'.sub_nonneg_of_le (mass_le_one k n)

theorem residual_le_one (k n : Nat) : residual k n ≤ (1 : Q') := by
  have h := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (mass_nonnegative k n))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (q_add_zero_eqv 1))

private theorem square_congr {a b : Q'} (h : a ≈ b) : a*a ≈ b*b :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ h)

/-- Exact scalar error at each nested depth, before any estimate. -/
theorem residual_square_error (k n : Nat) :
    residual (k+1) n * residual (k+1) n - residual k n ≈
      eval (errorPolynomial n) (mass k n) := by
  have h : residual (k+1) n ≈ 1-eval (polynomial n) (mass k n) :=
    q_add_congr (Q'.eqv_refl 1)
      (Q'.neg_eqv_congr _ _ (eval_compose (nested k n) 1 (polynomial n)))
  exact Q'.eqv_trans _ _ _ (q_add_congr (square_congr h) (Q'.eqv_refl _))
    (Q'.eqv_symm (eval_error n (mass k n)))

/-- The depth step costs only the already controlled scalar root error. -/
theorem residual_square_le (k n : Nat) :
    residual (k+1) n * residual (k+1) n ≤
      residual k n + ComplementRootMass.residual n * ComplementRootMass.residual n := by
  apply CReal.le_add_of_sub_le
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (residual_square_error k n))
    (Q'.le_trans' _ _ _
      (eval_monotone _ (error_coeffNonnegative n) (mass_nonnegative k n) (mass_le_one k n))
      (Q'.le_of_eqv (error_mass n)))

/-- Computable at every fixed depth; no uniform-in-depth claim. -/
def residualModulus : Nat → Q' → Nat
  | 0, _ => 0
  | k+1, epsilon =>
      max (residualModulus k (HalfPow.half*(epsilon*epsilon)))
        (ComplementRootMass.tailModulus (HalfPow.half*(epsilon*epsilon)))

theorem residual_small : ∀ k (epsilon : Q'), (0 : Q') < epsilon →
    ∀ n, residualModulus k epsilon ≤ n → residual k n ≤ epsilon
  | 0, epsilon, he, n, _ => by
      have hz : residual 0 n ≈ (0 : Q') :=
        Q'.eqv_trans _ _ _
          (q_add_congr (Q'.eqv_refl 1) (Q'.neg_eqv_congr _ _ (eval_pvar 1)))
          (Q'.add_neg_self_eqv 1)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hz) (Q'.le_of_lt he)
  | k+1, epsilon, he, n, hn => by
      let delta := HalfPow.half*(epsilon*epsilon)
      have hd : (0 : Q') < delta :=
        ExpNeg.half_mul_pos _ (Q'.mul_pos he he)
      have hk : residual k n ≤ delta := residual_small k delta hd n
        (Nat.le_trans (Nat.le_max_left _ _) hn)
      have hr : ComplementRootMass.residual n ≤ delta :=
        ComplementRootMass.residual_small hd (Nat.le_trans (Nat.le_max_right _ _) hn)
      have hrr : ComplementRootMass.residual n * ComplementRootMass.residual n ≤ delta :=
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (ComplementRootMass.residual_le_one n)
            (ComplementRootMass.residual_nonnegative n))
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hr)
      apply CReal.le_of_sq_le_sq he (residual_nonnegative (k+1) n)
      exact Q'.le_trans' _ _ _ (residual_square_le k n)
        (Q'.le_trans' _ _ _ (Q'.add_le_add hk hrr)
          (Q'.le_of_eqv (ExpNeg.two_halves (epsilon*epsilon))))

#print axioms eval_nonnegative
#print axioms eval_monotone
#print axioms mass_nonnegative
#print axioms mass_le_one
#print axioms residual_square_error
#print axioms residual_square_le
#print axioms residualModulus
#print axioms residual_small

end YMGap.Continuum.ComplementRootNestedMass
