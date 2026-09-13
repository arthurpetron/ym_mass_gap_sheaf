/-
# Exact differentiated finite symmetric Chebyshev multiplication

The original Lcoef recurrence proves the derivative companion of the finite
three-neighbor coefficient rule. Both finite endpoint terms are retained
until their coefficients are proved zero. This is rational finite algebra at
every x, including endpoints, and does not differentiate an infinite limit.
-/

import YMGap.Continuum.FiniteSymmetricChebyshev
import YMGap.Continuum.ChebTFwdRatioClose

namespace YMGap.Continuum.FiniteSymmetricChebyshevDerivative

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.FiniteSymmetricChebyshev
open YMGap.Continuum.ChebTFwdRatioClose (Lcoef)

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

private theorem neg_num_cast (a : Q') : (-a).num = -a.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

/-- Formal derivative of the symmetric finite sum. The constant has derivative
zero; the existing Lcoef is exactly (j+1)*U_j at the nonconstant indices. -/
def dsum (a : Nat → Q') (x : Q') : Nat → Q'
  | 0 => 0
  | N + 1 => dsum a x N + (2 : Q') * a (N + 1) * Lcoef x (N + 1)

theorem dsum_congr (a b : Nat → Q') (x : Q') (N : Nat)
    (h : ∀ j, j ≤ N → a j ≈ b j) : dsum a x N ≈ dsum b x N := by
  induction N with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      exact Cheb.add_eqv_congr _ _ _ _ (ih (fun j hj => h j (by omega)))
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ (h (N + 1) (by omega))))

theorem dsum_scale (c : Q') (a : Nat → Q') (x : Q') (N : Nat) :
    dsum (fun j => c * a j) x N ≈ c * dsum a x N := by
  induction N with
  | zero => exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  | succ N ih =>
      calc dsum (fun j => c * a j) x (N + 1)
          ≈ c * dsum a x N + (2 : Q') * (c * a (N + 1)) * Lcoef x (N + 1) :=
            Q'.add_eqv_congr_right _ _ _ ih
        _ ≈ c * dsum a x (N + 1) := by rw [dsum]; ring_qeqv

/-- The derivative neighbor identity includes the derivative of 2*x. -/
theorem L_neighbors (N : Nat) (x : Q') :
    Lcoef x (N + 2) + Lcoef x N
      ≈ ((2 : Q') * x) * Lcoef x (N + 1) + (2 : Q') * Cheb.T (N + 1) x := by
  have htwo : ((1 : Q') + 1) ≈ (2 : Q') := by decide
  have hrec : Lcoef x (N + 2)
      ≈ (((2 : Q') * x) * Lcoef x (N + 1) + -Lcoef x N)
        + (2 : Q') * Cheb.T (N + 1) x :=
    Q'.eqv_trans _ _ _ (ChebTFwdRatioClose.Lcoef_rec x N)
      (Cheb.add_eqv_congr _ _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _ htwo)))
        (Q'.mul_eqv_congr_right _ _ _ htwo))
  calc Lcoef x (N + 2) + Lcoef x N
      ≈ ((((2 : Q') * x) * Lcoef x (N + 1) + -Lcoef x N)
        + (2 : Q') * Cheb.T (N + 1) x) + Lcoef x N := Q'.add_eqv_congr_right _ _ _ hrec
    _ ≈ (((2 : Q') * x) * Lcoef x (N + 1) + (-Lcoef x N + Lcoef x N))
        + (2 : Q') * Cheb.T (N + 1) x := by ring_qeqv
    _ ≈ (((2 : Q') * x) * Lcoef x (N + 1) + 0)
        + (2 : Q') * Cheb.T (N + 1) x :=
      Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv _))
    _ ≈ ((2 : Q') * x) * Lcoef x (N + 1) + (2 : Q') * Cheb.T (N + 1) x := by
      rw [Q'.add_zero']; exact Q'.eqv_refl _

/-- Exact finite Leibniz rule, BEFORE discarding the two endpoint terms. -/
theorem dsum_step_with_boundary (B c : Q') (a : Nat → Q') (x : Q') (N : Nat) :
    dsum (step B c a) x (N + 1)
      ≈ (B + (2 : Q') * c * x) * dsum a x N
        + (2 : Q') * c * sum a x N
        + (2 : Q') * c * a (N + 1) * Lcoef x N
        + (2 : Q') * (B * a (N + 1) + c * a (N + 2)) * Lcoef x (N + 1) := by
  induction N with
  | zero =>
      have hL : Lcoef x 1 ≈ (1 : Q') := by
        change ((1 : Q') * 1) ≈ (1 : Q'); decide
      have hleft : dsum (step B c a) x 1 ≈ (2 : Q') * (c * a 0 + B * a 1 + c * a 2) := by
        change (0 + (2 : Q') * (c * a 0 + B * a 1 + c * a 2) * Lcoef x 1) ≈ _
        rw [Q'.zero_add']
        exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hL) (Q'.mul_one_eqv _)
      have hright : (B + (2 : Q') * c * x) * dsum a x 0 + (2 : Q') * c * sum a x 0
          + (2 : Q') * c * a 1 * Lcoef x 0
          + (2 : Q') * (B * a 1 + c * a 2) * Lcoef x 1
          ≈ (2 : Q') * c * a 0 + (2 : Q') * (B * a 1 + c * a 2) := by
        apply Q'.eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
          (Cheb.add_eqv_congr _ _ _ _
            (Q'.add_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _)) (Q'.mul_zero_eqv _))
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hL) (Q'.mul_one_eqv _)))
        rw [Q'.zero_add', Q'.add_zero']; exact Q'.eqv_refl _
      exact Q'.eqv_trans _ _ _ hleft
        (Q'.eqv_trans _ _ _ (by ring_qeqv) (Q'.eqv_symm hright))
  | succ N ih =>
      calc dsum (step B c a) x (N + 1 + 1)
          ≈ ((B + (2 : Q') * c * x) * dsum a x N
              + (2 : Q') * c * sum a x N
              + (2 : Q') * c * a (N + 1) * Lcoef x N
              + (2 : Q') * (B * a (N + 1) + c * a (N + 2)) * Lcoef x (N + 1))
            + (2 : Q') * (c * a (N + 1) + B * a (N + 2) + c * a (N + 3)) * Lcoef x (N + 2) :=
              Q'.add_eqv_congr_right _ _ _ ih
        _ ≈ (((B + (2 : Q') * c * x) * dsum a x N
              + (2 : Q') * c * sum a x N
              + (2 : Q') * B * a (N + 1) * Lcoef x (N + 1))
              + (2 : Q') * c * a (N + 1) * (Lcoef x (N + 2) + Lcoef x N))
              + (2 : Q') * c * a (N + 2) * Lcoef x (N + 1)
              + (2 : Q') * (B * a (N + 2) + c * a (N + 3)) * Lcoef x (N + 2) := by
                ring_qeqv
        _ ≈ (((B + (2 : Q') * c * x) * dsum a x N
              + (2 : Q') * c * sum a x N
              + (2 : Q') * B * a (N + 1) * Lcoef x (N + 1))
              + (2 : Q') * c * a (N + 1)
                * (((2 : Q') * x) * Lcoef x (N + 1) + (2 : Q') * Cheb.T (N + 1) x))
              + (2 : Q') * c * a (N + 2) * Lcoef x (N + 1)
              + (2 : Q') * (B * a (N + 2) + c * a (N + 3)) * Lcoef x (N + 2) :=
                Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _
                  (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ (L_neighbors N x))))
        _ ≈ (B + (2 : Q') * c * x) * dsum a x (N + 1)
              + (2 : Q') * c * sum a x (N + 1)
              + (2 : Q') * c * a (N + 2) * Lcoef x (N + 1)
              + (2 : Q') * (B * a (N + 2) + c * a (N + 3)) * Lcoef x (N + 2) := by
                rw [dsum, sum]; ring_qeqv

/-- Exact finite Leibniz rule when the two endpoint coefficients vanish. -/
theorem dsum_step (B c : Q') (a : Nat → Q') (x : Q') (N : Nat)
    (h₁ : a (N + 1) ≈ 0) (h₂ : a (N + 2) ≈ 0) :
    dsum (step B c a) x (N + 1)
      ≈ (B + (2 : Q') * c * x) * dsum a x N + (2 : Q') * c * sum a x N := by
  have ht₁ : (2 : Q') * c * a (N + 1) * Lcoef x N ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h₁) (Q'.mul_zero_eqv _)))
      (Q'.zero_mul_eqv _)
  have hz : B * a (N + 1) + c * a (N + 2) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h₁) (Q'.mul_zero_eqv _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h₂) (Q'.mul_zero_eqv _)))
      (by decide)
  have ht₂ : (2 : Q') * (B * a (N + 1) + c * a (N + 2)) * Lcoef x (N + 1) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)))
      (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ _ _ (dsum_step_with_boundary B c a x N)
    (Q'.eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
      (Q'.add_eqv_congr_left _ _ _ ht₁) ht₂)
      (by rw [Q'.add_zero', Q'.add_zero']; exact Q'.eqv_refl _))

end YMGap.Continuum.FiniteSymmetricChebyshevDerivative

#print axioms YMGap.Continuum.FiniteSymmetricChebyshevDerivative.dsum
#print axioms YMGap.Continuum.FiniteSymmetricChebyshevDerivative.dsum_congr
#print axioms YMGap.Continuum.FiniteSymmetricChebyshevDerivative.dsum_scale
#print axioms YMGap.Continuum.FiniteSymmetricChebyshevDerivative.L_neighbors
#print axioms YMGap.Continuum.FiniteSymmetricChebyshevDerivative.dsum_step_with_boundary
#print axioms YMGap.Continuum.FiniteSymmetricChebyshevDerivative.dsum_step
