/-
# Finite symmetric Chebyshev multiplication with exact boundary terms

For S_N = a_0 + 2 sum_{j=1..N} a_j T_j(x), multiplying by B+2cx
acts on coefficients by the three-neighbor rule

    b_0 = B a_0 + 2c a_1,
    b_{j+1} = c a_j + B a_{j+1} + c a_{j+2}.

The finite identity below retains both endpoint terms before imposing
finite support. It is algebra at arbitrary rational x, not a convergence
or differentiation assumption. In the Jacobi application B=1+c*c.
-/

import YMGap.Continuum.ChebyshevBound
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.FiniteSymmetricChebyshev

open YMGap.Constructive
open YMGap.Constructive.Q'

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_add_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.add_num, Q'.add_den_cast, Cheb.mul_num,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Symmetric real Laurent polynomial written in the original Chebyshev T
basis; no complex numbers or inverse variables are introduced. -/
def sum (a : Nat → Q') (x : Q') : Nat → Q'
  | 0 => a 0
  | N + 1 => sum a x N + (2 : Q') * a (N + 1) * Cheb.T (N + 1) x

/-- The exact coefficient update for multiplication by B+2cx. -/
def step (B c : Q') (a : Nat → Q') : Nat → Q'
  | 0 => B * a 0 + (2 : Q') * c * a 1
  | j + 1 => c * a j + B * a (j + 1) + c * a (j + 2)

/-- Equality on the finite range suffices; no infinite family assumption. -/
theorem sum_congr (a b : Nat → Q') (x : Q') (N : Nat)
    (h : ∀ j, j ≤ N → a j ≈ b j) : sum a x N ≈ sum b x N := by
  induction N with
  | zero => exact h 0 (by omega)
  | succ N ih =>
      exact Cheb.add_eqv_congr _ _ _ _ (ih (fun j hj => h j (by omega)))
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (h (N + 1) (by omega))))

/-- The T recurrence with its subtraction cancelled constructively. -/
theorem T_neighbors (N : Nat) (x : Q') :
    Cheb.T (N + 2) x + Cheb.T N x ≈ ((2 : Q') * x) * Cheb.T (N + 1) x := by
  rw [Cheb.T_succ_succ]
  calc (((2 : Q') * x) * Cheb.T (N + 1) x + -Cheb.T N x) + Cheb.T N x
      ≈ ((2 : Q') * x) * Cheb.T (N + 1) x + (-Cheb.T N x + Cheb.T N x) :=
        Q'.add_assoc_eqv _ _ _
    _ ≈ ((2 : Q') * x) * Cheb.T (N + 1) x + 0 :=
      Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv _)
    _ ≈ ((2 : Q') * x) * Cheb.T (N + 1) x := by rw [Q'.add_zero']; exact Q'.eqv_refl _

/-- Exact finite multiplication identity BEFORE discarding endpoints.
The only omitted coefficients are a_(N+1) and a_(N+2), displayed explicitly. -/
theorem sum_step_with_boundary (B c : Q') (a : Nat → Q') (x : Q') (N : Nat) :
    sum (step B c a) x (N + 1)
      ≈ (B + (2 : Q') * c * x) * sum a x N
        + (2 : Q') * c * a (N + 1) * Cheb.T N x
        + (2 : Q') * (B * a (N + 1) + c * a (N + 2)) * Cheb.T (N + 1) x := by
  induction N with
  | zero =>
      change ((B * a 0 + (2 : Q') * c * a 1)
        + (2 : Q') * (c * a 0 + B * a 1 + c * a 2) * x) ≈
        ((B + (2 : Q') * c * x) * a 0 + (2 : Q') * c * a 1 * 1)
          + (2 : Q') * (B * a 1 + c * a 2) * x
      mul_add_ring
  | succ N ih =>
      change (sum (step B c a) x (N + 1)
        + (2 : Q') * (c * a (N + 1) + B * a (N + 2) + c * a (N + 3)) * Cheb.T (N + 2) x) ≈ _
      calc sum (step B c a) x (N + 1)
              + (2 : Q') * (c * a (N + 1) + B * a (N + 2) + c * a (N + 3)) * Cheb.T (N + 2) x
          ≈ ((B + (2 : Q') * c * x) * sum a x N
              + (2 : Q') * c * a (N + 1) * Cheb.T N x
              + (2 : Q') * (B * a (N + 1) + c * a (N + 2)) * Cheb.T (N + 1) x)
              + (2 : Q') * (c * a (N + 1) + B * a (N + 2) + c * a (N + 3)) * Cheb.T (N + 2) x :=
                Q'.add_eqv_congr_right _ _ _ ih
        _ ≈ (((B + (2 : Q') * c * x) * sum a x N
              + (2 : Q') * B * a (N + 1) * Cheb.T (N + 1) x)
              + (2 : Q') * c * a (N + 1) * (Cheb.T (N + 2) x + Cheb.T N x))
              + (2 : Q') * c * a (N + 2) * Cheb.T (N + 1) x
              + (2 : Q') * (B * a (N + 2) + c * a (N + 3)) * Cheb.T (N + 2) x := by
                mul_add_ring
        _ ≈ (((B + (2 : Q') * c * x) * sum a x N
              + (2 : Q') * B * a (N + 1) * Cheb.T (N + 1) x)
              + (2 : Q') * c * a (N + 1) * (((2 : Q') * x) * Cheb.T (N + 1) x))
              + (2 : Q') * c * a (N + 2) * Cheb.T (N + 1) x
              + (2 : Q') * (B * a (N + 2) + c * a (N + 3)) * Cheb.T (N + 2) x :=
                Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _
                  (Q'.add_eqv_congr_left _ _ _
                    (Q'.mul_eqv_congr_left _ _ _ (T_neighbors N x))))
        _ ≈ (B + (2 : Q') * c * x) * sum a x (N + 1)
              + (2 : Q') * c * a (N + 2) * Cheb.T (N + 1) x
              + (2 : Q') * (B * a (N + 2) + c * a (N + 3)) * Cheb.T (N + 2) x := by
                rw [sum]; mul_add_ring

/-- Multiplication by B+2cx when the two finite endpoints vanish. -/
theorem sum_step (B c : Q') (a : Nat → Q') (x : Q') (N : Nat)
    (h₁ : a (N + 1) ≈ 0) (h₂ : a (N + 2) ≈ 0) :
    sum (step B c a) x (N + 1) ≈ (B + (2 : Q') * c * x) * sum a x N := by
  have htail₁ : (2 : Q') * c * a (N + 1) * Cheb.T N x ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h₁) (Q'.mul_zero_eqv _)))
      (Q'.zero_mul_eqv _)
  have htail₂ : (2 : Q') * (B * a (N + 1) + c * a (N + 2)) * Cheb.T (N + 1) x ≈ 0 := by
    have hz : B * a (N + 1) + c * a (N + 2) ≈ 0 :=
      Q'.eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h₁) (Q'.mul_zero_eqv _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h₂) (Q'.mul_zero_eqv _)))
        (by rw [Q'.add_zero']; exact Q'.eqv_refl _)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)))
      (Q'.zero_mul_eqv _)
  calc sum (step B c a) x (N + 1)
      ≈ (B + (2 : Q') * c * x) * sum a x N
        + (2 : Q') * c * a (N + 1) * Cheb.T N x
        + (2 : Q') * (B * a (N + 1) + c * a (N + 2)) * Cheb.T (N + 1) x :=
          sum_step_with_boundary B c a x N
    _ ≈ (B + (2 : Q') * c * x) * sum a x N + 0 + 0 :=
      Cheb.add_eqv_congr _ _ _ _ (Q'.add_eqv_congr_left _ _ _ htail₁) htail₂
    _ ≈ (B + (2 : Q') * c * x) * sum a x N := by
      rw [Q'.add_zero', Q'.add_zero']; exact Q'.eqv_refl _

end YMGap.Continuum.FiniteSymmetricChebyshev

#print axioms YMGap.Continuum.FiniteSymmetricChebyshev.sum
#print axioms YMGap.Continuum.FiniteSymmetricChebyshev.step
#print axioms YMGap.Continuum.FiniteSymmetricChebyshev.sum_congr
#print axioms YMGap.Continuum.FiniteSymmetricChebyshev.T_neighbors
#print axioms YMGap.Continuum.FiniteSymmetricChebyshev.sum_step_with_boundary
#print axioms YMGap.Continuum.FiniteSymmetricChebyshev.sum_step
