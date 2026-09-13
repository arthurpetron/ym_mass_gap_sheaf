/-
# Exact Euler normalization of the recursive Gaussian binomial

`GaussQBinom.qbin` is defined by q-Pascal, not by a quotient. This module
proves its denominator-cleared Euler product formula for every finite index:

    qbin Q N k * E Q k * E Q (N-k) ≈ E Q N,   k ≤ N,
    E Q n = product_{j=1..n} (1-Q^j).

The proof is algebraic and permits every rational Q, including Q=1: no
division, positivity assumption, or cancellation of a possibly zero factor
is used. This identifies the exact normalization needed in a finite
symmetric Jacobi identity; it does NOT prove that identity or its limit.
In particular, it does not identify a bare finite theta series with a finite
theta product, establish `DiffJTP`, or prove heat/action positivity.
-/

import YMGap.Continuum.GaussQBinom

namespace YMGap.Continuum.GaussQBinomEulerNormalization

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.GaussQBinom

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

private theorem add_num (a b : Q') :
    (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl

private theorem mul_num (a b : Q') : (a * b).num = a.num * b.num := rfl

-- Only polynomial rearrangement, with rational powers kept as opaque atoms.
local macro "mul_add_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [add_num, Q'.add_den_cast, mul_num,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Finite Euler product at an arbitrary rational base. -/
def euler (Q : Q') : Nat → Q'
  | 0 => 1
  | n + 1 => euler Q n * (1 + -(Q ^ (n + 1)))

@[simp] theorem euler_zero (Q : Q') : euler Q 0 = 1 := rfl

@[simp] theorem euler_succ (Q : Q') (n : Nat) :
    euler Q (n + 1) = euler Q n * (1 + -(Q ^ (n + 1))) := rfl

/-- The diagonal q-Pascal coefficient is exactly one, up to rational setoid
equality; the out-of-range term is not silently omitted. -/
theorem qbin_diagonal (Q : Q') (N : Nat) : qbin Q N N ≈ 1 := by
  induction N with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      rw [qbin_succ_succ, Nat.sub_self, Q'.pow_zero]
      calc qbin Q N (N + 1) + 1 * qbin Q N N
          ≈ 0 + 1 * 1 := Cheb.add_eqv_congr _ _ _ _
            (qbin_out_of_range Q N (N + 1) (by omega))
            (Q'.mul_eqv_congr_left _ _ _ ih)
        _ ≈ (1 : Q') := by rw [Q'.zero_add']; exact Q'.one_mul_eqv _

private theorem one_sub_combine (a b : Q') :
    (1 + -a) + a * (1 + -b) ≈ 1 + -(a * b) := by
  calc (1 + -a) + a * (1 + -b)
      ≈ (1 + -a) + (a + -(a * b)) :=
        Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
            (Cheb.add_eqv_congr _ _ _ _ (Q'.mul_one_eqv _) (Q'.mul_neg_eqv _ _)))
    _ ≈ ((1 + -a) + a) + -(a * b) := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ (1 + (-a + a)) + -(a * b) :=
      Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv _ _ _)
    _ ≈ (1 + 0) + -(a * b) := Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv _))
    _ ≈ 1 + -(a * b) := by rw [Q'.add_zero']; exact Q'.eqv_refl _

/-- q-Pascal's two complementary Euler factors combine without division. -/
theorem euler_pascal_factor (Q : Q') (N k : Nat) (hk : k ≤ N) :
    (1 + -(Q ^ (N - k))) + Q ^ (N - k) * (1 + -(Q ^ (k + 1)))
      ≈ 1 + -(Q ^ (N + 1)) := by
  calc (1 + -(Q ^ (N - k))) + Q ^ (N - k) * (1 + -(Q ^ (k + 1)))
      ≈ 1 + -(Q ^ (N - k) * Q ^ (k + 1)) := one_sub_combine _ _
    _ ≈ 1 + -(Q ^ ((N - k) + (k + 1))) :=
      Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (pow_add_eqv Q _ _))
    _ ≈ 1 + -(Q ^ (N + 1)) := by
      rw [show N - k + (k + 1) = N + 1 by omega]
      exact Q'.eqv_refl _

/-- Denominator-cleared q-factorial formula for the ORIGINAL recursive
Gaussian binomial. Valid at every rational base, even where Euler factors
vanish. -/
theorem qbin_mul_euler (Q : Q') (N k : Nat) (hk : k ≤ N) :
    qbin Q N k * euler Q k * euler Q (N - k) ≈ euler Q N := by
  induction N generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      exact Q'.eqv_refl _
  | succ N ih =>
      cases k with
      | zero =>
          simp only [qbin_succ_zero, euler_zero, Nat.sub_zero]
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)) (Q'.one_mul_eqv _)
      | succ k =>
          by_cases hdiag : k = N
          · subst k
            rw [Nat.sub_self, euler_zero]
            exact Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (Q'.mul_eqv_congr_right _ _ _ (qbin_diagonal Q (N + 1))))
              (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.one_mul_eqv _))
          · have hkN : k + 1 ≤ N := by omega
            have hm : N - k = (N - (k + 1)) + 1 := by omega
            have hEm : euler Q (N - k) =
                euler Q (N - (k + 1)) * (1 + -(Q ^ (N - k))) := by
              calc euler Q (N - k)
                  = euler Q ((N - (k + 1)) + 1) := by rw [hm]
                _ = euler Q (N - (k + 1)) * (1 + -(Q ^ (N - k))) := by
                  rw [euler_succ, ← hm]
            rw [Nat.succ_sub_succ_eq_sub, qbin_succ_succ]
            calc (qbin Q N (k + 1) + Q ^ (N - k) * qbin Q N k)
                    * euler Q (k + 1) * euler Q (N - k)
                ≈ qbin Q N (k + 1) * euler Q (k + 1) * euler Q (N - k)
                    + (Q ^ (N - k) * qbin Q N k) * euler Q (k + 1) * euler Q (N - k) := by
                      mul_add_ring
              _ ≈ (qbin Q N (k + 1) * euler Q (k + 1) * euler Q (N - (k + 1)))
                      * (1 + -(Q ^ (N - k)))
                    + (qbin Q N k * euler Q k * euler Q (N - k))
                      * (Q ^ (N - k) * (1 + -(Q ^ (k + 1)))) := by
                      apply Cheb.add_eqv_congr
                      · rw [hEm]; mul_add_ring
                      · rw [euler_succ Q k]; mul_add_ring
              _ ≈ euler Q N * (1 + -(Q ^ (N - k)))
                    + euler Q N * (Q ^ (N - k) * (1 + -(Q ^ (k + 1)))) :=
                      Cheb.add_eqv_congr _ _ _ _
                        (Q'.mul_eqv_congr_right _ _ _ (ih (k + 1) hkN))
                        (Q'.mul_eqv_congr_right _ _ _ (ih k (by omega)))
              _ ≈ euler Q N *
                    ((1 + -(Q ^ (N - k))) + Q ^ (N - k) * (1 + -(Q ^ (k + 1)))) :=
                      Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
              _ ≈ euler Q N * (1 + -(Q ^ (N + 1))) :=
                Q'.mul_eqv_congr_left _ _ _ (euler_pascal_factor Q N k (by omega))
              _ ≈ euler Q (N + 1) := Q'.eqv_refl _

/-- Centered finite-Jacobi indices, with both denominator indices explicit.
This is the normalized coefficient formula, not a finite Jacobi identity. -/
theorem centered_qbin_mul_euler (Q : Q') (N j : Nat) (hj : j ≤ N) :
    qbin Q (N + N) (N + j) * euler Q (N + j) * euler Q (N - j)
      ≈ euler Q (N + N) := by
  have h := qbin_mul_euler Q (N + N) (N + j) (by omega)
  rw [show N + N - (N + j) = N - j by omega] at h
  exact h

end YMGap.Continuum.GaussQBinomEulerNormalization

#print axioms YMGap.Continuum.GaussQBinomEulerNormalization.euler
#print axioms YMGap.Continuum.GaussQBinomEulerNormalization.qbin_diagonal
#print axioms YMGap.Continuum.GaussQBinomEulerNormalization.euler_pascal_factor
#print axioms YMGap.Continuum.GaussQBinomEulerNormalization.qbin_mul_euler
#print axioms YMGap.Continuum.GaussQBinomEulerNormalization.centered_qbin_mul_euler
