/-
# Positive-denominator Gaussian coefficients and the actual theta Euler factor

For `0<Q<1`, the denominator-cleared q-Pascal formula gives the exact
computable quotient and complementary-index symmetry of `GaussQBinom.qbin`.
The base change `Q=a*a` is pinned to `RealTheta.eulerProd`, not to a new
surrogate product. The centered coefficient includes its finite Euler
normalization explicitly.

These are finite identities and finite strict positivity statements.
No lower bound uniform in Q or truncation is asserted. The symmetric finite
Jacobi identity, quantitative convergence of its coefficients, differentiated
JTP, and original-action positive floor remain open here.
-/

import YMGap.Continuum.GaussQBinomEulerNormalization
import YMGap.Continuum.RealTheta
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.GaussQBinomEulerQuotient

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.GaussQBinom
open YMGap.Continuum.GaussQBinomEulerNormalization

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (h' : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ h')

/-- Every finite Euler denominator is strictly positive. This is NOT a
uniform-in-cutoff or uniform-in-base lower floor. -/
theorem euler_pos {Q : Q'} (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (N : Nat) : (0 : Q') < euler Q N := by
  induction N with
  | zero => exact (by decide : (0 : Q') < (1 : Q'))
  | succ N ih =>
      exact HKPos.q_mul_pos ih
        (HKPos.one_sub_pos (HKPos.pow_succ_pos_lt_one hQ0 hQ1 N).2)

/-- Exact rational quotient, with its two Euler denominators exposed. -/
theorem qbin_eq_euler_quotient {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (N k : Nat) (hk : k ≤ N) :
    qbin Q N k ≈ HKConv.divPos (euler Q N) (euler Q k * euler Q (N - k)) := by
  have hD := HKPos.q_mul_pos (euler_pos hQ0 hQ1 k) (euler_pos hQ0 hQ1 (N - k))
  apply Q'.mul_left_cancel_of_pos hD
  calc (euler Q k * euler Q (N - k)) * qbin Q N k
      ≈ qbin Q N k * (euler Q k * euler Q (N - k)) := Q'.mul_comm_eqv _ _
    _ ≈ qbin Q N k * euler Q k * euler Q (N - k) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    _ ≈ euler Q N := qbin_mul_euler Q N k hk
    _ ≈ HKConv.divPos (euler Q N) (euler Q k * euler Q (N - k))
          * (euler Q k * euler Q (N - k)) :=
      Q'.eqv_symm (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hD))
    _ ≈ (euler Q k * euler Q (N - k))
          * HKConv.divPos (euler Q N) (euler Q k * euler Q (N - k)) :=
      Q'.mul_comm_eqv _ _

/-- Complementary-index symmetry of the original recursive coefficients.
Positive denominators justify the cancellation explicitly. -/
theorem qbin_complement {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (N k : Nat) (hk : k ≤ N) : qbin Q N k ≈ qbin Q N (N - k) := by
  have hD := HKPos.q_mul_pos (euler_pos hQ0 hQ1 k) (euler_pos hQ0 hQ1 (N - k))
  have hright := qbin_mul_euler Q N (N - k) (by omega)
  rw [show N - (N - k) = k by omega] at hright
  apply Q'.mul_left_cancel_of_pos hD
  calc (euler Q k * euler Q (N - k)) * qbin Q N k
      ≈ qbin Q N k * euler Q k * euler Q (N - k) :=
        Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    _ ≈ euler Q N := qbin_mul_euler Q N k hk
    _ ≈ qbin Q N (N - k) * euler Q (N - k) * euler Q k := Q'.eqv_symm hright
    _ ≈ (euler Q k * euler Q (N - k)) * qbin Q N (N - k) := by
      calc qbin Q N (N - k) * euler Q (N - k) * euler Q k
          ≈ euler Q k * (qbin Q N (N - k) * euler Q (N - k)) := Q'.mul_comm_eqv _ _
        _ ≈ euler Q k * (euler Q (N - k) * qbin Q N (N - k)) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
        _ ≈ (euler Q k * euler Q (N - k)) * qbin Q N (N - k) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- Algebraic even-power change of base; no restriction on a. -/
theorem square_pow (a : Q') (N : Nat) : (a * a) ^ N ≈ a ^ (2 * N) := by
  induction N with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      rw [Q'.pow_succ]
      calc (a * a) * (a * a) ^ N
          ≈ (a * a) * a ^ (2 * N) := Q'.mul_eqv_congr_left _ _ _ ih
        _ ≈ a * (a * a ^ (2 * N)) := Q'.mul_assoc_eqv _ _ _
        _ ≈ a ^ (2 * N + 1 + 1) := Q'.eqv_refl _
        _ ≈ a ^ (2 * (N + 1)) := by
          rw [show 2 * N + 1 + 1 = 2 * (N + 1) by omega]
          exact Q'.eqv_refl _

/-- Pin the new generic Euler product to the ORIGINAL theta-product Euler
factor. This is an algebraic identity for every a, not a limit assumption. -/
theorem euler_square_eq_theta (a : Q') (N : Nat) :
    euler (a * a) N ≈ RealTheta.eulerProd a N := by
  induction N with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      rw [euler_succ, RealTheta.eulerProd_succ]
      apply mul_congr ih
      apply Q'.add_eqv_congr_left
      apply Q'.neg_eqv_congr
      unfold ThetaConv.uAmp
      have h := square_pow a (N + 1)
      rw [show 2 * (N + 1) = 2 * N + 2 by omega] at h
      exact h

/-- The finite centered coefficient includes the Euler normalizer.
No claim that this equals one at finite N is made. -/
def centeredWeight (Q : Q') (N j : Nat) : Q' :=
  euler Q N * qbin Q (N + N) (N + j)

/-- Exact denominator-cleared normalized centered weight. -/
theorem centeredWeight_mul_euler (Q : Q') (N j : Nat) (hj : j ≤ N) :
    centeredWeight Q N j * (euler Q (N + j) * euler Q (N - j))
      ≈ euler Q N * euler Q (N + N) := by
  unfold centeredWeight
  calc (euler Q N * qbin Q (N + N) (N + j))
          * (euler Q (N + j) * euler Q (N - j))
      ≈ euler Q N * (qbin Q (N + N) (N + j)
          * (euler Q (N + j) * euler Q (N - j))) := Q'.mul_assoc_eqv _ _ _
    _ ≈ euler Q N * (qbin Q (N + N) (N + j)
          * euler Q (N + j) * euler Q (N - j)) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    _ ≈ euler Q N * euler Q (N + N) :=
      Q'.mul_eqv_congr_left _ _ _ (centered_qbin_mul_euler Q N j hj)

/-- The centered weight as a computable quotient of four finite products. -/
theorem centeredWeight_eq_quotient {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (N j : Nat) (hj : j ≤ N) :
    centeredWeight Q N j ≈ HKConv.divPos (euler Q N * euler Q (N + N))
      (euler Q (N + j) * euler Q (N - j)) := by
  have hD := HKPos.q_mul_pos (euler_pos hQ0 hQ1 (N + j)) (euler_pos hQ0 hQ1 (N - j))
  apply Q'.mul_left_cancel_of_pos hD
  calc (euler Q (N + j) * euler Q (N - j)) * centeredWeight Q N j
      ≈ centeredWeight Q N j * (euler Q (N + j) * euler Q (N - j)) := Q'.mul_comm_eqv _ _
    _ ≈ euler Q N * euler Q (N + N) := centeredWeight_mul_euler Q N j hj
    _ ≈ HKConv.divPos (euler Q N * euler Q (N + N))
          (euler Q (N + j) * euler Q (N - j))
          * (euler Q (N + j) * euler Q (N - j)) :=
      Q'.eqv_symm (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hD))
    _ ≈ (euler Q (N + j) * euler Q (N - j))
          * HKConv.divPos (euler Q N * euler Q (N + N))
            (euler Q (N + j) * euler Q (N - j)) := Q'.mul_comm_eqv _ _

end YMGap.Continuum.GaussQBinomEulerQuotient

#print axioms YMGap.Continuum.GaussQBinomEulerQuotient.euler_pos
#print axioms YMGap.Continuum.GaussQBinomEulerQuotient.qbin_eq_euler_quotient
#print axioms YMGap.Continuum.GaussQBinomEulerQuotient.qbin_complement
#print axioms YMGap.Continuum.GaussQBinomEulerQuotient.square_pow
#print axioms YMGap.Continuum.GaussQBinomEulerQuotient.euler_square_eq_theta
#print axioms YMGap.Continuum.GaussQBinomEulerQuotient.centeredWeight
#print axioms YMGap.Continuum.GaussQBinomEulerQuotient.centeredWeight_mul_euler
#print axioms YMGap.Continuum.GaussQBinomEulerQuotient.centeredWeight_eq_quotient
