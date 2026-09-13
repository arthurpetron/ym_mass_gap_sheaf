/-
# Gaussian weights in the finite symmetric Jacobi recurrence

The coefficients are the original recursive Gaussian binomials multiplied
by q^(j*j), not bare theta coefficients. The two-sided q-Pascal recurrence
becomes the exact coefficient update for multiplication by
1 + q^(4N+2) + 2 q^(2N+1) x.

This module keeps the central coefficient and the outermost coefficient
separate from the interior, so no negative natural exponent or silent
endpoint deletion enters the argument. No limit identity is asserted.
-/

import YMGap.Continuum.GaussQBinomSymmetricStep
import YMGap.Continuum.FiniteSymmetricChebyshev

namespace YMGap.Continuum.FiniteJacobiCoefficients

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.GaussQBinom
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.GaussQBinomSymmetricStep

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_add_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.add_num, Q'.add_den_cast, Cheb.mul_num,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (h' : c ≈ d) :
    a * c ≈ b * d := Cheb.mul_eqv_congr _ _ _ _ h h'

private theorem square_succ (j : Nat) :
    (j + 1) * (j + 1) = j * j + 2 * j + 1 := by
  rw [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

/-- The actual finite Gaussian coefficient, including its q-binomial weight. -/
def coeff (q : Q') (N j : Nat) : Q' :=
  q ^ (j * j) * qbin (q * q) (N + N) (N + j)

def amp (q : Q') (N : Nat) : Q' := q ^ (2 * N + 1)

def middle (q : Q') (N : Nat) : Q' := 1 + amp q N * amp q N

theorem square_base_lt_one {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    q * q < (1 : Q') := by
  apply HKPos.q_lt_of_le_of_lt (q := q) _ hq1
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left q 1 q (Q'.le_of_lt hq1) (Q'.le_of_lt hq0))
    (Q'.le_of_eqv (Q'.mul_one_eqv q))

theorem coeff_zero (q : Q') (N : Nat) :
    coeff q N 0 ≈ qbin (q * q) (N + N) N := by
  unfold coeff
  rw [Nat.mul_zero, Q'.pow_zero, Nat.add_zero]
  exact Q'.one_mul_eqv _

theorem coeff_top (q : Q') (N : Nat) : coeff q N N ≈ q ^ (N * N) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (qbin_diagonal (q * q) (N + N)))
    (Q'.mul_one_eqv _)

theorem coeff_out_of_range (q : Q') (N j : Nat) (hj : N < j) : coeff q N j ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (qbin_out_of_range (q * q) (N + N) (N + j) (by omega)))
    (Q'.mul_zero_eqv _)

theorem middle_power (q : Q') (N : Nat) :
    (q * q) ^ (N + N + 1) ≈ amp q N * amp q N := by
  calc (q * q) ^ (N + N + 1)
      ≈ q ^ (2 * (N + N + 1)) := square_pow q _
    _ ≈ q ^ ((2 * N + 1) + (2 * N + 1)) := by
      rw [show 2 * (N + N + 1) = (2 * N + 1) + (2 * N + 1) by omega]
      exact Q'.eqv_refl _
    _ ≈ amp q N * amp q N := Q'.eqv_symm (pow_add_eqv q _ _)

theorem upper_power (q : Q') (N j : Nat) :
    q ^ (j * j) * (q * q) ^ (N + j + 1)
      ≈ amp q N * q ^ ((j + 1) * (j + 1)) := by
  calc q ^ (j * j) * (q * q) ^ (N + j + 1)
      ≈ q ^ (j * j) * q ^ (2 * (N + j + 1)) := Q'.mul_eqv_congr_left _ _ _ (square_pow q _)
    _ ≈ q ^ (j * j + 2 * (N + j + 1)) := pow_add_eqv q _ _
    _ ≈ q ^ ((2 * N + 1) + (j + 1) * (j + 1)) := by
      rw [show j * j + 2 * (N + j + 1) = (2 * N + 1) + (j + 1) * (j + 1) by
        rw [square_succ]; omega]
      exact Q'.eqv_refl _
    _ ≈ amp q N * q ^ ((j + 1) * (j + 1)) := Q'.eqv_symm (pow_add_eqv q _ _)

theorem lower_power (q : Q') (N j : Nat) (hj : j + 1 ≤ N) :
    q ^ ((j + 1) * (j + 1)) * (q * q) ^ (N - j)
      ≈ amp q N * q ^ (j * j) := by
  calc q ^ ((j + 1) * (j + 1)) * (q * q) ^ (N - j)
      ≈ q ^ ((j + 1) * (j + 1)) * q ^ (2 * (N - j)) :=
        Q'.mul_eqv_congr_left _ _ _ (square_pow q _)
    _ ≈ q ^ ((j + 1) * (j + 1) + 2 * (N - j)) := pow_add_eqv q _ _
    _ ≈ q ^ ((2 * N + 1) + j * j) := by
      rw [show (j + 1) * (j + 1) + 2 * (N - j) = (2 * N + 1) + j * j by
        rw [square_succ]; omega]
      exact Q'.eqv_refl _
    _ ≈ amp q N * q ^ (j * j) := Q'.eqv_symm (pow_add_eqv q _ _)

/-- The noncentral, nonouter Gaussian coefficients follow the Chebyshev
three-neighbor rule exactly. -/
theorem coeff_step_interior {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (N j : Nat) (hj : j + 1 ≤ N) :
    coeff q (N + 1) (j + 1)
      ≈ amp q N * coeff q N j + middle q N * coeff q N (j + 1)
        + amp q N * coeff q N (j + 2) := by
  have h := centered_qbin_step (HKPos.q_mul_pos hq0 hq0) (square_base_lt_one hq0 hq1)
    N (j + 1) (by omega) hj
  rw [show N + 1 - (j + 1) = N - j by omega,
    show N + (j + 1) - 1 = N + j by omega,
    show N + (j + 1) + 1 = N + (j + 2) by omega] at h
  unfold coeff
  calc q ^ ((j + 1) * (j + 1)) * qbin (q * q) ((N + 1) + (N + 1)) ((N + 1) + (j + 1))
      ≈ q ^ ((j + 1) * (j + 1)) *
        ((q * q) ^ (N + (j + 2)) * qbin (q * q) (N + N) (N + (j + 2))
          + (1 + (q * q) ^ (N + N + 1)) * qbin (q * q) (N + N) (N + (j + 1))
          + (q * q) ^ (N - j) * qbin (q * q) (N + N) (N + j)) :=
        Q'.mul_eqv_congr_left _ _ _ h
    _ ≈ (q ^ ((j + 1) * (j + 1)) * (q * q) ^ (N - j)) * qbin (q * q) (N + N) (N + j)
        + (1 + (q * q) ^ (N + N + 1)) * (q ^ ((j + 1) * (j + 1)) * qbin (q * q) (N + N) (N + (j + 1)))
        + (q ^ ((j + 1) * (j + 1)) * (q * q) ^ (N + (j + 2))) * qbin (q * q) (N + N) (N + (j + 2)) := by
          mul_add_ring
    _ ≈ (amp q N * q ^ (j * j)) * qbin (q * q) (N + N) (N + j)
        + middle q N * (q ^ ((j + 1) * (j + 1)) * qbin (q * q) (N + N) (N + (j + 1)))
        + (amp q N * q ^ ((j + 2) * (j + 2))) * qbin (q * q) (N + N) (N + (j + 2)) :=
          Cheb.add_eqv_congr _ _ _ _
            (Cheb.add_eqv_congr _ _ _ _
              (Q'.mul_eqv_congr_right _ _ _ (lower_power q N j hj))
              (Q'.mul_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (middle_power q N))))
            (Q'.mul_eqv_congr_right _ _ _ (upper_power q N (j + 1)))
    _ ≈ amp q N * (q ^ (j * j) * qbin (q * q) (N + N) (N + j))
        + middle q N * (q ^ ((j + 1) * (j + 1)) * qbin (q * q) (N + N) (N + (j + 1)))
        + amp q N * (q ^ ((j + 2) * (j + 2)) * qbin (q * q) (N + N) (N + (j + 2))) := by
          mul_add_ring

/-- The outermost Gaussian coefficient is generated only from its previous
outermost neighbor; the other two old coefficients vanish. -/
theorem coeff_step_outer (q : Q') (N : Nat) :
    coeff q (N + 1) (N + 1) ≈ amp q N * coeff q N N := by
  calc coeff q (N + 1) (N + 1)
      ≈ q ^ ((N + 1) * (N + 1)) := coeff_top q _
    _ ≈ q ^ ((2 * N + 1) + N * N) := by
      rw [show (N + 1) * (N + 1) = (2 * N + 1) + N * N by rw [square_succ]; omega]
      exact Q'.eqv_refl _
    _ ≈ amp q N * q ^ (N * N) := Q'.eqv_symm (pow_add_eqv q _ _)
    _ ≈ amp q N * coeff q N N := Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (coeff_top q N))

/-- The central row counts both equal neighboring coefficients. -/
theorem coeff_step_center_pos {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (N : Nat) (hN : 0 < N) :
    coeff q (N + 1) 0 ≈ middle q N * coeff q N 0 + (2 : Q') * amp q N * coeff q N 1 := by
  have hQ0 := HKPos.q_mul_pos hq0 hq0
  have hQ1 := square_base_lt_one hq0 hq1
  have h := centered_qbin_step hQ0 hQ1 N 0 hN (by omega)
  simp only [Nat.add_zero, Nat.sub_zero] at h
  have hs := qbin_complement hQ0 hQ1 (N + N) (N + 1) (by omega)
  rw [show N + N - (N + 1) = N - 1 by omega] at hs
  have hp : (q * q) ^ (N + 1) ≈ amp q N * q ^ (1 * 1) := by
    have hu := upper_power q N 0
    simp only [Nat.zero_mul, Q'.pow_zero, Nat.add_zero] at hu
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _)) hu
  have hu : (q * q) ^ (N + 1) * qbin (q * q) (N + N) (N + 1)
      ≈ amp q N * coeff q N 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hp) (Q'.mul_assoc_eqv _ _ _)
  have hm : (1 + (q * q) ^ (N + N + 1)) * qbin (q * q) (N + N) N
      ≈ middle q N * coeff q N 0 :=
    mul_congr (Q'.add_eqv_congr_left _ _ _ (middle_power q N)) (Q'.eqv_symm (coeff_zero q N))
  have hd : amp q N * coeff q N 1 + amp q N * coeff q N 1
      ≈ (2 : Q') * amp q N * coeff q N 1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Cheb.two_mul_eqv _))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  calc coeff q (N + 1) 0
      ≈ qbin (q * q) ((N + 1) + (N + 1)) (N + 1) := coeff_zero q _
    _ ≈ (q * q) ^ (N + 1) * qbin (q * q) (N + N) (N + 1)
        + (1 + (q * q) ^ (N + N + 1)) * qbin (q * q) (N + N) N
        + (q * q) ^ (N + 1) * qbin (q * q) (N + N) (N - 1) := h
    _ ≈ amp q N * coeff q N 1 + middle q N * coeff q N 0 + amp q N * coeff q N 1 :=
      Cheb.add_eqv_congr _ _ _ _ (Cheb.add_eqv_congr _ _ _ _ hu hm)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hs)) hu)
    _ ≈ middle q N * coeff q N 0 + (amp q N * coeff q N 1 + amp q N * coeff q N 1) := by
      mul_add_ring
    _ ≈ middle q N * coeff q N 0 + (2 : Q') * amp q N * coeff q N 1 :=
      Q'.add_eqv_congr_left _ _ _ hd

/-- The central row at the first factor, proved directly from q-Pascal. -/
theorem coeff_one_center (q : Q') : coeff q 1 0 ≈ middle q 0 := by
  change (1 * ((0 + 1 * 1) + ((q * q) * 1) * 1)) ≈ 1 + (q * 1) * (q * 1)
  rw [Q'.zero_add']
  mul_add_ring

theorem coeff_step_center {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (N : Nat) :
    coeff q (N + 1) 0 ≈ middle q N * coeff q N 0 + (2 : Q') * amp q N * coeff q N 1 := by
  cases N with
  | succ N => exact coeff_step_center_pos hq0 hq1 (N + 1) (by omega)
  | zero =>
      have hz : coeff q 0 0 ≈ 1 := coeff_top q 0
      have htail : (2 : Q') * amp q 0 * coeff q 0 1 ≈ 0 :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (coeff_out_of_range q 0 1 (by omega)))
          (Q'.mul_zero_eqv _)
      calc coeff q 1 0 ≈ middle q 0 := coeff_one_center q
        _ ≈ middle q 0 * 1 + 0 := Q'.eqv_symm
          (by rw [Q'.add_zero']; exact Q'.mul_one_eqv _)
        _ ≈ middle q 0 * coeff q 0 0 + (2 : Q') * amp q 0 * coeff q 0 1 :=
          Cheb.add_eqv_congr _ _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hz))
            (Q'.eqv_symm htail)

/-- ALL finite coefficients of the next symmetric polynomial obey the
actual Chebyshev multiplication rule, including the center and endpoint. -/
theorem coeff_step {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (N j : Nat) (hj : j ≤ N + 1) :
    coeff q (N + 1) j
      ≈ FiniteSymmetricChebyshev.step (middle q N) (amp q N) (coeff q N) j := by
  cases j with
  | zero => exact coeff_step_center hq0 hq1 N
  | succ j =>
      by_cases hi : j + 1 ≤ N
      · exact coeff_step_interior hq0 hq1 N j hi
      · have he : j = N := by omega
        subst j
        have hz₁ : middle q N * coeff q N (N + 1) ≈ 0 :=
          Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (coeff_out_of_range q N (N + 1) (by omega)))
            (Q'.mul_zero_eqv _)
        have hz₂ : amp q N * coeff q N (N + 2) ≈ 0 :=
          Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (coeff_out_of_range q N (N + 2) (by omega)))
            (Q'.mul_zero_eqv _)
        calc coeff q (N + 1) (N + 1)
            ≈ amp q N * coeff q N N := coeff_step_outer q N
          _ ≈ amp q N * coeff q N N + 0 + 0 := by
            rw [Q'.add_zero', Q'.add_zero']; exact Q'.eqv_refl _
          _ ≈ FiniteSymmetricChebyshev.step (middle q N) (amp q N) (coeff q N) (N + 1) :=
            Cheb.add_eqv_congr _ _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hz₁))
              (Q'.eqv_symm hz₂)

end YMGap.Continuum.FiniteJacobiCoefficients

#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.square_base_lt_one
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff_zero
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff_top
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff_out_of_range
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.middle_power
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.upper_power
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.lower_power
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff_step_interior
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff_step_outer
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff_step_center_pos
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff_one_center
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff_step_center
#print axioms YMGap.Continuum.FiniteJacobiCoefficients.coeff_step
