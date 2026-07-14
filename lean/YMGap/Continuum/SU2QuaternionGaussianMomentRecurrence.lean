/-
# Constructive product-Gaussian moment recurrences

The Hermite positivity route starts from the exact algebraic integration-by-
parts recurrence `mu_(n+2) = (n+1) mu_n`.  No representing measure is used:
the recurrence follows directly from the odd-double-factorial formula.
-/

import YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor

namespace YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 300000
set_option maxRecDepth 10000

private theorem oddDoubleFactorial_succ (k : Nat) :
    oddDoubleFactorial (k + 1) =
      (2 * k + 1) * oddDoubleFactorial k := by
  rfl

private theorem gaussianMoment4_eq_of_even (e0 e1 e2 e3 : Nat)
    (hEven : e0 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0) :
    gaussianMoment4 e0 e1 e2 e3 =
      Q'.ofNat
        (oddDoubleFactorial (e0 / 2) * oddDoubleFactorial (e1 / 2) *
          oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e3 / 2)) := by
  simp [gaussianMoment4, hEven]

private theorem gaussianMoment4_eq_zero_of_not_even (e0 e1 e2 e3 : Nat)
    (hEven : ¬ (e0 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0)) :
    gaussianMoment4 e0 e1 e2 e3 = 0 := by
  simp [gaussianMoment4, hEven]

theorem gaussianMoment4_swap01 (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 e0 e1 e2 e3 ≈ gaussianMoment4 e1 e0 e2 e3 := by
  by_cases h : e0 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0
  · have hs : e1 % 2 = 0 ∧ e0 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0 :=
      ⟨h.2.1, h.1, h.2.2⟩
    rw [gaussianMoment4_eq_of_even _ _ _ _ h,
      gaussianMoment4_eq_of_even _ _ _ _ hs]
    have hN :
        oddDoubleFactorial (e0 / 2) * oddDoubleFactorial (e1 / 2) *
            oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e3 / 2) =
          oddDoubleFactorial (e1 / 2) * oddDoubleFactorial (e0 / 2) *
            oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e3 / 2) := by
      ac_rfl
    rw [hN]
    exact Q'.eqv_refl _
  · have hs : ¬
        (e1 % 2 = 0 ∧ e0 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0) := by
      intro hs
      exact h ⟨hs.2.1, hs.1, hs.2.2⟩
    rw [gaussianMoment4_eq_zero_of_not_even _ _ _ _ h,
      gaussianMoment4_eq_zero_of_not_even _ _ _ _ hs]
    exact Q'.eqv_refl 0

theorem gaussianMoment4_swap02 (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 e0 e1 e2 e3 ≈ gaussianMoment4 e2 e1 e0 e3 := by
  by_cases h : e0 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0
  · have hs : e2 % 2 = 0 ∧ e1 % 2 = 0 ∧ e0 % 2 = 0 ∧ e3 % 2 = 0 :=
      ⟨h.2.2.1, h.2.1, h.1, h.2.2.2⟩
    rw [gaussianMoment4_eq_of_even _ _ _ _ h,
      gaussianMoment4_eq_of_even _ _ _ _ hs]
    have hN :
        oddDoubleFactorial (e0 / 2) * oddDoubleFactorial (e1 / 2) *
            oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e3 / 2) =
          oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e1 / 2) *
            oddDoubleFactorial (e0 / 2) * oddDoubleFactorial (e3 / 2) := by
      ac_rfl
    rw [hN]
    exact Q'.eqv_refl _
  · have hs : ¬
        (e2 % 2 = 0 ∧ e1 % 2 = 0 ∧ e0 % 2 = 0 ∧ e3 % 2 = 0) := by
      intro hs
      exact h ⟨hs.2.2.1, hs.2.1, hs.1, hs.2.2.2⟩
    rw [gaussianMoment4_eq_zero_of_not_even _ _ _ _ h,
      gaussianMoment4_eq_zero_of_not_even _ _ _ _ hs]
    exact Q'.eqv_refl 0

theorem gaussianMoment4_swap03 (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 e0 e1 e2 e3 ≈ gaussianMoment4 e3 e1 e2 e0 := by
  by_cases h : e0 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0
  · have hs : e3 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e0 % 2 = 0 :=
      ⟨h.2.2.2, h.2.1, h.2.2.1, h.1⟩
    rw [gaussianMoment4_eq_of_even _ _ _ _ h,
      gaussianMoment4_eq_of_even _ _ _ _ hs]
    have hN :
        oddDoubleFactorial (e0 / 2) * oddDoubleFactorial (e1 / 2) *
            oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e3 / 2) =
          oddDoubleFactorial (e3 / 2) * oddDoubleFactorial (e1 / 2) *
            oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e0 / 2) := by
      ac_rfl
    rw [hN]
    exact Q'.eqv_refl _
  · have hs : ¬
        (e3 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e0 % 2 = 0) := by
      intro hs
      exact h ⟨hs.2.2.2, hs.2.1, hs.2.2.1, hs.1⟩
    rw [gaussianMoment4_eq_zero_of_not_even _ _ _ _ h,
      gaussianMoment4_eq_zero_of_not_even _ _ _ _ hs]
    exact Q'.eqv_refl 0

/-- Gaussian integration-by-parts recurrence in the first coordinate. -/
theorem gaussianMoment4_shift0 (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 (e0 + 2) e1 e2 e3 ≈
      Q'.ofNat (e0 + 1) * gaussianMoment4 e0 e1 e2 e3 := by
  by_cases h0 : e0 % 2 = 0
  · by_cases h1 : e1 % 2 = 0
    · by_cases h2 : e2 % 2 = 0
      · by_cases h3 : e3 % 2 = 0
        · have h0plus : (e0 + 2) % 2 = 0 := by omega
          have hdiv : (e0 + 2) / 2 = e0 / 2 + 1 := by omega
          have hcoeff : e0 + 1 = 2 * (e0 / 2) + 1 := by omega
          have hg0 : gaussianMoment4 e0 e1 e2 e3 =
              Q'.ofNat
                (oddDoubleFactorial (e0 / 2) * oddDoubleFactorial (e1 / 2) *
                  oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e3 / 2)) := by
            simp [gaussianMoment4, h0, h1, h2, h3]
          have hg2 : gaussianMoment4 (e0 + 2) e1 e2 e3 =
              Q'.ofNat
                (oddDoubleFactorial (e0 / 2 + 1) *
                  oddDoubleFactorial (e1 / 2) * oddDoubleFactorial (e2 / 2) *
                  oddDoubleFactorial (e3 / 2)) := by
            simp [gaussianMoment4, h0plus, h1, h2, h3, hdiv]
          rw [hg0, hg2, hcoeff, oddDoubleFactorial_succ]
          show _ * (_ : Int) = _ * (_ : Int)
          simp only [Q'.mul_num_cast, Q'.mul_den_cast,
            Q'.ofNat_num_cast, Q'.ofNat_den_cast]
          push_cast
          ac_rfl
        · have h3plus : ¬ e3 % 2 = 0 := h3
          simp [gaussianMoment4, h3plus]
          exact Q'.eqv_refl 0
      · have h2plus : ¬ e2 % 2 = 0 := h2
        simp [gaussianMoment4, h2plus]
        exact Q'.eqv_refl 0
    · have h1plus : ¬ e1 % 2 = 0 := h1
      simp [gaussianMoment4, h1plus]
      exact Q'.eqv_refl 0
  · simp [gaussianMoment4, h0]
    exact Q'.eqv_refl 0

theorem gaussianMoment4_shift1 (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 e0 (e1 + 2) e2 e3 ≈
      Q'.ofNat (e1 + 1) * gaussianMoment4 e0 e1 e2 e3 := by
  refine Q'.eqv_trans _ (gaussianMoment4 (e1 + 2) e0 e2 e3) _
    (gaussianMoment4_swap01 e0 (e1 + 2) e2 e3) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (e1 + 1) * gaussianMoment4 e1 e0 e2 e3) _
    (gaussianMoment4_shift0 e1 e0 e2 e3) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (gaussianMoment4_swap01 e1 e0 e2 e3)

theorem gaussianMoment4_shift2 (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 e0 e1 (e2 + 2) e3 ≈
      Q'.ofNat (e2 + 1) * gaussianMoment4 e0 e1 e2 e3 := by
  refine Q'.eqv_trans _ (gaussianMoment4 (e2 + 2) e1 e0 e3) _
    (gaussianMoment4_swap02 e0 e1 (e2 + 2) e3) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (e2 + 1) * gaussianMoment4 e2 e1 e0 e3) _
    (gaussianMoment4_shift0 e2 e1 e0 e3) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (gaussianMoment4_swap02 e2 e1 e0 e3)

theorem gaussianMoment4_shift3 (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 e0 e1 e2 (e3 + 2) ≈
      Q'.ofNat (e3 + 1) * gaussianMoment4 e0 e1 e2 e3 := by
  refine Q'.eqv_trans _ (gaussianMoment4 (e3 + 2) e1 e2 e0) _
    (gaussianMoment4_swap03 e0 e1 e2 (e3 + 2)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (e3 + 1) * gaussianMoment4 e3 e1 e2 e0) _
    (gaussianMoment4_shift0 e3 e1 e2 e0) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (gaussianMoment4_swap03 e3 e1 e2 e0)

end YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence

#print axioms YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence.gaussianMoment4_shift0
#print axioms YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence.gaussianMoment4_shift1
#print axioms YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence.gaussianMoment4_shift2
#print axioms YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence.gaussianMoment4_shift3
