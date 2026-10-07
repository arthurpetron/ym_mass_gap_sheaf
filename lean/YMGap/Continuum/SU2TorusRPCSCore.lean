/-
# Torus RP (f1): integer discriminant core of the polarization Cauchy–Schwarz

`cs_int`: if `0 ≤ s²a + 2st·b + t²c (written `s*s*a + (s*t*b + s*t*b) + t*t*c`)` for all integers `s, t`, then `b·b ≤ a·c`. The proof is constructive, by cases
on the decidable `0 < c` and `0 < a`. This is the arithmetic core of `TorusCS`; lifting it to `Q'` and the bilinear
expansion of `rpB` are not done.

**OPEN: `TorusCS` is not proved.**
-/

namespace YMGap.Continuum.SU2TorusRPCSCore

set_option autoImplicit false

theorem quad_id (a b c : Int) : c * c * a + (c * (-b) * b + c * (-b) * b) + (-b) * (-b) * c = c * (a * c - b * b) := by
  simp only [Int.mul_add, Int.mul_neg, Int.neg_mul, Int.sub_eq_add_neg, Int.neg_neg, Int.mul_sub]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem quad_id' (a b c : Int) : (-b) * (-b) * a + ((-b) * a * b + (-b) * a * b) + a * a * c = a * (a * c - b * b) := by
  simp only [Int.mul_add, Int.mul_neg, Int.neg_mul, Int.sub_eq_add_neg, Int.neg_neg, Int.mul_sub]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem cs_int (a b c : Int) (h : ∀ s t : Int, 0 ≤ s * s * a + (s * t * b + s * t * b) + t * t * c) : b * b ≤ a * c := by
  have hc : 0 ≤ c := by have := h 0 1; simp only [Int.mul_zero, Int.zero_mul, Int.mul_one, Int.zero_add] at this; omega
  have ha : 0 ≤ a := by have := h 1 0; simp only [Int.mul_zero, Int.zero_mul, Int.mul_one, Int.add_zero] at this; omega
  by_cases hcp : 0 < c
  · have h1 := h c (-b); rw [quad_id, Int.mul_comm] at h1
    have : 0 ≤ a * c - b * b := Int.nonneg_of_mul_nonneg_left h1 hcp
    omega
  · have hc0 : c = 0 := by omega
    by_cases hap : 0 < a
    · have h1 := h (-b) a; rw [quad_id', Int.mul_comm] at h1
      have : 0 ≤ a * c - b * b := Int.nonneg_of_mul_nonneg_left h1 hap
      omega
    · have ha0 : a = 0 := by omega
      subst hc0; subst ha0
      have h1 := h 1 (-b)
      simp only [Int.mul_zero, Int.mul_one, Int.one_mul, Int.add_zero, Int.zero_add, Int.mul_neg,
        Int.neg_mul] at h1
      simp only [Int.mul_zero]
      omega

end YMGap.Continuum.SU2TorusRPCSCore

#print axioms YMGap.Continuum.SU2TorusRPCSCore.cs_int
