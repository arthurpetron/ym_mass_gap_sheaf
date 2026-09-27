/-
# Degree is bounded by the conservative local cone budget

For nonempty initial support, the explicit cone budget used by the local
auxiliary estimate dominates its recurrence degree. This is an elementary
natural-number comparison, not a decay or mass-gap assertion.
-/

import YMGap.Continuum.BF4ExactSlabLocalAuxiliaryCoercivity

namespace YMGap.Continuum.BF4ExactSlabConeBudgetDegree

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabLocalAuxiliaryCoercivity

private theorem degree_le_power (n : Nat) : n+1 ≤ 25^(16*(n+1)) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hexp : 16*((n+1)+1) = 16*(n+1)+16 := by omega
      rw [hexp, Nat.pow_add]
      calc
        n+2 ≤ 2*(n+1) := by omega
        _ ≤ 2*(25^(16*(n+1))) := Nat.mul_le_mul_left 2 ih
        _ = 25^(16*(n+1))*2 := Nat.mul_comm _ _
        _ ≤ 25^(16*(n+1))*25^16 :=
          Nat.mul_le_mul_left _ (by decide)

/-- If the initial support is nonempty, its conservative cone-volume budget
dominates the Chebyshev recurrence degree. -/
theorem degree_le_coneBudget (size n : Nat) (hs : 1 ≤ size) :
    n+1 ≤ coneBudget size n := by
  unfold coneBudget
  calc
    n+1 ≤ 25^(16*(n+1)) := degree_le_power n
    _ ≤ 25^(16*(n+1)) * size := by
      have h := Nat.mul_le_mul_left (25^(16*(n+1))) hs
      simpa using h

#print axioms degree_le_coneBudget

end YMGap.Continuum.BF4ExactSlabConeBudgetDegree
