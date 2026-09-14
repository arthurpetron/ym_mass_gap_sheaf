/-
# First nonzero SU(2) Casimir excess is at least five

A positive label costs at least three; changing a fundamental label to
any higher spin adds at least five. For two replicas with at least twelve
occupied faces, total heat power below 39 is therefore exactly 36.
This is an all-spin arithmetic theorem, not a sign or remainder bound.
-/

import YMGap.Continuum.SU2FiniteHeatPowerFactorization

namespace YMGap.Continuum.SU2FiniteCasimirFirstExcess

set_option autoImplicit false

open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteHeatPowerFactorization

theorem scalar_excess_zero_or_five (spin : Nat) : c4 spin - 3 = 0 ∨ 5 ≤ c4 spin - 3 := by
  by_cases h : spin ≤ 1
  · left
    have he : spin = 0 ∨ spin = 1 := by omega
    rcases he with he | he <;> rw [he] <;> rfl
  · right
    have hm : 8 ≤ c4 spin := Nat.mul_le_mul (show 2 ≤ spin by omega) (show 4 ≤ spin+2 by omega)
    omega

theorem excessSum_zero_or_five (state : Nat → Nat) : ∀ ids : List Nat,
    excessSum state ids = 0 ∨ 5 ≤ excessSum state ids
  | [] => Or.inl rfl
  | id::ids => by
    have h := scalar_excess_zero_or_five (state id)
    have ht := excessSum_zero_or_five state ids
    change (c4 (state id)-3)+excessSum state ids = 0 ∨ 5 ≤ (c4 (state id)-3)+excessSum state ids
    omega

/-- No Casimir total 37 or 38 can occur above the twelve-occupation floor. -/
theorem paired_small_power_eq36 (left right : Nat → Nat) (ids : List Nat)
    (ha : 12 ≤ positiveCount left ids + positiveCount right ids)
    (hp : casimirSum left ids + casimirSum right ids < 39) :
    casimirSum left ids + casimirSum right ids = 36 := by
  have hl := casimir_decomposition left ids
  have hr := casimir_decomposition right ids
  have el := excessSum_zero_or_five left ids
  have er := excessSum_zero_or_five right ids
  omega

end YMGap.Continuum.SU2FiniteCasimirFirstExcess

#print axioms YMGap.Continuum.SU2FiniteCasimirFirstExcess.scalar_excess_zero_or_five
#print axioms YMGap.Continuum.SU2FiniteCasimirFirstExcess.excessSum_zero_or_five
#print axioms YMGap.Continuum.SU2FiniteCasimirFirstExcess.paired_small_power_eq36
