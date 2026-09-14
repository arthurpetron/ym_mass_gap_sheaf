/-
# Parity bits and higher labels have separate SU(2) costs

Write j = 2*h+b with b=j%2 and h=j/2. The exact Casimir is at
least 3*b+8*h, while the squared dimension is at most 4^b*9^h.
These are all-label arithmetic bounds, not a count of admissible states.
-/

import YMGap.Continuum.SU2FiniteHeatPowerFactorization

namespace YMGap.Continuum.SU2ParityHigherArithmetic

set_option autoImplicit false

open YMGap.Continuum.RGTransport

theorem label_split (spin : Nat) : spin = 2*(spin/2) + spin%2 := by omega

theorem casimir_parity_floor (spin : Nat) : 3*(spin%2) + 8*(spin/2) ≤ c4 spin := by
  by_cases h : spin ≤ 1
  · have he : spin = 0 ∨ spin = 1 := by omega
    rcases he with he | he <;> subst spin <;> decide
  · have hm := Nat.mul_le_mul_left spin (show 4 ≤ spin+2 by omega)
    change 3*(spin%2) + 8*(spin/2) ≤ spin*(spin+2)
    omega

theorem dimension_encoded (bit : Nat) (hb : bit ≤ 1) : ∀ higher : Nat,
    2*higher + bit + 1 ≤ 2^bit * 3^higher
  | 0 => by
    have he : bit = 0 ∨ bit = 1 := by omega
    rcases he with he | he <;> subst bit <;> decide
  | higher+1 => by
    calc
      2*(higher+1)+bit+1 ≤ 3*(2*higher+bit+1) := by omega
      _ ≤ 3*(2^bit*3^higher) := Nat.mul_le_mul_left 3 (dimension_encoded bit hb higher)
      _ = 2^bit*3^(higher+1) := by rw [Nat.pow_succ]; ac_rfl

theorem dimension_parity_bound (spin : Nat) : spin+1 ≤ 2^(spin%2)*3^(spin/2) := by
  calc
    spin+1 = 2*(spin/2)+spin%2+1 := by omega
    _ ≤ 2^(spin%2)*3^(spin/2) := dimension_encoded _ (by omega) _

theorem dimension_square_bound (spin : Nat) : (spin+1)*(spin+1) ≤ 4^(spin%2)*9^(spin/2) := by
  calc
    (spin+1)*(spin+1) ≤ (2^(spin%2)*3^(spin/2))*(2^(spin%2)*3^(spin/2)) :=
      Nat.mul_le_mul (dimension_parity_bound spin) (dimension_parity_bound spin)
    _ = (2^(spin%2)*2^(spin%2))*(3^(spin/2)*3^(spin/2)) := by ac_rfl
    _ = 4^(spin%2)*9^(spin/2) := by rw [← Nat.mul_pow, ← Nat.mul_pow]

end YMGap.Continuum.SU2ParityHigherArithmetic

#print axioms YMGap.Continuum.SU2ParityHigherArithmetic.label_split
#print axioms YMGap.Continuum.SU2ParityHigherArithmetic.casimir_parity_floor
#print axioms YMGap.Continuum.SU2ParityHigherArithmetic.dimension_encoded
#print axioms YMGap.Continuum.SU2ParityHigherArithmetic.dimension_parity_bound
#print axioms YMGap.Continuum.SU2ParityHigherArithmetic.dimension_square_bound
