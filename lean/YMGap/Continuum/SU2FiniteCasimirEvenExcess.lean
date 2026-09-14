/-
# Even SU(2) heat powers: the next possible retained power is 42

The Casimir parity equals label parity. Above twelve occupied faces an
even total below 42 is exactly 36. At power 42 all fourteen occupations
are fundamental: a single higher-spin excess is 5 or at least 12, and
two nonzero excesses already cost at least 10.
These are finite all-spin arithmetic facts; no Haar assertion is made.
-/

import YMGap.Continuum.SU2FiniteCasimirFirstExcess
import YMGap.Continuum.SU2FiniteParityHigherProduct

namespace YMGap.Continuum.SU2FiniteCasimirEvenExcess

set_option autoImplicit false

open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteCasimirFirstExcess
open YMGap.Continuum.SU2FiniteParityHigherProduct

theorem casimir_mod_two (spin : Nat) : c4 spin%2=spin%2 := by
  have h : spin%2=0 ∨ spin%2=1 := by omega
  rw [c4, Nat.mul_mod, Nat.add_mod]
  rcases h with h | h <;> rw [h] <;> decide

theorem casimirSum_mod_two (state : Nat → Nat) : ∀ ids : List Nat,
    casimirSum state ids%2=parityCount state ids%2
  | [] => rfl
  | id::ids => by
    rw [casimirSum, parityCount, Nat.add_mod, casimir_mod_two, casimirSum_mod_two]
    omega

theorem parityCount_filter_length (state : Nat → Nat) : ∀ ids : List Nat,
    parityCount state ids=(ids.filter (fun id => decide (state id%2=1))).length
  | [] => rfl
  | id::ids => by
    have ih := parityCount_filter_length state ids
    by_cases h : state id%2=1
    · simp only [parityCount, List.filter_cons, h, decide_true, ↓reduceIte, List.length_cons]
      omega
    · have hz : state id%2=0 := by omega
      simpa only [parityCount, List.filter_cons, decide_eq_false h, Bool.false_eq_true, ↓reduceIte,
        hz, Nat.zero_add] using ih

theorem scalar_excess_zero_five_or_twelve (spin : Nat) :
    c4 spin-3=0 ∨ c4 spin-3=5 ∨ 12 ≤ c4 spin-3 := by
  by_cases hs : spin ≤ 2
  · have he : spin=0 ∨ spin=1 ∨ spin=2 := by omega
    rcases he with rfl | rfl | rfl <;> decide
  · have h : 15 ≤ c4 spin := Nat.mul_le_mul (show 3 ≤ spin by omega) (show 5 ≤ spin+2 by omega)
    omega

theorem excessSum_zero_five_or_ten (state : Nat → Nat) : ∀ ids : List Nat,
    excessSum state ids=0 ∨ excessSum state ids=5 ∨ 10 ≤ excessSum state ids
  | [] => Or.inl rfl
  | id::ids => by
    have hh := scalar_excess_zero_five_or_twelve (state id)
    have ht := excessSum_zero_five_or_ten state ids
    change (c4 (state id)-3)+excessSum state ids=0 ∨
      (c4 (state id)-3)+excessSum state ids=5 ∨ 10 ≤ (c4 (state id)-3)+excessSum state ids
    omega

theorem paired_even_sub42_eq36 (left right : Nat → Nat) (ids : List Nat)
    (ha : 12 ≤ positiveCount left ids+positiveCount right ids)
    (hp : casimirSum left ids+casimirSum right ids < 42)
    (he : (casimirSum left ids+casimirSum right ids)%2=0) :
    casimirSum left ids+casimirSum right ids=36 := by
  have hl := casimir_decomposition left ids
  have hr := casimir_decomposition right ids
  have el := excessSum_zero_or_five left ids
  have er := excessSum_zero_or_five right ids
  omega

theorem paired_power42_fundamental (left right : Nat → Nat) (ids : List Nat)
    (ha : 12 ≤ positiveCount left ids+positiveCount right ids)
    (hp : casimirSum left ids+casimirSum right ids=42) :
    positiveCount left ids+positiveCount right ids=14 ∧
      ∀ id, id ∈ ids → left id ≤ 1 ∧ right id ≤ 1 := by
  have hl := casimir_decomposition left ids
  have hr := casimir_decomposition right ids
  have el := excessSum_zero_five_or_ten left ids
  have er := excessSum_zero_five_or_ten right ids
  have zl : excessSum left ids=0 := by omega
  have zr : excessSum right ids=0 := by omega
  constructor
  · omega
  · intro id hi
    exact ⟨zero_excess_small left ids zl id hi,zero_excess_small right ids zr id hi⟩

end YMGap.Continuum.SU2FiniteCasimirEvenExcess

#print axioms YMGap.Continuum.SU2FiniteCasimirEvenExcess.casimir_mod_two
#print axioms YMGap.Continuum.SU2FiniteCasimirEvenExcess.casimirSum_mod_two
#print axioms YMGap.Continuum.SU2FiniteCasimirEvenExcess.parityCount_filter_length
#print axioms YMGap.Continuum.SU2FiniteCasimirEvenExcess.scalar_excess_zero_five_or_twelve
#print axioms YMGap.Continuum.SU2FiniteCasimirEvenExcess.excessSum_zero_five_or_ten
#print axioms YMGap.Continuum.SU2FiniteCasimirEvenExcess.paired_even_sub42_eq36
#print axioms YMGap.Continuum.SU2FiniteCasimirEvenExcess.paired_power42_fundamental
