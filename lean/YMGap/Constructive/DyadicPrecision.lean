/-
# Least executable dyadic precision below a positive rational

`HalfPow.pow_half_le` supplies the coarse witness `epsilon.den` for
`(1/2)^n <= epsilon`.  This module searches the finite interval up to that
witness and returns the first successful exponent.  The returned value is
therefore no larger than any supplied successful candidate, so later analytic
proofs can establish logarithmic-size bounds without changing the executable
search program.

## Axiom gate

Constructive `Nat`/`Bool`/`Q'` recursion only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, functional extensionality, or
noncomputable declaration.
-/

import YMGap.Constructive.HalfPow

namespace YMGap.Constructive.DyadicPrecision

/-! ## 1. Bounded first-success search -/

/-- Search the half-open natural interval `[start, start + fuel)` for the
first point satisfying `test`, falling back to the right endpoint. -/
def firstTrue (test : Nat -> Bool) : Nat -> Nat -> Nat
  | 0, start => start
  | fuel + 1, start =>
      if test start then start else firstTrue test fuel (start + 1)

theorem firstTrue_sound (test : Nat -> Bool) :
    forall fuel start witness,
      start <= witness ->
      witness < start + fuel ->
      test witness = true ->
      test (firstTrue test fuel start) = true
  | 0, _, _, _, hwitness, _ => False.elim (by omega)
  | fuel + 1, start, witness, hstart, hwitness, htest => by
      unfold firstTrue
      by_cases hhere : test start = true
      · rw [if_pos hhere]
        exact hhere
      · rw [if_neg hhere]
        have hne : witness ≠ start := by
          intro heq
          subst witness
          exact hhere htest
        exact firstTrue_sound test fuel (start + 1) witness
          (by omega) (by omega) htest

/-- The bounded first-success search never exceeds any successful point at or
to the right of its start. -/
theorem firstTrue_le_of_true (test : Nat -> Bool) :
    forall fuel start witness,
      start <= witness ->
      test witness = true ->
      firstTrue test fuel start <= witness
  | 0, _, _, hstart, _ => hstart
  | fuel + 1, start, witness, hstart, htest => by
      unfold firstTrue
      by_cases hhere : test start = true
      · rw [if_pos hhere]
        exact hstart
      · rw [if_neg hhere]
        have hne : witness ≠ start := by
          intro heq
          subst witness
          exact hhere htest
        exact firstTrue_le_of_true test fuel (start + 1) witness
          (by omega) htest

/-! ## 2. Least dyadic precision -/

/-- Least exponent found in the certified finite search window for which
`(1/2)^n <= epsilon`. -/
def least (epsilon : Q') : Nat :=
  firstTrue
    (fun precision => decide (HalfPow.half ^ precision <= epsilon))
    (epsilon.den + 1) 0

theorem half_pow_le_at_least
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    HalfPow.half ^ least epsilon <= epsilon := by
  have hwitness :
      (fun precision =>
        decide (HalfPow.half ^ precision <= epsilon)) epsilon.den = true :=
    decide_eq_true (HalfPow.pow_half_le epsilon hepsilon)
  have hsound :=
    firstTrue_sound
      (fun precision =>
        decide (HalfPow.half ^ precision <= epsilon))
      (epsilon.den + 1) 0 epsilon.den
      (Nat.zero_le _) (by omega) hwitness
  exact of_decide_eq_true hsound

/-- Minimality interface: any analytically supplied dyadic exponent below the
tolerance bounds the executable least precision. -/
theorem least_le_of_half_pow_le
    {epsilon : Q'} {precision : Nat}
    (hprecision : HalfPow.half ^ precision <= epsilon) :
    least epsilon <= precision := by
  exact firstTrue_le_of_true
    (fun candidate =>
      decide (HalfPow.half ^ candidate <= epsilon))
    (epsilon.den + 1) 0 precision
    (Nat.zero_le _) (decide_eq_true hprecision)

/-! ## Axiom audit -/

#print axioms firstTrue_sound
#print axioms firstTrue_le_of_true
#print axioms half_pow_le_at_least
#print axioms least_le_of_half_pow_le

end YMGap.Constructive.DyadicPrecision
