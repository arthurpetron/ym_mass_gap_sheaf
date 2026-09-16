/-
# No rational square is one half

Parity descent supplies a representation-independent obstruction in `Q'`.
This is an arithmetic diagnostic: it does not modify a continuum frontier or
replace any coupling-matching requirement with a weaker statement.
-/

import YMGap.Constructive.Rationals

namespace YMGap.Constructive.Q'

set_option autoImplicit false

private theorem no_double_square (total : Nat) :
    ∀ d n : Nat, d + n = total → 0 < d → d * d = 2 * (n * n) → False := by
  induction total using Nat.strongRecOn with
  | ind total ih =>
      intro d n htotal hd heq
      have hmod : (d * d) % 2 = 0 := by
        rw [heq]
        exact Nat.mul_mod_right 2 (n * n)
      have heven : d % 2 = 0 := by
        have hrem : d % 2 < 2 := Nat.mod_lt d (by decide)
        by_cases hz : d % 2 = 0
        · exact hz
        · have hone : d % 2 = 1 := by omega
          rw [Nat.mul_mod, hone] at hmod
          contradiction
      have hdouble : d = 2 * (d / 2) := by
        have h := Nat.mod_add_div d 2
        omega
      have hsmall : d / 2 < d := Nat.div_lt_self hd (by decide)
      have hn : 0 < n := by
        have hdd : 0 < d * d := Nat.mul_pos hd hd
        by_cases hz : n = 0
        · subst n
          simp only [Nat.mul_zero] at heq
          omega
        · omega
      have hcancel : 2 * (2 * ((d / 2) * (d / 2))) = 2 * (n * n) := by
        calc
          _ = (2 * (d / 2)) * (2 * (d / 2)) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm]
          _ = d * d := by rw [← hdouble]
          _ = 2 * (n * n) := heq
      have hnext : n * n = 2 * ((d / 2) * (d / 2)) :=
        (Nat.mul_left_cancel (by decide : 0 < (2 : Nat)) hcancel).symm
      exact ih (n + d / 2) (by omega) n (d / 2) rfl hn hnext

/-- No signed rational, in any positive-denominator presentation, squares
to one half. The proof uses natural-number parity and strict descent. -/
theorem square_ne_half (q : Q') :
    ¬ Q'.eqv (q * q) (Q'.mkPos 1 2 (by decide)) := by
  intro h
  change (q.num * q.num) * 2 =
    1 * ((q.den * q.den - 1 + 1 : Nat) : Int) at h
  have hden : 1 ≤ q.den * q.den := Nat.mul_pos (den_pos q) (den_pos q)
  rw [Nat.sub_add_cancel hden, Int.one_mul] at h
  have habs := congrArg Int.natAbs h
  rw [Int.natAbs_mul, Int.natAbs_mul] at habs
  change q.num.natAbs * q.num.natAbs * 2 = q.den * q.den at habs
  apply no_double_square (q.den + q.num.natAbs) q.den q.num.natAbs rfl (den_pos q)
  exact habs.symm.trans (Nat.mul_comm _ _)

#print axioms square_ne_half

end YMGap.Constructive.Q'
