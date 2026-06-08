/-
Constructive absolute value on `Q'` and a sign-cased product bound — the
`Q'`-level layer that `CReal.mul` (and its product modulus) needs.

`Reals.lean` deliberately avoided `Q'.abs` for the *order* on `CReal`.  But
`CReal.mul`'s Cauchy estimate needs (i) a symmetric rational bound
`-B ≤ a_n ≤ B` on each factor (built as `B = |a_N| + 1`), and (ii) the product
bound `|u| ≤ B, |v| ≤ d ⇒ u·v ≤ B·d`.  This module supplies a minimal `abs`
(just the bound-construction lemmas — no triangle/`abs_mul` needed) and the
sign-cased `mul_le_of_bounds`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` only.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Constructive.RationalsMul

namespace YMGap.Constructive

namespace Q'

/-- `−b ≤ −a` from `a ≤ b` (negation reverses order). -/
theorem neg_le_neg {a b : Q'} (h : a ≤ b) : -b ≤ -a := by
  have h' : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h
  show (-b.num) * (a.den : Int) ≤ (-a.num) * (b.den : Int)
  rw [Int.neg_mul, Int.neg_mul]
  exact Int.neg_le_neg h'

/-- `0 ≤ −q` when `¬ (0 ≤ q)`. -/
theorem neg_nonneg_of_not_nonneg {q : Q'} (h : ¬ (0 : Q') ≤ q) : (0 : Q') ≤ -q := by
  rw [zero_le_iff_num_nonneg] at h ⊢
  show (0 : Int) ≤ -q.num
  exact Int.le_of_lt (Int.neg_pos.mpr (Int.not_le.mp h))

/-- `q ≤ 0` when `¬ (0 ≤ q)`. -/
theorem nonpos_of_not_nonneg {q : Q'} (h : ¬ (0 : Q') ≤ q) : q ≤ (0 : Q') := by
  rw [zero_le_iff_num_nonneg] at h
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.le_of_lt (Int.not_le.mp h)

/-- Absolute value: `|q| = q` if `0 ≤ q`, else `−q`. -/
def abs (q : Q') : Q' := if (0 : Q') ≤ q then q else -q

theorem abs_nonneg (q : Q') : (0 : Q') ≤ abs q := by
  unfold abs
  by_cases h : (0 : Q') ≤ q
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact neg_nonneg_of_not_nonneg h

theorem le_abs_self (q : Q') : q ≤ abs q := by
  unfold abs
  by_cases h : (0 : Q') ≤ q
  · rw [if_pos h]; exact le_refl' q
  · rw [if_neg h]
    exact le_trans' q 0 (-q) (nonpos_of_not_nonneg h) (neg_nonneg_of_not_nonneg h)

theorem neg_le_abs (q : Q') : -q ≤ abs q := by
  unfold abs
  by_cases h : (0 : Q') ≤ q
  · rw [if_pos h]
    have h1 : -q ≤ -(0 : Q') := neg_le_neg h
    have e : (-(0 : Q')) = 0 := rfl
    rw [e] at h1
    exact le_trans' (-q) 0 q h1 h
  · rw [if_neg h]; exact le_refl' (-q)

/-- `−B ≤ q` and `q ≤ B` give `|q| ≤ B`. -/
theorem abs_le {q b : Q'} (h1 : -b ≤ q) (h2 : q ≤ b) : abs q ≤ b := by
  unfold abs
  by_cases h : (0 : Q') ≤ q
  · rw [if_pos h]; exact h2
  · rw [if_neg h]
    have := neg_le_neg h1  -- -q ≤ -(-b)
    exact le_trans' (-q) (-(-b)) b this (le_of_eqv (neg_neg_eqv b))

/-- **Sign-cased product bound**: `|u| ≤ B`, `|v| ≤ d` (`B, d ≥ 0`) ⇒ `u·v ≤ B·d`. -/
theorem mul_le_of_bounds {u v B d : Q'} (hB : (0 : Q') ≤ B) (hd : (0 : Q') ≤ d)
    (hu1 : -B ≤ u) (hu2 : u ≤ B) (hv1 : -d ≤ v) (hv2 : v ≤ d) : u * v ≤ B * d := by
  by_cases hu : (0 : Q') ≤ u
  · -- u ≥ 0:  u·v ≤ u·d ≤ B·d
    exact le_trans' (u * v) (u * d) (B * d)
      (mul_le_mul_of_nonneg_left v d u hv2 hu)
      (mul_le_mul_of_nonneg_right u B d hu2 hd)
  · -- u < 0:  u·v = −((−u)·v) ≤ (−u)·d ≤ B·d
    have hw : (0 : Q') ≤ -u := neg_nonneg_of_not_nonneg hu
    have hwB : -u ≤ B := le_trans' (-u) (-(-B)) B (neg_le_neg hu1) (le_of_eqv (neg_neg_eqv B))
    have step1 : (-u) * (-d) ≤ (-u) * v := mul_le_mul_of_nonneg_left (-d) v (-u) hv1 hw
    have e1 : ((-u) * (-d)).eqv (-((-u) * d)) := mul_neg_eqv (-u) d
    have h5 : -((-u) * d) ≤ (-u) * v :=
      le_trans' (-((-u) * d)) ((-u) * (-d)) ((-u) * v) (ge_of_eqv e1) step1
    have h6 : -((-u) * v) ≤ -(-((-u) * d)) := neg_le_neg h5
    have h7 : -((-u) * v) ≤ (-u) * d :=
      le_trans' (-((-u) * v)) (-(-((-u) * d))) ((-u) * d) h6
        (le_of_eqv (neg_neg_eqv ((-u) * d)))
    have huv : (u * v).eqv (-((-u) * v)) :=
      eqv_trans (u * v) ((-(-u)) * v) (-((-u) * v))
        (mul_eqv_congr_right u (-(-u)) v (eqv_symm (neg_neg_eqv u)))
        (neg_mul_eqv (-u) v)
    have step3 : (-u) * d ≤ B * d := mul_le_mul_of_nonneg_right (-u) B d hwB hd
    exact le_trans' (u * v) ((-u) * d) (B * d)
      (le_trans' (u * v) (-((-u) * v)) ((-u) * d) (le_of_eqv huv) h7) step3

end Q'

end YMGap.Constructive

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.Q'.neg_le_neg
#print axioms YMGap.Constructive.Q'.abs_nonneg
#print axioms YMGap.Constructive.Q'.le_abs_self
#print axioms YMGap.Constructive.Q'.neg_le_abs
#print axioms YMGap.Constructive.Q'.abs_le
#print axioms YMGap.Constructive.Q'.mul_le_of_bounds
