/-
U.5 — a concrete `ExpUB` instance: the Padé/Bernoulli rational bound
`E(x) = 1/(1+x)` for `e^{-x}`.

`ExpBound.ExpUB` was abstract (the analytic seed of the character-tail
bound).  This module instantiates it concretely with the rational
upper-bound operator `E(x) = 1/(1+x)` (`x ≥ 0`), the `[0/1]` Padé
approximant of `e^{-x}` — the sharpest *rational* bound that is provably
`≥ e^{-x}` from the elementary `e^x ≥ 1+x`.

Defining `E` via `Int.toNat` clamping makes it literally `1/(1+max(0,x))`,
hence **antitone on all of `Q'`** (constant `1` for `x ≤ 0`, strictly
decreasing for `x ≥ 0`), so `ExpUB.E_antitone`'s universal quantifier is
met without a side condition.

This file proves the three structural `ExpUB` fields (`E_pos`,
`E_zero_le_one`, `E_antitone`) in pure `Q'`, axiom-clean.  The soundness
`e^{-x} ≤ E(x)` (the `expNeg` connection) is the named analytic obligation
tracked in `notes/uniform-character-tail-bound.md` / the plan U.5.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` only (the `Q'` order).  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Constructive.ExpBound

namespace YMGap.Constructive.ExpUBInstance

open YMGap.Constructive
open YMGap.Constructive.ExpBound

/-- `oneOver1p x = 1/(1+x)` for `x ≥ 0`, and `= 1` for `x ≤ 0`
(the `Int.toNat` clamp gives `1/(1+max(0,x))`).

For `x = n/d` (`d = x.den`), `1+x = (n+d)/d`, so `1/(1+x) = d/(n+d)`;
clamping `n ↦ n.toNat` collapses the `x < 0` branch to `d/d = 1`. -/
def oneOver1p (x : Q') : Q' :=
  ⟨(x.den : Int), x.num.toNat + x.den - 1⟩

@[simp] theorem oneOver1p_num (x : Q') : (oneOver1p x).num = (x.den : Int) := rfl

theorem oneOver1p_den (x : Q') : (oneOver1p x).den = x.num.toNat + x.den := by
  show (x.num.toNat + x.den - 1) + 1 = x.num.toNat + x.den
  have := x.den_pos; omega

/-- `E ≥ 0`: the numerator `x.den` is a positive `Nat`. -/
theorem oneOver1p_nonneg (x : Q') : (0 : Q') ≤ oneOver1p x := by
  rw [Q'.zero_le_iff_num_nonneg, oneOver1p_num]
  exact Int.natCast_nonneg x.den

/-- `E 0 = 1`. -/
theorem oneOver1p_zero : oneOver1p 0 = 1 := by decide

/-- `E` is antitone: `x ≤ y → E y ≤ E x`. -/
theorem oneOver1p_antitone (x y : Q') (hxy : x ≤ y) : oneOver1p y ≤ oneOver1p x := by
  -- unfold `≤` on `oneOver1p`: (y.den)(x.num⁺ + x.den) ≤ (x.den)(y.num⁺ + y.den)
  show (oneOver1p y).num * ((oneOver1p x).den : Int)
      ≤ (oneOver1p x).num * ((oneOver1p y).den : Int)
  rw [oneOver1p_num, oneOver1p_num, oneOver1p_den, oneOver1p_den]
  -- hypothesis: x.num * y.den ≤ y.num * x.den
  have h : x.num * (y.den : Int) ≤ y.num * (x.den : Int) := hxy
  have hxd : (0 : Int) < (x.den : Int) := by have := x.den_pos; omega
  have hyd : (0 : Int) < (y.den : Int) := by have := y.den_pos; omega
  -- key clamp inequality: x.num⁺ * y.den ≤ y.num⁺ * x.den
  have hclamp : (x.num.toNat : Int) * (y.den : Int) ≤ (y.num.toNat : Int) * (x.den : Int) := by
    rcases Int.lt_or_le x.num 0 with hxn | hxn
    · -- x.num < 0 ⇒ x.num⁺ = 0 ; RHS ≥ 0
      have : (x.num.toNat : Int) = 0 := by omega
      rw [this, Int.zero_mul]
      exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.le_of_lt hxd)
    · -- x.num ≥ 0 ⇒ x.num⁺ = x.num
      have hxt : (x.num.toNat : Int) = x.num := Int.toNat_of_nonneg hxn
      rcases Int.lt_or_le y.num 0 with hyn | hyn
      · -- y.num < 0 with x.num ≥ 0 contradicts x ≤ y (h)
        exfalso
        have h1 : (0 : Int) ≤ x.num * (y.den : Int) :=
          Int.mul_nonneg hxn (Int.le_of_lt hyd)
        have h2 : y.num * (x.den : Int) < 0 :=
          Int.mul_neg_of_neg_of_pos hyn hxd
        omega
      · have hyt : (y.num.toNat : Int) = y.num := Int.toNat_of_nonneg hyn
        rw [hxt, hyt]; exact h
  -- expand the products and cancel the common x.den*y.den
  have hcomm : (y.den : Int) * (x.den : Int) = (x.den : Int) * (y.den : Int) := Int.mul_comm _ _
  calc (y.den : Int) * ((x.num.toNat : Int) + (x.den : Int))
        = (y.den : Int) * (x.num.toNat : Int) + (y.den : Int) * (x.den : Int) := by
          rw [Int.mul_add]
    _ ≤ (x.den : Int) * (y.num.toNat : Int) + (x.den : Int) * (y.den : Int) := by
          have hA : (y.den : Int) * (x.num.toNat : Int) ≤ (x.den : Int) * (y.num.toNat : Int) := by
            rw [Int.mul_comm (y.den : Int) (x.num.toNat : Int),
                Int.mul_comm (x.den : Int) (y.num.toNat : Int)]
            exact hclamp
          have hB : (y.den : Int) * (x.den : Int) ≤ (x.den : Int) * (y.den : Int) :=
            Int.le_of_eq hcomm
          exact Int.add_le_add hA hB
    _ = (x.den : Int) * ((y.num.toNat : Int) + (y.den : Int)) := by rw [Int.mul_add]

/-- The concrete `ExpUB` seed: `E(x) = 1/(1+x)` (clamped). -/
def recipExpUB : ExpUB where
  E := oneOver1p
  E_pos := oneOver1p_nonneg
  E_zero_le_one := by decide
  E_antitone := oneOver1p_antitone

end YMGap.Constructive.ExpUBInstance

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.ExpUBInstance.oneOver1p_nonneg
#print axioms YMGap.Constructive.ExpUBInstance.oneOver1p_zero
#print axioms YMGap.Constructive.ExpUBInstance.oneOver1p_antitone
#print axioms YMGap.Constructive.ExpUBInstance.recipExpUB
