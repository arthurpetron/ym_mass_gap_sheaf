/-
Monotonicity of the constructive `artanh` series and of its argument `yOf` —
the two load-bearing analytic residuals of `HamiltonianSpectrumInf`.

# What this module delivers (genuine content, no residuals left)

This module DISCHARGES the two named `Type`-level residuals
`HamiltonianSpectrumInf.YOfMonotone` and
`HamiltonianSpectrumInf.ArtanhMonotoneWindow` by constructing witnesses:

  * `yOf_mono` — the artanh argument `yOf m = (m−1)/(m+1)` is monotone in `m`.
    Route: reciprocal-antitone (`recipPos_antitone`) + the affine rewrite
    `yOf m ≃ 1 + (−2)·recipPos(m+1)` (`yOf_eqv_one_sub`).
  * `artanh_mono_window` — for window arguments `|y|,|y'| ≤ 1/3`, `y ≤ y'`
    implies `leEv (artanh y) (artanh y')`.  Route: odd-power monotonicity of the
    signed terms (`oddPow_mono`, via the sign helper `neg_pow_odd_eqv`), hence of
    every partial sum (`partialSum_mono_arg`); the pointwise `≤` gives `leEv`
    directly with no ε-accumulation.

The two structure values `yOfMonotone` / `artanhMonotoneWindow` package these
into the residual structures, so downstream `hamiltonianGap_le_energy` and
`spectrumInfResidual` become unconditional once fed these witnesses.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  The three-way sign splits use the
DECIDABLE `Q'.le` (`q_le_of_not_le`), not `Classical.em`.  No `Classical.*`,
no `sorryAx`, no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.HamiltonianSpectrumInf

open YMGap.Constructive
open YMGap.Constructive.CRealLog

namespace YMGap.Continuum.ArtanhMonotone

/-- `¬ (p ≤ q) → q ≤ p` on the DECIDABLE `Q'.le` (`Int` trichotomy on numerators).
Local copy to keep the import surface minimal; the sign split stays axiom-clean. -/
theorem q_le_of_not_le {p q : Q'} (h : ¬ (p ≤ q)) : q ≤ p := by
  show q.num * (p.den : Int) ≤ p.num * (q.den : Int)
  have h' : ¬ (p.num * (q.den : Int) ≤ q.num * (p.den : Int)) := h
  exact Int.le_of_lt (Int.not_le.mp h')

/-! ## (b) `ArtanhMonotoneWindow` — odd-power monotonicity of the signed terms -/

/-- **L1 (sign helper).**  `(−y)^{2k+1} ≃ −(y^{2k+1})`: odd powers flip the sign.
Induction on `k`, folding through `pow_odd_step_eqv`. -/
theorem neg_pow_odd_eqv (y : Q') : ∀ k : Nat,
    ((-y) ^ (2 * k + 1)).eqv (-(y ^ (2 * k + 1)))
  | 0 => by
    -- `2*0+1 = 1`; `(-y)^1 ≃ -y` and `-(y^1) ≃ -y`.
    have h1 : ((-y) ^ (2 * 0 + 1)).eqv (-y) := by
      show ((-y) * (-y) ^ 0).eqv (-y)
      exact Q'.mul_one_eqv (-y)
    have h2 : (y ^ (2 * 0 + 1)).eqv y := by
      show (y * y ^ 0).eqv y
      exact Q'.mul_one_eqv y
    exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_symm (Q'.neg_eqv_congr _ _ h2))
  | k + 1 => by
    -- `(-y)^{2(k+1)+1} ≃ ((-y)(-y))·(-y)^{2k+1} ≃ (yy)·(-(y^{2k+1})) ≃ -(y^{2(k+1)+1})`.
    have hsq : ((-y) * (-y)).eqv (y * y) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y (-y)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv y y)) ?_
      exact Q'.neg_neg_eqv (y * y)
    have ih := neg_pow_odd_eqv y k
    refine Q'.eqv_trans _ _ _ (pow_odd_step_eqv (-y) k) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right ((-y) * (-y)) (y * y) ((-y) ^ (2 * k + 1)) hsq) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (y * y) ((-y) ^ (2 * k + 1)) (-(y ^ (2 * k + 1))) ih) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (y * y) (y ^ (2 * k + 1))) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.eqv_symm (pow_odd_step_eqv y k))

/-- **L2.**  Odd powers are monotone in the base (no sign hypothesis).  Decidable
three-way sign split via `q_le_of_not_le`. -/
theorem oddPow_mono (y y' : Q') (k : Nat) (h : y ≤ y') :
    y ^ (2 * k + 1) ≤ y' ^ (2 * k + 1) := by
  by_cases hy0 : (0 : Q') ≤ y
  · -- `0 ≤ y ≤ y'`.
    exact pow_le_pow_base y y' hy0 h (2 * k + 1)
  · have hyn : y ≤ (0 : Q') := q_le_of_not_le hy0
    by_cases hy'0 : (0 : Q') ≤ y'
    · -- `y ≤ 0 ≤ y'`.
      exact Q'.le_trans' _ _ _ (odd_pow_nonpos y hyn k) (pow_nonneg y' hy'0 (2 * k + 1))
    · -- `y ≤ 0`, `y' ≤ 0`.  Reduce to `pow_le_pow_base` on `-y' ≤ -y` and flip.
      have hy'n : y' ≤ (0 : Q') := q_le_of_not_le hy'0
      have h1 : -y' ≤ -y := Q'.neg_le_neg h
      have h0negy' : (0 : Q') ≤ -y' :=
        Q'.le_trans' 0 (-(0 : Q')) (-y') (by decide) (Q'.neg_le_neg hy'n)
      have hpow : (-y') ^ (2 * k + 1) ≤ (-y) ^ (2 * k + 1) :=
        pow_le_pow_base (-y') (-y) h0negy' h1 (2 * k + 1)
      -- rewrite both ends by L1: `-(y'^o) ≤ -(y^o)`.
      have hL : (-(y' ^ (2 * k + 1))) ≤ (-(y ^ (2 * k + 1))) :=
        Q'.le_trans' _ _ _ (Q'.ge_of_eqv (neg_pow_odd_eqv y' k))
          (Q'.le_trans' _ _ _ hpow (Q'.le_of_eqv (neg_pow_odd_eqv y k)))
      -- flip: `y^o ≤ y'^o`.
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv (y ^ (2 * k + 1))))
        (Q'.le_trans' _ _ _ (Q'.neg_le_neg hL)
          (Q'.le_of_eqv (Q'.neg_neg_eqv (y' ^ (2 * k + 1)))))

/-- **L3.**  Each signed term `y^{2k+1}·recipOdd k` is monotone in `y`. -/
theorem term_mono_arg (y y' : Q') (k : Nat) (h : y ≤ y') : term y k ≤ term y' k := by
  show y ^ (2 * k + 1) * recipOdd k ≤ y' ^ (2 * k + 1) * recipOdd k
  exact Q'.mul_le_mul_of_nonneg_right _ _ (recipOdd k) (oddPow_mono y y' k h) (recipOdd_nonneg k)

/-- **L4.**  Every partial sum is monotone in the argument. -/
theorem partialSum_mono_arg (y y' : Q') (h : y ≤ y') :
    ∀ n : Nat, partialSum y n ≤ partialSum y' n
  | 0 => Q'.le_refl' _
  | n + 1 => by
    show partialSum y n + term y n ≤ partialSum y' n + term y' n
    exact Q'.add_le_add (partialSum_mono_arg y y' h n) (term_mono_arg y y' n h)

/-- **L5 (discharge of `ArtanhMonotoneWindow`).**  The pointwise `≤` of partial
sums gives `leEv` directly. -/
theorem artanh_mono_window (y y' : Q')
    (hy : Q'.abs y ≤ recipOdd 1) (hy' : Q'.abs y' ≤ recipOdd 1) (h : y ≤ y') :
    CReal.leEv (artanh y hy) (artanh y' hy') := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  show partialSum y n ≤ partialSum y' n + ε
  exact Q'.le_trans' _ _ _ (partialSum_mono_arg y y' h n)
    (Q'.add_le_self_of_nonneg (partialSum y' n) ε (Q'.le_of_lt hε))

/-! ## (a) `YOfMonotone` — reciprocal-antitone route -/

/-- **Y1.**  The positive-rational reciprocal is antitone: `p ≤ q ⟹ 1/q ≤ 1/p`.
Cross-product identity via `recipPos_num` / `recipPos_den`. -/
theorem recipPos_antitone (p q : Q') (hp : (0 : Q') < p) (hq : (0 : Q') < q)
    (h : p ≤ q) : Q'.recipPos q hq ≤ Q'.recipPos p hp := by
  show (Q'.recipPos q hq).num * ((Q'.recipPos p hp).den : Int)
      ≤ (Q'.recipPos p hp).num * ((Q'.recipPos q hq).den : Int)
  rw [Q'.recipPos_num q hq, Q'.recipPos_num p hp, Q'.recipPos_den p hp, Q'.recipPos_den q hq]
  -- goal: `q.den * p.num ≤ p.den * q.num`, i.e. `h` up to `Int.mul_comm`.
  have hh : p.num * (q.den : Int) ≤ q.num * (p.den : Int) := h
  rw [Int.mul_comm (q.den : Int) p.num, Int.mul_comm (p.den : Int) q.num]
  exact hh

/-- **Y2.**  The affine form of the artanh argument:
`yOf m = (m−1)/(m+1) ≃ 1 + (−2)·recipPos(m+1)`. -/
theorem yOf_eqv_one_sub (m : Q') (hm1 : (0 : Q') < m + 1) :
    (yOf m hm1).eqv (1 + (-(2 : Q')) * Q'.recipPos (m + 1) hm1) := by
  show ((m + -1) * Q'.recipPos (m + 1) hm1).eqv
      (1 + (-(2 : Q')) * Q'.recipPos (m + 1) hm1)
  -- `m + -1 ≃ (m+1) + -2`.
  have hnum : (m + -1).eqv ((m + 1) + (-(2 : Q'))) := by
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv m 1 (-(2 : Q'))) ?_)
    exact Q'.add_eqv_congr_left m (1 + (-(2 : Q'))) (-1) (by decide)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (m + -1) ((m + 1) + (-(2 : Q')))
      (Q'.recipPos (m + 1) hm1) hnum) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv (m + 1) (-(2 : Q')) (Q'.recipPos (m + 1) hm1)) ?_
  exact Q'.add_eqv_congr_right ((m + 1) * Q'.recipPos (m + 1) hm1) 1
    ((-(2 : Q')) * Q'.recipPos (m + 1) hm1) (Q'.mul_recipPos_eqv (m + 1) hm1)

/-- **Y3 (discharge of `YOfMonotone`).**  `a ≤ b ⟹ yOf a ≤ yOf b`. -/
theorem yOf_mono (a b : Q') (ha : (0 : Q') < a + 1) (hb : (0 : Q') < b + 1)
    (hab : a ≤ b) : yOf a ha ≤ yOf b hb := by
  have hab1 : a + 1 ≤ b + 1 := Q'.add_le_add_right a b 1 hab
  have hrec : Q'.recipPos (b + 1) hb ≤ Q'.recipPos (a + 1) ha :=
    recipPos_antitone (a + 1) (b + 1) ha hb hab1
  -- `2·recipPos(b+1) ≤ 2·recipPos(a+1)`.
  have h2 : (2 : Q') * Q'.recipPos (b + 1) hb ≤ (2 : Q') * Q'.recipPos (a + 1) ha :=
    Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q') hrec (by decide)
  -- negate: `-(2·recipPos(a+1)) ≤ -(2·recipPos(b+1))`.
  have h3 : -((2 : Q') * Q'.recipPos (a + 1) ha) ≤ -((2 : Q') * Q'.recipPos (b + 1) hb) :=
    Q'.neg_le_neg h2
  -- pull the sign in: `(-2)·recipPos(a+1) ≤ (-2)·recipPos(b+1)`.
  have h4 : (-(2 : Q')) * Q'.recipPos (a + 1) ha ≤ (-(2 : Q')) * Q'.recipPos (b + 1) hb :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_mul_eqv (2 : Q') (Q'.recipPos (a + 1) ha)))
      (Q'.le_trans' _ _ _ h3
        (Q'.ge_of_eqv (Q'.neg_mul_eqv (2 : Q') (Q'.recipPos (b + 1) hb))))
  have h5 : 1 + (-(2 : Q')) * Q'.recipPos (a + 1) ha
      ≤ 1 + (-(2 : Q')) * Q'.recipPos (b + 1) hb :=
    Q'.add_le_add_left 1 _ _ h4
  -- transport across the affine form.
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (yOf_eqv_one_sub a ha))
    (Q'.le_trans' _ _ _ h5 (Q'.ge_of_eqv (yOf_eqv_one_sub b hb)))

/-! ## Packaging into the named residual structures -/

/-- **Discharge.**  The `YOfMonotone` residual, constructed. -/
def yOfMonotone : HamiltonianSpectrumInf.YOfMonotone where
  mono := yOf_mono

/-- **Discharge.**  The `ArtanhMonotoneWindow` residual, constructed. -/
def artanhMonotoneWindow : HamiltonianSpectrumInf.ArtanhMonotoneWindow where
  mono := artanh_mono_window

end YMGap.Continuum.ArtanhMonotone

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ArtanhMonotone.neg_pow_odd_eqv
#print axioms YMGap.Continuum.ArtanhMonotone.oddPow_mono
#print axioms YMGap.Continuum.ArtanhMonotone.term_mono_arg
#print axioms YMGap.Continuum.ArtanhMonotone.partialSum_mono_arg
#print axioms YMGap.Continuum.ArtanhMonotone.artanh_mono_window
#print axioms YMGap.Continuum.ArtanhMonotone.recipPos_antitone
#print axioms YMGap.Continuum.ArtanhMonotone.yOf_eqv_one_sub
#print axioms YMGap.Continuum.ArtanhMonotone.yOf_mono
#print axioms YMGap.Continuum.ArtanhMonotone.yOfMonotone
#print axioms YMGap.Continuum.ArtanhMonotone.artanhMonotoneWindow
