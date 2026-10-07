/-
# Square-box doubling iteration algebra (C1 Milestone 2, REDUCTION)

Companion to `audits/SCOPE-C1-SQUARE-BOX-DOUBLING-2026-10-06.md` §5 (Milestone 2).
ADDITIVE, pure `Q'` algebra.

Write `g k = 1 − r(2^k L₀)` for the vacuum-sector gap of the box at doubling
level `k`.  The (OPEN) doubling inequality of the scope note is
`1 − r(2L) ≥ (1 − r(L)) · (1 − ε_L)`, one doubling being four slab doublings.

* `prodLoss ε k = Π_{i<k} (1 − ε i)`, `sumLoss ε k = Σ_{i<k} ε i`.
* `doubling_iterate`: per-step `g k·(1−ε k) ≤ g (k+1)` and `ε k ≤ 1` give
  `g 0 · prodLoss ε k ≤ g k` for every `k`.
* `slab_doubling_iterate`: the same along a slab-indexed sequence, read at
  level `4k` (four slab doublings per box doubling).
* `prodLoss_ge_one_sub_sumLoss` (Bernoulli/Weierstrass): `0 ≤ ε i ≤ 1` give
  `1 − Σ_{i<k} ε i ≤ Π_{i<k} (1 − ε i)`.
* `doubling_uniform_gap`: if additionally every partial sum is `≤ σ` and
  `0 ≤ g 0`, then `g 0 · (1 − σ) ≤ g k` for all `k` (a scale-uniform gap
  when `σ < 1`).

**REDUCTION.** The doubling inequality and summability of `ε` are OPEN
hypotheses; nothing here is proved about any Yang–Mills transfer matrix.
Choice-free; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.SquareBoxDoublingIteration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

/-- `Π_{i<k} (1 − ε i)`. -/
def prodLoss (ε : Nat → Q') : Nat → Q'
  | 0 => 1
  | k + 1 => prodLoss ε k * ((1 : Q') + -ε k)

/-- `Σ_{i<k} ε i`. -/
def sumLoss (ε : Nat → Q') : Nat → Q'
  | 0 => 0
  | k + 1 => sumLoss ε k + ε k

theorem one_sub_nonneg {e : Q'} (h : e ≤ 1) : (0 : Q') ≤ (1 : Q') + -e := by
  have h1 := Q'.add_le_add_right e 1 (-e) h
  have e1 : ((0 : Q')).eqv
          (e + -e) :=
    poly_identity_of_normal_eq (.const 0) (.add (.var 0) (.neg (.var 0)))
      (by decide) (fun _ => e)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) h1

theorem one_sub_le_one {e : Q'} (h : (0 : Q') ≤ e) : (1 : Q') + -e ≤ 1 := by
  have h1 := Q'.add_le_add_left ((1 : Q') + -e) 0 e h
  have e1 : ((1 : Q') + -e).eqv
          (((1 : Q') + -e) + 0) :=
    poly_identity_of_normal_eq (.add (.const 1) (.neg (.var 0)))
      (.add (.add (.const 1) (.neg (.var 0))) (.const 0)) (by decide) (fun _ => e)
  have e2 : (((1 : Q') + -e) + e).eqv
          (1) :=
    poly_identity_of_normal_eq (.add (.add (.const 1) (.neg (.var 0))) (.var 0))
      (.const 1) (by decide) (fun _ => e)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e2))

theorem prodLoss_nonneg (ε : Nat → Q') (h1 : ∀ k, ε k ≤ 1) :
    ∀ k, (0 : Q') ≤ prodLoss ε k
  | 0 => by show (0 : Q') ≤ (1 : Q'); decide
  | k + 1 => Q'.mul_nonneg _ _ (prodLoss_nonneg ε h1 k) (one_sub_nonneg (h1 k))

theorem prodLoss_le_one (ε : Nat → Q') (h0 : ∀ k, (0 : Q') ≤ ε k) (h1 : ∀ k, ε k ≤ 1) :
    ∀ k, prodLoss ε k ≤ 1
  | 0 => by show (1 : Q') ≤ (1 : Q'); decide
  | k + 1 => by
      show prodLoss ε k * ((1 : Q') + -ε k) ≤ 1
      have hP := prodLoss_nonneg ε h1 k
      have ha := Q'.mul_le_mul_of_nonneg_left _ _ (prodLoss ε k) (one_sub_le_one (h0 k)) hP
      have e1 : (prodLoss ε k * 1).eqv
          (prodLoss ε k) :=
        poly_identity_of_normal_eq (.mul (.var 0) (.const 1)) (.var 0) (by decide)
          (fun _ => prodLoss ε k)
      exact Q'.le_trans' _ _ _ ha
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (prodLoss_le_one ε h0 h1 k))

/-- **Doubling iteration.** If each doubling loses at most a factor `1 − ε k`
of the gap, then after `k` doublings the gap is at least `g 0 · Π (1 − ε i)`. -/
theorem doubling_iterate (g ε : Nat → Q') (h1 : ∀ k, ε k ≤ 1)
    (hstep : ∀ k, g k * ((1 : Q') + -ε k) ≤ g (k + 1)) :
    ∀ k, g 0 * prodLoss ε k ≤ g k
  | 0 => by
      show g 0 * 1 ≤ g 0
      exact Q'.le_of_eqv (poly_identity_of_normal_eq (.mul (.var 0) (.const 1)) (.var 0)
        (by decide) (fun _ => g 0))
  | k + 1 => by
      show g 0 * (prodLoss ε k * ((1 : Q') + -ε k)) ≤ g (k + 1)
      have ih := doubling_iterate g ε h1 hstep k
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ ((1 : Q') + -ε k) ih (one_sub_nonneg (h1 k))
      have e1 : (g 0 * (prodLoss ε k * ((1 : Q') + -ε k))).eqv
          ((g 0 * prodLoss ε k) * ((1 : Q') + -ε k)) :=
        poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.mul (.var 0) (.var 1)) (.var 2)) (by decide)
          (fun | 0 => g 0 | 1 => prodLoss ε k | _ => (1 : Q') + -ε k)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ hm (hstep k))

/-- **Four slab doublings per box doubling.** Along a slab-indexed gap sequence
`gs` (box doubling `k` = slab steps `4k, …, 4k+3`), per-slab losses `δ` give the
box-level bound at slab index `4k`. -/
theorem slab_doubling_iterate (gs δ : Nat → Q') (h1 : ∀ s, δ s ≤ 1)
    (hslab : ∀ s, gs s * ((1 : Q') + -δ s) ≤ gs (s + 1)) (k : Nat) :
    gs 0 * prodLoss δ (4 * k) ≤ gs (4 * k) :=
  doubling_iterate gs δ h1 hslab (4 * k)

/-- **Bernoulli product bound** `1 − Σ ε ≤ Π (1 − ε)` for `0 ≤ ε i ≤ 1`. -/
theorem prodLoss_ge_one_sub_sumLoss (ε : Nat → Q') (h0 : ∀ k, (0 : Q') ≤ ε k)
    (h1 : ∀ k, ε k ≤ 1) : ∀ k, (1 : Q') + -sumLoss ε k ≤ prodLoss ε k
  | 0 => by
      show (1 : Q') + -(0 : Q') ≤ (1 : Q'); decide
  | k + 1 => by
      show (1 : Q') + -(sumLoss ε k + ε k) ≤ prodLoss ε k * ((1 : Q') + -ε k)
      have ih := prodLoss_ge_one_sub_sumLoss ε h0 h1 k
      -- P·e ≤ e
      have hPe := Q'.mul_le_mul_of_nonneg_right _ _ (ε k) (prodLoss_le_one ε h0 h1 k) (h0 k)
      have e1 : ((1 : Q') * ε k).eqv
          (ε k) :=
        poly_identity_of_normal_eq (.mul (.const 1) (.var 0)) (.var 0) (by decide)
          (fun _ => ε k)
      have hPe' := Q'.le_trans' _ _ _ hPe (Q'.le_of_eqv e1)
      have hA := Q'.add_le_add_right _ _ (-(ε k)) ih
      -- (1 + -S) + -e ≤ P + -e
      have eL : ((1 : Q') + -(sumLoss ε k + ε k)).eqv (((1 : Q') + -sumLoss ε k) + -(ε k)) :=
        poly_identity_of_normal_eq
          (.add (.const 1) (.neg (.add (.var 0) (.var 1))))
          (.add (.add (.const 1) (.neg (.var 0))) (.neg (.var 1))) (by decide)
          (fun | 0 => sumLoss ε k | _ => ε k)
      -- direct route: P + -e ≤ P + -(P e) since P e ≤ e
      have hD : prodLoss ε k + -(ε k) ≤ prodLoss ε k + -(prodLoss ε k * ε k) :=
        Q'.add_le_add_left _ _ _ (Q'.neg_le_neg hPe')
      have eR : (prodLoss ε k + -(prodLoss ε k * ε k)).eqv
          (prodLoss ε k * ((1 : Q') + -ε k)) :=
        poly_identity_of_normal_eq
          (.add (.var 0) (.neg (.mul (.var 0) (.var 1))))
          (.mul (.var 0) (.add (.const 1) (.neg (.var 1)))) (by decide)
          (fun | 0 => prodLoss ε k | _ => ε k)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL)
        (Q'.le_trans' _ _ _ hA (Q'.le_trans' _ _ _ hD (Q'.le_of_eqv eR)))

/-- **Uniform gap under summable losses.** With `0 ≤ ε ≤ 1`, every partial sum
`Σ_{i<k} ε i ≤ σ`, and `0 ≤ g 0`, the gap obeys `g 0 · (1 − σ) ≤ g k` at every
doubling level (scale-uniform and positive when `0 < g 0`, `σ < 1`). -/
theorem doubling_uniform_gap (g ε : Nat → Q') (σ : Q') (hg0 : (0 : Q') ≤ g 0)
    (h0 : ∀ k, (0 : Q') ≤ ε k) (h1 : ∀ k, ε k ≤ 1)
    (hsum : ∀ k, sumLoss ε k ≤ σ)
    (hstep : ∀ k, g k * ((1 : Q') + -ε k) ≤ g (k + 1)) (k : Nat) :
    g 0 * ((1 : Q') + -σ) ≤ g k := by
  have hs : (1 : Q') + -σ ≤ (1 : Q') + -sumLoss ε k :=
    Q'.add_le_add_left _ _ _ (Q'.neg_le_neg (hsum k))
  have hp := Q'.le_trans' _ _ _ hs (prodLoss_ge_one_sub_sumLoss ε h0 h1 k)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (g 0) hp hg0)
    (doubling_iterate g ε h1 hstep k)

end YMGap.Continuum.SquareBoxDoublingIteration
