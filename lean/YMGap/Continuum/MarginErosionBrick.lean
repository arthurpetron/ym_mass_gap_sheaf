/-
`MarginErosionBrick` — Milestone 14.3 OPENED: the abstract brick that
turns the 14.2 corridor into the `recursion` field's multiplicative form.

# The brick

`SingleStepDefectBoundLoose.recursion` demands
`(1 − realδ k)·trueMargin k ≤ trueMargin (k+1)`.  The 14.2 ratio sandwich
(`FusedEnvelope`) delivers ADDITIVE eigenvalue control: the blocked
normalized eigenvalue proxy `λ'` exceeds the free `λ` by at most an
explicit corridor width `ε` (of `intAmp·w⁶` type).  This module proves
the conversion, purely in `Q'`:

    m ≃ 1 − λ,   m' ≃ 1 − λ',   λ' ≤ λ + ε,   ε ≤ δ·m
    ─────────────────────────────────────────────────
                (1 − δ)·m  ≤  m'

— i.e. an additive eigenvalue corridor of width `ε` erodes the margin by
at most the multiplicative factor `(1 − δ)` as soon as `ε ≤ δ·m`.  The
remaining 14.3 content is therefore sharply localized: identify `λ, λ'`
with the per-scale normalized transfer data, and prove the WIDTH-VS-
MARGIN comparison `ε_k ≤ δ_k·m_k` at the anchor scale (the `9·w³`-type
relative width of `FusedEnvelope` against the anchor margin — the
strong-coupling side, reality-fact one, where the corridor is tight).

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusedEnvelope

namespace YMGap.Continuum.MarginErosionBrick

open YMGap.Constructive

/-- **`margin_recursion_of_corridor` (PROVED — the 14.3 conversion
brick).**  If the margins are `m ≃ 1 − λ`, `m' ≃ 1 − λ'`, the blocked
eigenvalue proxy sits in an additive corridor `λ' ≤ λ + ε`, and the
corridor width is dominated by the margin, `ε ≤ δ·m`, then the margin
recursion holds in the consumer's multiplicative form:
`(1 − δ)·m ≤ m'`. -/
theorem margin_recursion_of_corridor {lam lam' eps del m m' : Q'}
    (hm : m.eqv ((1 : Q') + -lam))
    (hm' : ((1 : Q') + -lam').eqv m')
    (hcorr : lam' ≤ lam + eps)
    (habs : eps ≤ del * m) :
    ((1 : Q') - del) * m ≤ m' := by
  -- Step 0: `(1 − δ)·m ≤ m + −(δ·m) ≤ m + −ε`
  have hX : ((1 : Q') - del) * m ≤ m + -eps := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.sub_mul_eqv 1 del m)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _
        (Q'.one_mul_eqv m))) ?_
    exact Q'.add_le_add_left m _ _ (Q'.neg_le_neg habs)
  -- Step 1: `(m + −ε) + λ' ≤ 1`
  have hA : (m + -eps) + lam' ≤ (1 : Q') := by
    -- `(m + −ε) + λ' ≤ (m + −ε) + (λ + ε)`
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (m + -eps) _ _ hcorr) ?_
    -- `(m + −ε) + (λ + ε) ≃ m + λ`
    have hregroup : ((m + -eps) + (lam + eps)).eqv (m + lam) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv m (-eps) (lam + eps)) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      -- `−ε + (λ + ε) ≃ λ`
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv lam eps)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (-eps) eps lam)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.neg_add_self_eqv eps)) ?_
      rw [Q'.zero_add']
      exact Q'.eqv_refl _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) ?_
    -- `m + λ ≃ (1 + −λ) + λ ≃ 1`
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hm) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv 1 (-lam) lam) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv lam)) ?_
    rw [Q'.add_zero']
    exact Q'.eqv_refl _
  -- Step 2: cancel `λ'` on the right: `m + −ε ≤ 1 + −λ' ≃ m'`
  have hcancel : ((m + -eps) + lam') + -lam' ≤ (1 : Q') + -lam' :=
    Q'.add_le_add_right _ _ _ hA
  have hLHS : (((m + -eps) + lam') + -lam').eqv (m + -eps) := by
    have hzero : ((lam' : Q') + -lam').eqv 0 :=
      Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv lam' (-lam')) (Q'.neg_add_self_eqv lam')
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (m + -eps) lam' (-lam')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (m + -eps) _ _ hzero) ?_
    rw [Q'.add_zero']
    exact Q'.eqv_refl _
  refine Q'.le_trans' _ _ _ hX ?_
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hLHS) ?_
  exact Q'.le_trans' _ _ _ hcancel (Q'.le_of_eqv hm')

end YMGap.Continuum.MarginErosionBrick

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms
  YMGap.Continuum.MarginErosionBrick.margin_recursion_of_corridor
