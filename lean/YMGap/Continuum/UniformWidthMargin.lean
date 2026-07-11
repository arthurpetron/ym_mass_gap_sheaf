/-
`UniformWidthMargin` — Milestone 14.3, the k-uniform front OPENED with a
window theorem and an ADJUDICATION: the width-vs-margin comparison holds
UNIFORMLY on the strong-coupling window `w ∈ [0, 1/2]` (a theorem in `w`,
not a point check), and the naive same-scale margin proxy is
machine-REFUTED on the AF flow's weak-coupling tail — pinning the
remaining identification to the per-scale RESCALING.

# The window theorem (identification (ii), uniform)

For all `w ∈ [0, 1/2]`, with `δ(w) := 41·w³`:

    intAmp 3 1 · w⁶  ≤  (41·w³) · (1 − 2·coeffW w 1)

(i.e. `36·w⁶ ≤ 41·w³·(1 − 4·w³)`; on the window `w³ ≤ 1/8` so LHS
`≤ (9/2)·w³` while RHS `≥ (41/2)·w³`).  Combined with `lamB_corridor`
and the conversion brick this gives the margin recursion at EVERY scale
whose weight lies in the window — with `δ_k = 41·w_k³` geometrically
summable wherever the flow's weights decay.

# THE ADJUDICATION: the same-scale proxy dies at weak coupling

`AFRateModulus` drives `w_k → 1` (`1 − w_k ≤ A/(k+B)`).  At `w = 9/10`
the naive same-scale margin proxy is NEGATIVE (kernel-checked):

    1 − 2·coeffW (9/10) 1  <  0        (4·(9/10)³ = 729/250 > 1),

while `trueMargin_nonneg` demands `≥ 0`.  So the k-uniform inhabitation
of `SingleStepDefectBoundLoose.recursion` CANNOT use `1 − 2·c₁(w_k)` as
`trueMargin k` on the tail: the margin must be the RESCALED, per-scale
dimensionless margin — the blocked operator read in its own
normalization, i.e. the corridor must be wired through the renormalized
weight flow (`renormWFix` layer / `effTransfer` located gaps), where the
free part of scale `k+1` is expressed at the RENORMALIZED weight, not at
`w_k`.  That wiring is the sole remaining 14.3 content.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` core; kernel `decide` on closed rationals only.
Gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusedRatioCorridor
import YMGap.Continuum.IntAmpAnchors

namespace YMGap.Continuum.UniformWidthMargin

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.FusedChannelOne
open YMGap.Continuum.FusedChannelAll
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.FusedEnvelope
open YMGap.Continuum.MarginErosionBrick
open YMGap.Continuum.FusedRatioCorridor
open YMGap.Continuum.IntAmpAnchors

/-- One half. -/
def half : Q' := Q'.mkPos 1 2 (by omega)

/-- One eighth. -/
def eighth : Q' := Q'.mkPos 1 8 (by omega)

/-- On the window, the cube is at most `1/8`. -/
theorem qpow3_le_eighth {w : Q'} (hw0 : (0 : Q') ≤ w) (hwh : w ≤ half) :
    qpow w 3 ≤ eighth :=
  Q'.le_trans' _ _ _ (qpow_mono_base hw0 hwh 3) (by decide)

/-- **`uniform_width_le_margin` (PROVED — identification (ii) as a
THEOREM in `w` on the strong-coupling window).**  For `0 ≤ w ≤ 1/2`,
with erosion rate `δ(w) = 41·w³`:

    intAmp 3 1 · w⁶ ≤ (41·w³) · (1 − 2·coeffW w 1). -/
theorem uniform_width_le_margin {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwh : w ≤ half) :
    intAmp 3 1 * qpow w 6
      ≤ (Q'.ofNat 41 * qpow w 3)
          * ((1 : Q') + -(coeffW w 1 + coeffW w 1)) := by
  have h8 : qpow w 3 ≤ eighth := qpow3_le_eighth hw0 hwh
  have hq3 : (0 : Q') ≤ qpow w 3 := qpow_nonneg w hw0 3
  -- LHS ≤ 36·(w³·w³) ≤ 36·(1/8·w³) ≤ (41·(1/2))·w³
  have hL : intAmp 3 1 * qpow w 6
      ≤ (Q'.ofNat 41 * half) * qpow w 3 := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ intAmp_N3_ch1)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat 36) _ _
        (qpow_add' w 3 3))) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ h8 hq3)
        (by decide : (0 : Q') ≤ Q'.ofNat 36)) ?_
    -- 36·(1/8·w³) ≃ (36·1/8)·w³ ≤ (41·1/2)·w³
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 36) eighth (qpow w 3)))) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (by decide : Q'.ofNat 36 * eighth ≤ Q'.ofNat 41 * half) hq3
  -- the margin is ≥ 1/2 on the window
  have hc : coeffW w 1 + coeffW w 1 ≤ half := by
    have hone : coeffW w 1 ≤ Q'.mkPos 1 4 (by omega) := by
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ h8 (dimQ_nonneg 1)) ?_
      exact by decide
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hone hone) ?_
    exact by decide
  have hm : half ≤ (1 : Q') + -(coeffW w 1 + coeffW w 1) := by
    refine Q'.le_trans' _ _ _
      (by decide : half ≤ (1 : Q') + -half) ?_
    exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hc)
  -- RHS ≥ (41·w³)·(1/2) ≃ (41·1/2)·w³
  have h41 : (0 : Q') ≤ Q'.ofNat 41 * qpow w 3 :=
    Q'.mul_nonneg _ _ (by decide) hq3
  refine Q'.le_trans' _ _ _ hL ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv ?_)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hm h41)
  -- (41·1/2)·w³ ≃ (41·w³)·(1/2)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (Q'.ofNat 41) half (qpow w 3)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 41) _ _
      (Q'.mul_comm_eqv half (qpow w 3))) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 41) (qpow w 3) half)

/-- **`window_recursion` (PROVED — the margin recursion at EVERY scale
in the strong-coupling window).**  For any `w ∈ [0, 1/2]`, one fused
blocking step erodes the naive margin by at most `(1 − 41·w³)`:

    (1 − 41·w³)·(1 − 2·coeffW w 1) ≤ 1 − lamB w 3 1. -/
theorem window_recursion {w : Q'} (hw0 : (0 : Q') ≤ w) (hwh : w ≤ half) :
    ((1 : Q') - Q'.ofNat 41 * qpow w 3)
        * ((1 : Q') + -(coeffW w 1 + coeffW w 1))
      ≤ (1 : Q') + -(lamB w 3 1) :=
  margin_recursion_of_corridor
    (Q'.eqv_refl _) (Q'.eqv_refl _)
    (lamB_corridor hw0
      (Q'.le_trans' _ _ _ hwh (by decide)) (by omega) (by omega : 1 ≤ 3))
    (uniform_width_le_margin hw0 hwh)

/-! ## THE ADJUDICATION: the same-scale proxy dies on the AF tail -/

/-- Nine tenths — a weak-coupling point the AF flow provably enters. -/
def wTail : Q' := Q'.mkPos 9 10 (by omega)

/-- **`naive_margin_negative_at_tail` (kernel-checked REFUTATION).**
At `w = 9/10` the same-scale margin proxy `1 − 2·coeffW w 1` is
NEGATIVE (`4·(9/10)³ = 729/250 > 1`), while `trueMargin_nonneg` demands
nonnegativity.  The k-uniform inhabitation of
`SingleStepDefectBoundLoose.recursion` therefore CANNOT take
`trueMargin k := 1 − 2·c₁(w_k)` on the AF tail: the margin must be read
in the per-scale RESCALED normalization (the renormalized-weight flow),
which is the sole remaining 14.3 identification. -/
theorem naive_margin_negative_at_tail :
    ¬ ((0 : Q') ≤ (1 : Q') + -(coeffW wTail 1 + coeffW wTail 1)) := by
  decide

end YMGap.Continuum.UniformWidthMargin

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.UniformWidthMargin.qpow3_le_eighth
#print axioms YMGap.Continuum.UniformWidthMargin.uniform_width_le_margin
#print axioms YMGap.Continuum.UniformWidthMargin.window_recursion
#print axioms
  YMGap.Continuum.UniformWidthMargin.naive_margin_negative_at_tail
