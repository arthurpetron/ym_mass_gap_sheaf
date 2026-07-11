/-
`FusedEnvelope` — Milestone 14.2, second half: the CORRECT normalized
comparison, built division-free after `IntAmpAnchors.naive_ratio_mismatch`
machine-refuted the raw channel/vacuum ratio.

# The object

The transfer-relevant quantity is the NORMALIZED blocked coefficient —
channel over vacuum.  `naive_ratio_mismatch` proved the raw ratio is the
wrong defect object (it misses the free ratio by `O(1)` at `w = 1`), so
the comparison is phrased CROSS-MULTIPLIED (no division in `Q'`), with
the vacuum renormalization carried explicitly:

  * vacuum split (`boxSum_vacuum_split`):
      `boxSum w N 0 ≃ 1 + intBlock w N 0`
    — the single pair `(0,0)` is the free vacuum (`0 ⊗ 0 ∋ 0` only), and
    every other contributing pair has BOTH spins `≥ 1`;
  * the ENVELOPE: for `1 ≤ s ≤ N`, `w ∈ [0, 1]`,
      `2·c_s ≤ boxSum w N s ≤ 2·c_s + intAmp N s·w⁶`
      `1 ≤ boxSum w N 0 ≤ 1 + intAmp N 0·w⁶`
  * the division-free RATIO SANDWICH (the headline):
      `2·c_s · boxSum(0) ≤ boxSum(s) · (1 + intAmp N 0·w⁶)`
      `boxSum(s) ≤ (2·c_s + intAmp N s·w⁶) · boxSum(0)`
    — read: the normalized blocked channel lies within an
    `intAmp·w⁶`-wide corridor around the free `2·c_s`.

# Where the corridor closes (the honest window)

The corridor is RELATIVELY small exactly where `intAmp·w⁶ ≪ c_s ~ w^{C₄(s)}`
— the STRONG-COUPLING side (small `w`), i.e. the anchor regime of
`singleStep` (reality-fact one, COMPACTNESS, of the measurement-model
map).  Channel `s = 1`: relative width `≤ (intAmp/2·dimQ 1)·w³ = 9·w³` at
`N = 3`.  Near `w = 1` the corridor is `O(1)` (that is precisely the
refuted naive regime): the per-step defect budget must be consumed at the
anchor side and propagated by the recursion (14.3), NOT evaluated at the
continuum end.

# What remains open (AGENTS.md Rule 6)

14.3: feeding the corridor into the gap-stability recursion (the
`(1−δ)·m` margin arithmetic against the `9·w³`-type relative width at the
anchor scale).  No frontier type is touched; the Clay problem stays OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusedFreeSplit

namespace YMGap.Continuum.FusedEnvelope

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.FusedChannelOne
open YMGap.Continuum.FusedChannelAll
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.TaylorModel

/-! ## 1. The vacuum split: `boxSum w N 0 ≃ 1 + intBlock w N 0` -/

/-- **`boxSum_vacuum_split` (PROVED).**  The blocked vacuum splits
exactly: the pair `(0,0)` contributes the free `1` (`0 ⊗ 0 ∋ 0` pins both
deltas), all `b = 0` heads of the `a ≥ 1` rows vanish (`a ⊗ 0 ∋ 0` forces
`a = 0`), and the remainder is the interacting block at `s = 0`. -/
theorem boxSum_vacuum_split (w : Q') (N : Nat) :
    (boxSum w N 0).eqv ((1 : Q') + intBlock w N 0) := by
  -- the a = 0 row is a delta row at b = 0
  have hrow0 : ∀ b, (fusionInd 0 b 0 * (coeffW w 0 * coeffW w b)).eqv
      ((if b = 0 then (1 : Q') else 0) * coeffW w b) := by
    intro b
    rw [fusionInd_zero_left b 0, coeffW_zero]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv (coeffW w b))
  unfold boxSum
  -- peel the a = 0 row
  refine Q'.eqv_trans _ _ _
    (fsum_peel (fun a => fsum (fun b =>
      fusionInd a b 0 * (coeffW w a * coeffW w b)) (N + 1)) N) ?_
  refine add_eqv_congr_both' ?_ ?_
  · -- Σ_b δ_{b,0}·c_b ≃ c_0 = 1
    refine Q'.eqv_trans _ _ _ (fsum_eqv_congr' hrow0 (N + 1)) ?_
    refine Q'.eqv_trans _ _ _
      (delta_fsum (fun b => coeffW w b) 0 (N + 1) (by omega)) ?_
    show (coeffW w 0).eqv 1
    rw [coeffW_zero]
    exact Q'.eqv_refl _
  · -- a ≥ 1 rows: the b = 0 heads vanish; the remainder is intBlock
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr' (fun a =>
        fsum_peel (fun b =>
          fusionInd (a + 1) b 0 * (coeffW w (a + 1) * coeffW w b)) N)
        N) ?_
    refine Q'.eqv_trans _ _ _
      (fsum_add' (fun a =>
        fusionInd (a + 1) 0 0 * (coeffW w (a + 1) * coeffW w 0))
        (fun a => fsum (fun b =>
          fusionInd (a + 1) (b + 1) 0
            * (coeffW w (a + 1) * coeffW w (b + 1))) N) N) ?_
    have hheads : (fsum (fun a =>
        fusionInd (a + 1) 0 0 * (coeffW w (a + 1) * coeffW w 0)) N).eqv
        0 := by
      refine fsum_zero_of_bounded N (fun a _ => ?_)
      show (fusionInd (a + 1) 0 0
        * (coeffW w (a + 1) * coeffW w 0)).eqv 0
      rw [fusionInd_zero_right (a + 1) 0,
        if_neg (by omega : ¬ a + 1 = 0)]
      exact Q'.zero_mul_eqv _
    refine Q'.eqv_trans _ _ _
      (add_eqv_congr_both' hheads (Q'.eqv_refl _)) ?_
    rw [Q'.zero_add']
    exact Q'.eqv_refl _

/-! ## 2. Nonnegativity of the interacting objects -/

/-- The interacting block is nonnegative on `w ≥ 0`. -/
theorem intBlock_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N s : Nat) :
    (0 : Q') ≤ intBlock w N s := by
  unfold intBlock
  exact fsum_nonneg (fun a => fsum_nonneg (fun b =>
    Q'.mul_nonneg _ _ (fusionInd_nonneg _ _ _)
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _)))
    N) N

/-- The derived interacting amplitude is nonnegative. -/
theorem intAmp_nonneg (N s : Nat) : (0 : Q') ≤ intAmp N s := by
  unfold intAmp
  exact fsum_nonneg (fun a => fsum_nonneg (fun b =>
    Q'.mul_nonneg _ _ (fusionInd_nonneg _ _ _)
      (Q'.mul_nonneg _ _ (dimQ_nonneg _) (dimQ_nonneg _))) N) N

/-! ## 3. The envelope -/

/-- The blocked vacuum is at least the free vacuum: `1 ≤ boxSum w N 0`. -/
theorem vacuum_ge_one {w : Q'} (hw0 : (0 : Q') ≤ w) (N : Nat) :
    (1 : Q') ≤ boxSum w N 0 := by
  refine Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg 1 (intBlock w N 0)
      (intBlock_nonneg hw0 N 0)) ?_
  exact Q'.ge_of_eqv (boxSum_vacuum_split w N)

/-- The blocked vacuum exceeds the free vacuum by at most
`intAmp N 0 · w⁶`. -/
theorem vacuum_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) :
    boxSum w N 0 ≤ (1 : Q') + intAmp N 0 * qpow w 6 := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (boxSum_vacuum_split w N)) ?_
  exact Q'.add_le_add_left 1 _ _ (intBlock_le hw0 hw1 N 0)

/-- The blocked channel is at least its free part: `2·c_s ≤ boxSum`. -/
theorem boxSum_ge_free {w : Q'} (hw0 : (0 : Q') ≤ w) {N s : Nat}
    (hs1 : 1 ≤ s) (hsN : s ≤ N) :
    coeffW w s + coeffW w s ≤ boxSum w N s := by
  refine Q'.le_trans' _ _ _ ?_
    (Q'.ge_of_eqv (boxSum_free_split w hs1 hsN))
  exact Q'.add_le_add_left _ _ _
    (Q'.add_le_self_of_nonneg _ _ (intBlock_nonneg hw0 N s))

/-- The blocked channel exceeds its free part by at most
`intAmp N s · w⁶`. -/
theorem boxSum_le_free_plus {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) {N s : Nat} (hs1 : 1 ≤ s) (hsN : s ≤ N) :
    boxSum w N s
      ≤ coeffW w s + (coeffW w s + intAmp N s * qpow w 6) := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (boxSum_free_split w hs1 hsN)) ?_
  exact Q'.add_le_add_left _ _ _
    (Q'.add_le_add_left _ _ _ (intBlock_le hw0 hw1 N s))

/-! ## 4. THE DIVISION-FREE RATIO SANDWICH (the headline) -/

/-- **`boxSum_ratio_upper` (PROVED).**  Cross-multiplied upper half of
the normalized comparison: the blocked channel is at most the corridor
ceiling times the blocked vacuum,

    boxSum(s) ≤ (2·c_s + intAmp N s·w⁶) · boxSum(0).

(Reads as: channel/vacuum ≤ 2·c_s + intAmp·w⁶ — the vacuum
renormalization can only HELP the upper bound since `boxSum(0) ≥ 1`.) -/
theorem boxSum_ratio_upper {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) {N s : Nat} (hs1 : 1 ≤ s) (hsN : s ≤ N) :
    boxSum w N s
      ≤ (coeffW w s + (coeffW w s + intAmp N s * qpow w 6))
          * boxSum w N 0 := by
  have hB : (0 : Q')
      ≤ coeffW w s + (coeffW w s + intAmp N s * qpow w 6) :=
    Q'.zero_le_add _ _ (coeffW_nonneg hw0 s)
      (Q'.zero_le_add _ _ (coeffW_nonneg hw0 s)
        (Q'.mul_nonneg _ _ (intAmp_nonneg N s) (qpow_nonneg w hw0 6)))
  refine Q'.le_trans' _ _ _ (boxSum_le_free_plus hw0 hw1 hs1 hsN) ?_
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_one_eqv
      (coeffW w s + (coeffW w s + intAmp N s * qpow w 6)))) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ (vacuum_ge_one hw0 N) hB

/-- **`boxSum_ratio_lower` (PROVED).**  Cross-multiplied lower half:

    2·c_s · boxSum(0) ≤ boxSum(s) · (1 + intAmp N 0·w⁶).

(Reads as: channel/vacuum ≥ 2·c_s / (1 + intAmp N 0·w⁶) — the free part
survives up to the vacuum's own `w⁶` renormalization.) -/
theorem boxSum_ratio_lower {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) {N s : Nat} (hs1 : 1 ≤ s) (hsN : s ≤ N) :
    (coeffW w s + coeffW w s) * boxSum w N 0
      ≤ boxSum w N s * ((1 : Q') + intAmp N 0 * qpow w 6) := by
  have hfree : (0 : Q') ≤ coeffW w s + coeffW w s :=
    Q'.zero_le_add _ _ (coeffW_nonneg hw0 s) (coeffW_nonneg hw0 s)
  have hvac : (0 : Q') ≤ (1 : Q') + intAmp N 0 * qpow w 6 :=
    Q'.zero_le_add _ _ (by decide)
      (Q'.mul_nonneg _ _ (intAmp_nonneg N 0) (qpow_nonneg w hw0 6))
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (vacuum_le hw0 hw1 N) hfree) ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (boxSum_ge_free hw0 hs1 hsN) hvac

end YMGap.Continuum.FusedEnvelope

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusedEnvelope.boxSum_vacuum_split
#print axioms YMGap.Continuum.FusedEnvelope.intBlock_nonneg
#print axioms YMGap.Continuum.FusedEnvelope.intAmp_nonneg
#print axioms YMGap.Continuum.FusedEnvelope.vacuum_ge_one
#print axioms YMGap.Continuum.FusedEnvelope.vacuum_le
#print axioms YMGap.Continuum.FusedEnvelope.boxSum_ge_free
#print axioms YMGap.Continuum.FusedEnvelope.boxSum_le_free_plus
#print axioms YMGap.Continuum.FusedEnvelope.boxSum_ratio_upper
#print axioms YMGap.Continuum.FusedEnvelope.boxSum_ratio_lower
