/-
Track B / R2 — THE SHARP ORDER of the MULTIPLICITY-BLIND bond-moved EIGENVALUE
defect `eigShift` on the bulk: does dividing out the `(s+1)` multiplicity restore
QUADRATICITY (closing `EigenvalueShiftBridge.bondMoved_below_gapEdge`), or is the
eigenvalue defect STILL non-quadratic?

# The question, made precise

`EigenvalueShiftBridge` reduced the bond-moving localization to the single per-mode
bound `eigShift ≤ 1/12` on the bulk, where

    eigShift N p hp w s  =  |bmEig N p w s  −  retEig p hp w s|,
    bmEig   N p w s  =  bondMovedCoeff N w p s / dimQ s,     (the p-fold fusion
                                                              convolution / (s+1))
    retEig  p hp w s =  renormWFix p hp w ^ {C₄(s)}.          (retuned heat kernel)

The PRIOR falsification (`BondMovingRelResidual`, `FusionRelResidualBound`) was for
the MULTIPLICITY-WEIGHTED COEFFICIENT residual `rrelFix` and showed it is LINEAR.
The open hope was that dividing out the `(s+1)` density — passing to the genuine
EIGENVALUE `bmEig = bmc/dimQ` — might restore the quadratic order.  This module
computes the SHARP order of `eigShift` directly.

# THE VERDICT — (b): the mult-blind eigShift is NOT quadratic; it is Θ(1)-or-worse

Dividing out the multiplicity does NOT restore quadraticity.  The reason is precise
and is NOT the multiplicity: the fusion convolution `bondMovedCoeff N w p` carries,
as an OVERALL prefactor, the vacuum L²-mass

    bmc(0) = bondMovedCoeff N w p 0  =  Σ_i (fusion of p copies → trivial)
           ⊇  Σ_i coeffW(i)²  (for p ≥ 2)   ~  (1 − w)^{−3/2}   (heat-kernel L²),

which is the integral `∫ K_w^p` of the bond-moved class function — NOT normalized to
`1` (it is `1` ONLY at `p = 1`).  Because `bmEig = bmc/dimQ s` divides out the
multiplicity `(s+1)` but NOT this vacuum mass, EVERY mode — including the bulk —
inherits the `bmc(0)`-sized prefactor.  The retuned heat-kernel eigenvalue `retEig`
has prefactor `≈ 1`.  So on the bulk

    eigShift  ≈  bmEig − retEig  ≈  (bmc(0)·Θ(1))  −  Θ(1)  =  Θ(1)-or-larger,

NOT `O((1−w)²)` and NOT `≤ 1/12`.  The `1/p` retune `renormWFix = 1 − (1−w)/p`
correctly matches the EXPONENT (the `e^{−C₄(s)(1−w)/p}` Gaussian decay of the
p-fold convolution), but it does NOT — and cannot — fix the missing VACUUM
NORMALIZATION.  Only the vacuum-NORMALIZED eigenvalue `bmc(s)/((s+1)·bmc(0))` has
the right `Θ(1)` size on the bulk — and even THAT one is LINEAR (not quadratic) in
`(1−w)` per mode (the documented `FusionRelResidualBound` linearity).  So the
multiplicity is a RED HERRING for the order: the obstruction is the L²-mass `bmc(0)`.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat`)

  * `eigShift_p1_zero` — the EXACT `p = 1` vanishing `eigShift N 1 _ w s ≃ 0`
    (s ≤ N).  At `p = 1` the unit fusion identity gives `bmEig = w^{C₄(s)}` and
    `renormWFix 1 = w` gives `retEig = w^{C₄(s)}`, so the eigenvalue defect VANISHES
    EXACTLY.  This confirms `eigShift` is a genuine `p ≥ 2` bond-moving effect — NOT
    the `BulkModeCrux.deltaRen` overshoot (which is `Θ(1)` already at `p = 1`).
  * `fsum_two_term_le` — a clean two-summand lower bound for a nonnegative `fsum`
    (the engine that extracts TWO fusion channels at once).
  * `bmc_vacuum_lower` — for every genuine bond-moving exponent `p + 1` (`p ≥ 1`,
    `1 ≤ N`), the SHARP vacuum lower bound
        bondMovedCoeff N w (p+1) 0  ≥  1  +  coeffW w 1²   ( = 1 + 4w⁶ ),
    extracting the identity channel `(0,…,0)` (coefficient `1`) AND the
    first-excited self-fusion channel `(1,1,…)` (coefficient `coeffW w 1²`).  This
    is the vacuum L²-mass EXCESS `bmc(0) − 1 ≥ 4w⁶`, the seed of the obstruction.
  * `eigShift_vacuum_lower` — the SHARP NEGATIVE: for every `p + 1` (`p ≥ 1`),
        eigShift N (p+1) _ w 0  ≥  coeffW w 1²   ( = 4w⁶ ),
    so the mult-blind eigenvalue defect is bounded BELOW by `4w⁶ = Θ(1)` (NOT
    quadratic, NOT `→ 0`).  Since `retEig(0) = 1` (vacuum) but `bmEig(0) = bmc(0)`,
    the defect is exactly the un-divided L²-mass excess.
  * `eigShift_vacuum_exceeds` — the concrete BRIDGE-DEFEAT at `w = 95/96`:
        eigShift N (p+1) _ (95/96) 0  ≥  coeffW (95/96) 1²  >  1/12  ( = q112 ),
    i.e. the per-mode `eigShift ≤ 1/12` hypothesis of `bondMoved_below_gapEdge` is
    VIOLATED for the genuine `p ≥ 2` bond-moving even at the vacuum — confirming the
    bridge does NOT close with the un-normalized `bmEig`.
  * `s1_anchor` — the `s = 1` (gap-edge) anchor: at `p = 1` the gap-edge eigShift
    vanishes (`eigShift N 1 _ w 1 ≃ 0`), and the genuine `s = 1` RETUNED transverse
    defect is the QUADRATIC `bondMovingDeltaRen` (`bondMovingDeltaRen_quadratic`,
    `≤ 18·(1−w)²`).  `s = 1` is a LOW mode (`EigenvalueShiftBridge.gapMode_low`),
    handled by the summable quadratic budget — distinct from the bulk/vacuum defect.

# HONEST scope and the precise next step

This is NOT a 4D Yang–Mills mass-gap proof.  It is the SHARP order verdict for the
mult-blind eigenvalue defect: dividing out `dimQ s` does NOT restore quadraticity;
the bulk eigShift is `Θ(1)`-or-larger because the fusion carries the vacuum L²-mass
`bmc(0)`.  The PRECISE NEXT STEP is therefore to pass to the VACUUM-NORMALIZED
eigenvalue `λ(s) = bmc(s)/((s+1)·bmc(0))` (the genuine transfer-operator spectrum),
re-run the bridge against `retEig`, and confront the residual LINEARITY of `λ(s) −
retEig(s)` on the bulk (the documented `FusionRelResidualBound` order) — the `1/p`
retune fixes the exponent, so the remaining content is exactly the SUB-leading
prefactor correction of the local CLT.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic over proved engines (`fusionPow_one_eq`,
`bmc_ge_identity`, `divPos_mul_left_cancel`, `le_divPos_of_mul_le`, `le_absQ`,
`fsum_term_le_of_nonneg`).  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on closed decidable facts), no
`sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.EigenvalueShiftBridge
import YMGap.Continuum.BondMovingRelResidual
import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.S1Dominance

namespace YMGap.Continuum.EigShiftOrder

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.EigenvalueShiftBridge

/-! ## 0. Small helpers (axiom-clean) -/

/-- `absQ x ≃ 0` when `x ≃ 0` (local copy; the value-level argument vanishes). -/
theorem absQ_eqv_zero {x : Q'} (h : x.eqv 0) : (absQ x).eqv 0 := by
  unfold absQ
  by_cases hx : (0 : Int) ≤ x.num
  · rw [if_pos hx]; exact h
  · rw [if_neg hx]
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr x 0 h) ?_
    show (-(0 : Q')).eqv 0
    decide

/-- **Two-summand lower bound for `fsum`.**  For a nonnegative sequence `f` and
indices `i < j < n`, the two summands `f i + f j` are `≤` the whole sum `fsum f n`.
(Induction on `n`: if `j < n` recurse and add the nonnegative last term; if `j = n`,
`f i ≤ fsum f n` by `fsum_term_le_of_nonneg` and add `f n` on the right.) -/
theorem fsum_two_term_le {f : Nat → Q'} (hf : ∀ i, (0 : Q') ≤ f i)
    (i j : Nat) (hij : i < j) : ∀ (n : Nat), j < n → f i + f j ≤ fsum f n
  | 0, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, hj => by
      show f i + f j ≤ fsum f n + f n
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact Q'.le_trans' _ _ _ (fsum_two_term_le hf i j hij n hlt)
          (Q'.add_le_self_of_nonneg _ _ (hf n))
      · rw [heq]
        rw [heq] at hij
        exact Q'.add_le_add_right _ _ (f n) (fsum_term_le_of_nonneg hf i n hij)

/-! ## 1. THE `p = 1` EXACT VANISHING -/

/-- **`eigShift_p1_zero` — the eigenvalue defect VANISHES at `p = 1`.**  For `s ≤ N`,

    eigShift N 1 _ w s  ≃  0.

At `p = 1` (heat-kernel input, no bond-moving): the unit fusion identity gives
`bondMovedCoeff N w 1 s ≃ coeffW w s = dimQ s · w^{C₄(s)}`, so `bmEig N 1 w s ≃
w^{C₄(s)}`; and `renormWFix 1 _ w ≃ w` gives `retEig 1 _ w s ≃ w^{C₄(s)}`.  The two
EIGENVALUES coincide, so the defect vanishes EXACTLY — confirming `eigShift` is a
genuine `p ≥ 2` bond-moving effect, NOT the `deltaRen` linear-model overshoot
(which is `Θ(1)` already at `p = 1`). -/
theorem eigShift_p1_zero (N : Nat) (w : Q') (s : Nat) (hsN : s ≤ N) :
    (eigShift N 1 (by decide) w s).eqv 0 := by
  -- bmEig N 1 w s ≃ qpow w (c4 s)
  have hbm : (bmEig N 1 w s).eqv (qpow w (c4 s)) := by
    show (Q'.divPos (bondMovedCoeff N w 1 s) (dimQ s) (Q'.ofNat_succ_pos s)).eqv
        (qpow w (c4 s))
    have hc : (Q'.divPos (bondMovedCoeff N w 1 s) (dimQ s) (Q'.ofNat_succ_pos s)).eqv
        (Q'.divPos (coeffW w s) (dimQ s) (Q'.ofNat_succ_pos s)) := by
      show (bondMovedCoeff N w 1 s * Q'.recipPos (dimQ s) (Q'.ofNat_succ_pos s)).eqv
          (coeffW w s * Q'.recipPos (dimQ s) (Q'.ofNat_succ_pos s))
      exact Q'.mul_eqv_congr_right _ _ _ (fusionPow_one_eq hsN)
    refine Q'.eqv_trans _ _ _ hc ?_
    show (Q'.divPos (dimQ s * qpow w (c4 s)) (dimQ s) (Q'.ofNat_succ_pos s)).eqv
        (qpow w (c4 s))
    exact HeatKernelRGStep.divPos_mul_left_cancel (dimQ s) (qpow w (c4 s))
      (Q'.ofNat_succ_pos s)
  -- retEig 1 _ w s = qpow (renormWFix 1 _ w) (c4 s) ≃ qpow w (c4 s)
  have hret : (retEig 1 (by decide) w s).eqv (qpow w (c4 s)) := by
    show (qpow (renormWFix 1 (by decide) w) (c4 s)).eqv (qpow w (c4 s))
    exact qpow_eqv_congr_base (renormWFix_one w) (c4 s)
  -- argument ≃ 0
  have harg : (bmEig N 1 w s + -(retEig 1 (by decide) w s)).eqv 0 := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hbm (Q'.neg_eqv_congr _ _ hret)) ?_
    exact Q'.add_neg_self_eqv (qpow w (c4 s))
  show (absQ (bmEig N 1 w s + -(retEig 1 (by decide) w s))).eqv 0
  exact absQ_eqv_zero harg

/-! ## 2. THE VACUUM L²-MASS LOWER BOUND (general bond-moving `p + 1`) -/

/-- **`bmc_vacuum_lower` — the sharp vacuum lower bound.**  For `0 ≤ w ≤ 1`,
`1 ≤ N`, `p ≥ 1`,

    bondMovedCoeff N w (p+1) 0  ≥  1  +  coeffW w 1 · coeffW w 1   ( = 1 + 4w⁶ ).

PROOF: `bondMovedCoeff N w (p+1) 0 = fusionProduct N (fusionPow N (coeffW w) p)
(coeffW w) 0` is a double sum of nonnegative terms.  Extract TWO outer summands
(rows `a = 0` and `a = 1`, `fsum_two_term_le`):
  * row `0` ≥ its `(b = 0)` term `= 1·(g_p(0)·coeffW w 0) = g_p(0)·1 ≥ 1`
    (`g_p(0) = bondMovedCoeff N w p 0 ≥ coeffW w 0 = 1`, the identity channel);
  * row `1` ≥ its `(b = 1)` term `= 1·(g_p(1)·coeffW w 1) ≥ coeffW w 1·coeffW w 1`
    (`g_p(1) ≥ coeffW w 1`, the first-excited self-fusion channel).
This is the vacuum L²-mass EXCESS — the seed of the eigenvalue-defect obstruction. -/
theorem bmc_vacuum_lower (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hN : 1 ≤ N) (p : Nat) (hp : 0 < p) :
    (1 : Q') + coeffW w 1 * coeffW w 1 ≤ bondMovedCoeff N w (p + 1) 0 := by
  have hc_nn : ∀ t, (0 : Q') ≤ fusionPow N (coeffW w) p t :=
    fusionPow_nonneg N (coeffW_nonneg hw0) p
  have hd_nn : ∀ t, (0 : Q') ≤ coeffW w t := coeffW_nonneg hw0
  -- the outer summand (row) at index `a`
  have hF_nn : ∀ a, (0 : Q') ≤
      fsum (fun b => fusionInd a b 0 * (fusionPow N (coeffW w) p a * coeffW w b)) (N + 1) :=
    fun a => fsum_nonneg (fun b => Q'.mul_nonneg _ _ (fusionInd_nonneg a b 0)
      (Q'.mul_nonneg _ _ (hc_nn a) (hd_nn b))) (N + 1)
  -- row 0 ≥ 1
  have hr0 : (1 : Q') ≤
      fsum (fun b => fusionInd 0 b 0 * (fusionPow N (coeffW w) p 0 * coeffW w b)) (N + 1) := by
    have hterm : fusionInd 0 0 0 * (fusionPow N (coeffW w) p 0 * coeffW w 0)
        ≤ fsum (fun b => fusionInd 0 b 0 * (fusionPow N (coeffW w) p 0 * coeffW w b)) (N + 1) :=
      fsum_term_le_of_nonneg (fun b => Q'.mul_nonneg _ _ (fusionInd_nonneg 0 b 0)
        (Q'.mul_nonneg _ _ (hc_nn 0) (hd_nn b))) 0 (N + 1) (Nat.succ_pos N)
    have hfi : fusionInd 0 0 0 = (1 : Q') := by unfold fusionInd; rw [if_pos (by decide)]
    have hc0 : (1 : Q') ≤ fusionPow N (coeffW w) p 0 := by
      have h := bmc_ge_identity N hw0 hw1 0 (Nat.zero_le N) p hp
      rwa [coeffW_zero] at h
    have heq : (fusionInd 0 0 0 * (fusionPow N (coeffW w) p 0 * coeffW w 0)).eqv
        (fusionPow N (coeffW w) p 0) := by
      rw [hfi, coeffW_zero]
      exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.mul_one_eqv _)
    exact Q'.le_trans' _ _ _ hc0 (Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hterm)
  -- row 1 ≥ coeffW w 1 · coeffW w 1
  have hr1 : coeffW w 1 * coeffW w 1 ≤
      fsum (fun b => fusionInd 1 b 0 * (fusionPow N (coeffW w) p 1 * coeffW w b)) (N + 1) := by
    have hterm : fusionInd 1 1 0 * (fusionPow N (coeffW w) p 1 * coeffW w 1)
        ≤ fsum (fun b => fusionInd 1 b 0 * (fusionPow N (coeffW w) p 1 * coeffW w b)) (N + 1) :=
      fsum_term_le_of_nonneg (fun b => Q'.mul_nonneg _ _ (fusionInd_nonneg 1 b 0)
        (Q'.mul_nonneg _ _ (hc_nn 1) (hd_nn b))) 1 (N + 1) (Nat.lt_succ_of_le hN)
    have hfi : fusionInd 1 1 0 = (1 : Q') := by unfold fusionInd; rw [if_pos (by decide)]
    have hc1 : coeffW w 1 ≤ fusionPow N (coeffW w) p 1 := bmc_ge_identity N hw0 hw1 1 hN p hp
    have heq : (fusionInd 1 1 0 * (fusionPow N (coeffW w) p 1 * coeffW w 1)).eqv
        (fusionPow N (coeffW w) p 1 * coeffW w 1) := by
      rw [hfi]; exact Q'.one_mul_eqv _
    have hmul : coeffW w 1 * coeffW w 1 ≤ fusionPow N (coeffW w) p 1 * coeffW w 1 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hc1 (coeffW_nonneg hw0 1)
    exact Q'.le_trans' _ _ _ hmul (Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hterm)
  -- assemble: the two rows sum below the full double sum
  show (1 : Q') + coeffW w 1 * coeffW w 1
      ≤ fsum (fun a => fsum (fun b =>
          fusionInd a b 0 * (fusionPow N (coeffW w) p a * coeffW w b)) (N + 1)) (N + 1)
  refine Q'.le_trans' _ _ _ (EigenvalueShiftBridge.qadd_le_add hr0 hr1) ?_
  exact fsum_two_term_le hF_nn 0 1 (by decide) (N + 1) (Nat.lt_succ_of_le hN)

/-! ## 3. THE SHARP NEGATIVE — eigShift at the vacuum is Θ(1), not quadratic -/

/-- **`eigShift_vacuum_lower` — the mult-blind eigenvalue defect is Θ(1)-or-larger.**
For `0 ≤ w ≤ 1`, `1 ≤ N`, `p ≥ 1`,

    eigShift N (p+1) _ w 0  ≥  coeffW w 1 · coeffW w 1   ( = 4w⁶ ).

`retEig (p+1) _ w 0 = renormWFix^{C₄(0)} = renormWFix^0 = 1` (the vacuum), while
`bmEig N (p+1) w 0 = bondMovedCoeff N w (p+1) 0 / dimQ 0 = bmc(0) ≥ 1 + coeffW w 1²`.
So `bmEig − retEig ≥ coeffW w 1²`, and `eigShift = |bmEig − retEig| ≥ coeffW w 1²`.
This is the un-divided vacuum L²-mass excess `bmc(0) − 1`: dividing out the
multiplicity `dimQ s` does NOT touch it.  Hence `eigShift` is NOT `O((1−w)²)` and
NOT `≤ 1/12` — verdict (b). -/
theorem eigShift_vacuum_lower (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hN : 1 ≤ N) (p : Nat) (hp : 0 < p) :
    coeffW w 1 * coeffW w 1 ≤ eigShift N (p + 1) (Nat.succ_pos p) w 0 := by
  have hbmc : (1 : Q') + coeffW w 1 * coeffW w 1 ≤ bondMovedCoeff N w (p + 1) 0 :=
    bmc_vacuum_lower N hw0 hw1 hN p hp
  -- bmEig N (p+1) w 0 ≥ 1 + coeffW w 1²  (dimQ 0 = 1)
  have hbmEig : (1 : Q') + coeffW w 1 * coeffW w 1 ≤ bmEig N (p + 1) w 0 := by
    have hmul : ((1 : Q') + coeffW w 1 * coeffW w 1) * dimQ 0
        ≤ bondMovedCoeff N w (p + 1) 0 := by
      have he : (((1 : Q') + coeffW w 1 * coeffW w 1) * dimQ 0).eqv
          ((1 : Q') + coeffW w 1 * coeffW w 1) := by
        rw [dimQ_zero]; exact Q'.mul_one_eqv _
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hbmc
    show (1 : Q') + coeffW w 1 * coeffW w 1
        ≤ Q'.divPos (bondMovedCoeff N w (p + 1) 0) (dimQ 0) (Q'.ofNat_succ_pos 0)
    exact Q'.le_divPos_of_mul_le _ _ (Q'.ofNat_succ_pos 0) hmul
  -- subtract retEig = 1 : coeffW w 1² ≤ bmEig + -(retEig)
  have hdiff : coeffW w 1 * coeffW w 1
      ≤ bmEig N (p + 1) w 0 + -(retEig (p + 1) (Nat.succ_pos p) w 0) := by
    show coeffW w 1 * coeffW w 1 ≤ bmEig N (p + 1) w 0 + -(1 : Q')
    have hstep : ((1 : Q') + coeffW w 1 * coeffW w 1) + -(1 : Q')
        ≤ bmEig N (p + 1) w 0 + -(1 : Q') :=
      Q'.add_le_add_right _ _ _ hbmEig
    have heq : (((1 : Q') + coeffW w 1 * coeffW w 1) + -(1 : Q')).eqv
        (coeffW w 1 * coeffW w 1) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (1 : Q') (coeffW w 1 * coeffW w 1))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (coeffW w 1 * coeffW w 1) (1 : Q') (-(1 : Q'))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (1 : Q'))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' _)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hstep
  show coeffW w 1 * coeffW w 1
      ≤ absQ (bmEig N (p + 1) w 0 + -(retEig (p + 1) (Nat.succ_pos p) w 0))
  exact Q'.le_trans' _ _ _ hdiff (le_absQ _)

/-- **`eigShift_vacuum_exceeds` — the concrete BRIDGE-DEFEAT at `w = 95/96`.**  For
every genuine bond-moving exponent `p + 1` (`p ≥ 1`, `1 ≤ N`),

    eigShift N (p+1) _ (95/96) 0  ≥  coeffW (95/96) 1²  >  1/12  ( = q112 ).

So the per-mode hypothesis `eigShift ≤ 1/12` of
`EigenvalueShiftBridge.bondMoved_below_gapEdge` is VIOLATED at the vacuum for the
genuine `p ≥ 2` bond-moving — the eigenvalue bridge does NOT close with the
un-normalized `bmEig`.  (`95/96` is the bridge's own near-continuum demo weight,
`1 − w = 1/96 ≤ 1/12`.) -/
theorem eigShift_vacuum_exceeds (N : Nat) (hN : 1 ≤ N) (p : Nat) (hp : 0 < p) :
    SpectralLocalizationCrux.q112
      ≤ eigShift N (p + 1) (Nat.succ_pos p) EigenvalueShiftBridge.demoW 0 := by
  have hlow : coeffW EigenvalueShiftBridge.demoW 1 * coeffW EigenvalueShiftBridge.demoW 1
      ≤ eigShift N (p + 1) (Nat.succ_pos p) EigenvalueShiftBridge.demoW 0 :=
    eigShift_vacuum_lower N SpectralLocalizationCrux.demoW_pos
      SpectralLocalizationCrux.demoW_le_one hN p hp
  have hnum : SpectralLocalizationCrux.q112
      ≤ coeffW EigenvalueShiftBridge.demoW 1 * coeffW EigenvalueShiftBridge.demoW 1 := by
    decide
  exact Q'.le_trans' _ _ _ hnum hlow

/-! ## 4. THE `s = 1` GAP-EDGE ANCHOR -/

/-- **`s1_anchor` — the gap-edge mode `s = 1`.**  BOTH hold:

  (i)  the gap-edge eigShift VANISHES at `p = 1` (`eigShift N 1 _ w 1 ≃ 0`); and
  (ii) the genuine `s = 1` RETUNED transverse defect is QUADRATIC in the margin,
       `bondMovingDeltaRen N 1 w ≤ 18·(1−w)²` (`bondMovingDeltaRen_quadratic`).

`s = 1` is a LOW mode (`EigenvalueShiftBridge.gapMode_low`: `C₄(1)(1−w) ≤ 1/4 < 1/2`,
below the bulk window), so its cumulative bond-moving shift is the SUMMABLE `s = 1`
quadratic budget — structurally DISTINCT from the bulk/vacuum `Θ(1)` defect above.
This is the precise sense in which the eigShift at the gap edge is the
`bondMovingDeltaRen`-controlled quadratic quantity. -/
theorem s1_anchor (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hN : 1 ≤ N) :
    (eigShift N 1 (by decide) w 1).eqv 0
      ∧ bondMovingDeltaRen N 1 w
          ≤ (Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat (c4 1) * Q'.ofNat (c4 1))))
              * (((1 : Q') - w) * ((1 : Q') - w)) :=
  ⟨eigShift_p1_zero N w 1 hN, bondMovingDeltaRen_quadratic hw0 hw1 N 1⟩

end YMGap.Continuum.EigShiftOrder

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.EigShiftOrder.absQ_eqv_zero
#print axioms YMGap.Continuum.EigShiftOrder.fsum_two_term_le
#print axioms YMGap.Continuum.EigShiftOrder.eigShift_p1_zero
#print axioms YMGap.Continuum.EigShiftOrder.bmc_vacuum_lower
#print axioms YMGap.Continuum.EigShiftOrder.eigShift_vacuum_lower
#print axioms YMGap.Continuum.EigShiftOrder.eigShift_vacuum_exceeds
#print axioms YMGap.Continuum.EigShiftOrder.s1_anchor
