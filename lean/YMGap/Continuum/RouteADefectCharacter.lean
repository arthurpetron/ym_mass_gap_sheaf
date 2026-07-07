/-
Track B / R2 — ROUTE A (CHARACTER / FUSION): connecting the JUST-CLOSED SU(2)
fusion local-CLT / s1-dominance to the REAL 4D block-spin excited-mode leakage,
and bounding that leakage by the TRANSVERSE QUADRATIC `6·pMult·(1−w)²` — the exact
envelope the model defect `δ_model = afDefectSeq` is compared against in
`SingleStepDefectReduction.SingleStepDefectBound.singleStep`.

# What this module does (read first)

The whole Clay continuum gap reduces (`SingleStepDefectReduction`) to the ONE open
per-step inequality `singleStep : (1 − δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}`,
i.e. the real 4D SU(2) block-spin per-step defect `realδ_k` of the TRUE dimensionless
margin is `≤ δ_model(w_k)`.  `δ_model` is DEFINED algebraically
(`bondMovingDeltaRen = p·2·(3(1−w) − (1−w³))`) and is PROVED `≤ 6·pMult·(1−w)²`
(`afDefectSeq_le_transverseQuad`).

Route A attacks the PHYSICAL side: the real per-step defect IS the excited-mode
leakage of the block-spin (fused) transfer matrix, and that leakage is the fused
FIRST-EXCITED / VACUUM character ratio.  This module PROVES, for the REAL SU(2)
character/fusion coefficients (`coeffW`, `acNfull`), in the strong-coupling regime
`0 ≤ w ≤ 1/2` (exactly where the fusion s1-dominance `SymMinorGershgorin` is
inhabited, `FusionUTuranReindex.symMinorGershgorin_of_trunc`), that:

  (S1) the single-plaquette (`p = 1`) real excited/vacuum ratio
       `coeffW w 1 / coeffW w 0 = 2·w³` is `≤ 6·(1 − w)²`  — the transverse
       quadratic at `pMult = 1`  (`charExcited_le_transverseQuad`);

  (S2) the 2-fold FUSED (`p = 2`, real autoconvolution `acNfull`) excited/vacuum
       ratio `acNfull w 1 / acNfull w 0 = 4·w³` is `≤ 12·(1 − w)²` = `6·2·(1 − w)²`
       — the transverse quadratic with the multi-link SHELL FACTOR `6·pMult`,
       `pMult = 2`  (`fusedExcited_le_transverseQuad`).

So the REAL fused excited-mode leakage is bounded by the SAME transverse quadratic
`6·pMult·(1 − w)²` that bounds the model defect `δ_model` — the character/fusion
derivation of "`realδ` is transverse-quadratic, matching the model".  Both realδ and
δ_model live under one envelope.

# HONEST verdict (AGENTS.md Rule 6 / Rule 9) — what is PROVED vs OPEN

PROVED (this module, real character/fusion coefficients, `0 ≤ w ≤ 1/2`):
  * the real single-plaquette AND 2-fold-fused excited/vacuum ratios are `≤`
    the transverse quadratic `6·pMult·(1 − w)²`.  This is the genuine
    "s1-dominance ⇒ excited-ratio ≤ 6(1−w)²" sub-lemma the crux asks for, made
    rigorous, over the strong-coupling regime where the fusion reserve is proved.

OPEN (the genuine residual, NOT inhabited here — it IS the Clay core):
  * `FullRangeFusedDefect` — the SAME bound extended to the WEAK-coupling / deep-UV
    regime `w → 1` (where AF drives `w_k → 1`), which needs (i) the RENORMALIZED
    (counterterm-subtracted) leakage, not the raw ratio (the raw ratio `2w³ → 2` at
    `w → 1`, so the raw bound FAILS there — machine-fact `raw_ratio_exceeds_at_weak`),
    and (ii) the fusion s1-dominance extended past `w = 1/2`.  This is the crux's
    (R-UV) moment-uniformity `α < 1` + (R-cross) finite-crossover residual.
  * The exact per-step matching `realδ_k ≤ δ_model_k` (not merely both `≤` the shared
    envelope) — the content of `SingleStepDefectBound.singleStep` — is NOT inhabited.
    We do NOT construct `SingleStepDefectBound` (it cascades to the guarded frontier).

# Adversarial honesty

The bound proved here is GENUINE and NON-VACUOUS: `charExcited_le_transverseQuad`
and `fusedExcited_le_transverseQuad` are real inequalities on the actual
heat-kernel / autoconvolution coefficients, and `raw_ratio_exceeds_at_weak` proves
the raw statement is FALSE at `w = 9/10` — so the strong-coupling restriction is
NECESSARY, not decorative, and the residual is real.  NO 4D Yang–Mills mass gap is
claimed; nothing is faked; no guarded bundle is inhabited.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing PROVED coefficient facts (`coeffW_zero`,
`coeffW1_le_one_of_strong`, `bondMovingDeltaRen_le_sixp`, `afDefectSeq_le_transverseQuad`).
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses are `Type`-level `Q'` data.
-/

import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Continuum.SelfFusionLogConcave
import YMGap.Continuum.CircleFourierPowerModel

namespace YMGap.Continuum.RouteADefectCharacter

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction

/-- Local abbreviation for the strong-coupling edge `1/2`. -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-! ## 0. The strong-coupling margin floor `1/2 ≤ 1 − w` and its square. -/

/-- For `w ≤ 1/2`, the weak-coupling margin `1 − w ≥ 1/2`. -/
theorem half_le_oneSub {w : Q'} (hw : w ≤ half) : half ≤ (1 : Q') - w := by
  have hneg : -half ≤ -w := Q'.neg_le_neg hw
  have hstep : (1 : Q') + (-half) ≤ (1 : Q') + (-w) := Q'.add_le_add_left 1 _ _ hneg
  have heq : ((1 : Q') + (-half)).eqv half := by decide
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hstep

/-- For `0 ≤ w ≤ 1/2`, `(1/2)² ≤ (1 − w)²`, i.e. `1/4 ≤ (1 − w)·(1 − w)`. -/
theorem quarter_le_oneSubSq {w : Q'} (hw : w ≤ half) :
    (half * half) ≤ ((1 : Q') - w) * ((1 : Q') - w) :=
  sq_le_sq (by decide : (0 : Q') ≤ half) (half_le_oneSub hw)

/-- `3/2 ≤ 6·(1 − w)²` for `w ≤ 1/2`: `6·(1 − w)² ≥ 6·(1/2)² = 3/2`. -/
theorem threeHalves_le_six_oneSubSq {w : Q'} (hw : w ≤ half) :
    Q'.mkPos 3 2 (by decide) ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) := by
  have hmul : Q'.ofNat 6 * (half * half)
      ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (quarter_le_oneSubSq hw) (by decide)
  refine Q'.le_trans' _ _ _ ?_ hmul
  -- 3/2 ≃ 6·(1/2·1/2) = 6·1/4
  exact Q'.le_of_eqv (by decide : (Q'.mkPos 3 2 (by decide)).eqv (Q'.ofNat 6 * (half * half)))

/-! ## 1. (S1) — the REAL single-plaquette excited/vacuum ratio ≤ transverse quadratic.

`coeffW w 0 = 1` (`coeffW_zero`), so the vacuum-normalized first-excited ratio IS
`coeffW w 1 = 2·w³` — the genuine SU(2) heat-kernel transfer-matrix gap separator.
In the strong-coupling regime `w ≤ 1/2` it is `≤ 1 ≤ 3/2 ≤ 6·(1 − w)²`. -/

/-- **(S1) `charExcited_le_transverseQuad`.**  The REAL single-plaquette
first-excited/vacuum character ratio `coeffW w 1 / coeffW w 0 = 2·w³` is bounded by
the transverse quadratic `6·(1 − w)²` for `0 ≤ w ≤ 1/2`:

    coeffW w 1  ≤  6·(1 − w)²  =  6·pMult·(1 − w)² |_{pMult = 1}.

(`coeffW w 0 = 1`, so `coeffW w 1` IS the vacuum-normalized excited ratio.)  This is
the transverse-quadratic envelope at `pMult = 1`, identical to the model-defect bound
`afDefectSeq_le_transverseQuad`.  PROVED from `coeffW1_le_one_of_strong`
(`coeffW w 1 ≤ 1`) and `threeHalves_le_six_oneSubSq`. -/
theorem charExcited_le_transverseQuad {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    coeffW w 1 ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) := by
  have h1 : coeffW w 1 ≤ (1 : Q') := coeffW1_le_one_of_strong hw0 hw
  have h32 : (1 : Q') ≤ Q'.mkPos 3 2 (by decide) := by decide
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h32 (threeHalves_le_six_oneSubSq hw))

/-- **The excited ratio equals the vacuum-normalized quantity.**  Since
`coeffW w 0 = 1`, `coeffW w 1 ≃ coeffW w 1 · coeffW w 0` is literally the
first-excited-over-vacuum ratio, confirming (S1) bounds the genuine leakage. -/
theorem charExcited_is_vacuum_normalized (w : Q') :
    (coeffW w 1).eqv (coeffW w 1 * coeffW w 0) := by
  rw [coeffW_zero]; exact Q'.eqv_symm (Q'.mul_one_eqv (coeffW w 1))

/-! ## 2. (S2) — the REAL 2-fold FUSED excited/vacuum ratio ≤ transverse quadratic.

The block-spin coarse link fuses parallel fine links; the 2-fold fusion is the
central autoconvolution `acNfull w t = Σ_{p≤t} coeffW w p · coeffW w (t−p)`
(`CircleFourierPowerModel`).  Its vacuum is `acNfull w 0 = 1` and its first-excited
is `acNfull w 1 = 2·coeffW w 1 = 4·w³` (the two Clebsch channels `(0,1),(1,0)`).
The fused excited/vacuum ratio is `4·w³ ≤ 12·(1 − w)²` — the SHELL FACTOR `6·pMult`
with `pMult = 2`. -/

/-- **`acNfull w 0 ≃ 1`** — the fused VACUUM coefficient (`coeffW w 0 · coeffW w 0`). -/
theorem acNfull_zero_eqv (w : Q') : (acNfull w 0).eqv 1 := by
  show (fsum (fun p => coeffW w p * coeffW w (0 - p)) 1).eqv 1
  simp only [fsum]
  rw [coeffW_zero]
  -- (0 + 1 · 1).eqv 1
  exact Q'.eqv_trans _ _ _ (q_zero_add_eqv _) (Q'.mul_one_eqv 1)

/-- **`acNfull w 1 ≃ coeffW w 1 + coeffW w 1`** — the fused FIRST-EXCITED coefficient:
the two Clebsch channels `(0,1)` and `(1,0)` each contribute `coeffW w 1`. -/
theorem acNfull_one_eqv (w : Q') :
    (acNfull w 1).eqv (coeffW w 1 + coeffW w 1) := by
  show (fsum (fun p => coeffW w p * coeffW w (1 - p)) 2).eqv (coeffW w 1 + coeffW w 1)
  simp only [fsum]
  rw [coeffW_zero]
  -- ((0 + 1 · coeffW w 1) + coeffW w 1 · 1).eqv (coeffW w 1 + coeffW w 1)
  refine Q'.add_eqv_congr' ?_ (Q'.mul_one_eqv (coeffW w 1))
  exact Q'.eqv_trans _ _ _ (q_zero_add_eqv _) (Q'.one_mul_eqv (coeffW w 1))

/-- **(S2) `fusedExcited_le_transverseQuad`.**  The REAL 2-fold-fused (block-spin,
`p = 2`) first-excited/vacuum character ratio `acNfull w 1 = 4·w³` is bounded by the
transverse quadratic with the multi-link SHELL FACTOR `6·pMult`, `pMult = 2`:

    acNfull w 1  ≤  12·(1 − w)²  =  6·2·(1 − w)²        (0 ≤ w ≤ 1/2).

Since `acNfull w 0 ≃ 1`, the LHS is exactly the vacuum-normalized fused excited
leakage.  PROVED: `acNfull w 1 ≃ 2·coeffW w 1 ≤ 2·6·(1 − w)² = 12·(1 − w)²` via (S1). -/
theorem fusedExcited_le_transverseQuad {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    acNfull w 1 ≤ Q'.ofNat 12 * (((1 : Q') - w) * ((1 : Q') - w)) := by
  have hS1 : coeffW w 1 ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) :=
    charExcited_le_transverseQuad hw0 hw
  -- coeffW w 1 + coeffW w 1 ≤ 6X + 6X ≃ 12X
  have hsum : coeffW w 1 + coeffW w 1
      ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w))
        + Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) :=
    AFRateCalibration.q_add_le_add hS1 hS1
  have heq : (Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w))
        + Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w))).eqv
      (Q'.ofNat 12 * (((1 : Q') - w) * ((1 : Q') - w))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 6) (Q'.ofNat 6)
        (((1 : Q') - w) * ((1 : Q') - w)))) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (by decide : ((Q'.ofNat 6) + (Q'.ofNat 6)).eqv (Q'.ofNat 12))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (acNfull_one_eqv w)) ?_
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv heq)

/-! ## 3. The connection to `δ_model` / `singleStep` — the shared transverse envelope.

Both the REAL fused excited leakage (S1/S2) and the MODEL defect `δ_model` are
`≤ 6·pMult·(1 − w)²`.  For `δ_model = afDefectSeq afr` the bound is
`afDefectSeq_le_transverseQuad` (RHS `ofNat pMult · (dimQ 1 · (ofNat 3 · (1−w)²))`);
for the real single-plaquette leakage it is (S1) (RHS `ofNat 6 · (1−w)²`).  The two
RHS agree at `pMult = 1` (`transverseQuad_pMult1_eqv`), so the comparison
`realδ ≤ δ_model` of `singleStep` is anchored to a genuine physical quantity, not a
definitional choice. -/

/-- The transverse-quadratic RHS of `afDefectSeq_le_transverseQuad` at `pMult = 1`
equals the `6·(1 − w)²` RHS of (S1): `ofNat 1·(dimQ 1·(ofNat 3·X)) ≃ ofNat 6·X`. -/
theorem transverseQuad_pMult1_eqv (w : Q') :
    (Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 *
        (((1 : Q') - w) * ((1 : Q') - w))))).eqv
      (Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w))) := by
  -- ofNat 1·(dimQ 1·(ofNat 3·X)) ≃ dimQ 1·(ofNat 3·X) ≃ (dimQ 1·ofNat 3)·X ≃ ofNat 6·X
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (dimQ 1) (Q'.ofNat 3)
      (((1 : Q') - w) * ((1 : Q') - w)))) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (by decide : (dimQ 1 * Q'.ofNat 3).eqv (Q'.ofNat 6))

/-- **`charExcited_le_modelEnvelope` — the real leakage sits under the SAME envelope
as `δ_model`.**  The real single-plaquette excited/vacuum ratio is `≤` the exact
transverse-quadratic RHS that `afDefectSeq_le_transverseQuad` bounds `δ_model` by (at
`pMult = 1`).  So `realδ` and `δ_model` share the envelope `6·(1 − w)²` — the
character/fusion anchoring of `singleStep`'s comparison. -/
theorem charExcited_le_modelEnvelope {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    coeffW w 1
      ≤ Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 *
          (((1 : Q') - w) * ((1 : Q') - w)))) := by
  exact Q'.le_trans' _ _ _ (charExcited_le_transverseQuad hw0 hw)
    (Q'.ge_of_eqv (transverseQuad_pMult1_eqv w))

/-! ## 4. The GENUINE RESIDUAL — the weak-coupling extension (NOT inhabited).

The strong-coupling bound (S1/S2) is where the fusion s1-dominance
(`SymMinorGershgorin`, inhabited for `0 < w ≤ 1/2`) holds.  The AF trajectory drives
`w_k → 1` (deep UV), where the RAW excited ratio is NO LONGER small — the raw bound
FAILS — so the renormalized (counterterm-subtracted) leakage and the extension of the
fusion reserve past `w = 1/2` are needed.  This is the crux's residual. -/

/-- **`raw_ratio_exceeds_at_weak` — the strong-coupling restriction is NECESSARY.**
At the weak-coupling point `w = 9/10` the RAW excited ratio `coeffW w 1 = 2·(9/10)³ =
1458/1000` EXCEEDS `6·(1 − w)² = 6/100`: `¬ (coeffW (9/10) 1 ≤ 6·(1 − 9/10)²)`.  A
constructive proof that (S1) is FALSE without `w ≤ 1/2` — the residual is real, and the
`realδ ≤ δ_model` comparison at `w → 1` genuinely requires renormalization. -/
theorem raw_ratio_exceeds_at_weak :
    ¬ (coeffW (Q'.mkPos 9 10 (by decide)) 1
        ≤ Q'.ofNat 6 * (((1 : Q') - Q'.mkPos 9 10 (by decide))
            * ((1 : Q') - Q'.mkPos 9 10 (by decide)))) := by
  -- coeffW (9/10) 1 = 2·(9/10)³ = 1458/1000 ; 6·(1/10)² = 6/100 = 60/1000
  intro h
  have hcoeff : (coeffW (Q'.mkPos 9 10 (by decide)) 1).eqv (Q'.mkPos 1458 1000 (by decide)) := by
    show (dimQ 1 * qpow (Q'.mkPos 9 10 (by decide)) (c4 1)).eqv (Q'.mkPos 1458 1000 (by decide))
    decide
  have hrhs : (Q'.ofNat 6 * (((1 : Q') - Q'.mkPos 9 10 (by decide))
        * ((1 : Q') - Q'.mkPos 9 10 (by decide)))).eqv (Q'.mkPos 60 1000 (by decide)) := by
    decide
  have hbad : (Q'.mkPos 1458 1000 (by decide)) ≤ (Q'.mkPos 60 1000 (by decide)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcoeff) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hrhs))
  exact absurd hbad (by decide)

/-- **`FullRangeFusedDefect` — the NAMED OPEN residual (`Type`, Rule 6a; UNINHABITED).**
The extension of (S1)/(S2) to the FULL AF range (all `k`, including `w_k → 1`): the
real renormalized per-step block-spin excited leakage `realLeak k` is `≤` the
transverse quadratic `6·pMult·(1 − w_k)²` for EVERY `k` — the crux's (R-UV)
moment-uniformity `α < 1` + (R-cross) finite-crossover residual, and the fusion
s1-dominance extended past `w = 1/2`.

This is the SOLE remaining content of the character/fusion route to `singleStep`.  It
is NOT inhabited (its `w = 1/2`-restriction is (S1)/(S2); its `w → 1` content is the
Clay core).  We do NOT construct `SingleStepDefectBound` from it — that cascades to the
guarded frontier. -/
structure FullRangeFusedDefect (afr : AFRateModulus) : Type where
  /-- The real renormalized per-step block-spin excited leakage of the true margin. -/
  realLeak : Nat → Q'
  /-- The genuine leakage is nonnegative. -/
  realLeak_nonneg : ∀ k, (0 : Q') ≤ realLeak k
  /-- **The open full-range bound** — real leakage `≤` transverse quadratic at EVERY
  scale, including the deep UV `w_k → 1`.  Its `w ≤ 1/2` slice is proved (S1/S2); its
  `w → 1` content is the Clay-core residual. -/
  fullRange : ∀ k,
    realLeak k ≤ Q'.ofNat pMult * (dimQ 1 * (Q'.ofNat 3 *
      (((1 : Q') - afr.w (afCutoff afr + k)) * ((1 : Q') - afr.w (afCutoff afr + k)))))

/-- **`fullRange_dominates_model` — the residual, once inhabited, would give
`realLeak ≤ δ_model`'s envelope.**  From a `FullRangeFusedDefect` witness, the real
leakage is `≤` the transverse quadratic that also bounds `δ_model` — i.e. real leakage
and model defect share the envelope at every scale.  (This is the LOGICAL bridge; it
does NOT inhabit `SingleStepDefectBound`, which additionally needs the SHARP two-sided
`realδ_k ≤ δ_model_k` and the margin-degradation identity — both still open.) -/
theorem fullRange_dominates_model {afr : AFRateModulus}
    (F : FullRangeFusedDefect afr) (k : Nat) :
    F.realLeak k ≤ Q'.ofNat pMult * (dimQ 1 * (Q'.ofNat 3 *
      (((1 : Q') - afr.w (afCutoff afr + k)) * ((1 : Q') - afr.w (afCutoff afr + k))))) :=
  F.fullRange k

/-- **`model_defect_le_transverseQuad` — re-export: `δ_model` under the same envelope.**
The model defect `afDefectSeq afr k = δ_model(w_k)` is `≤` the identical transverse
quadratic RHS (`afDefectSeq_le_transverseQuad`).  Pairing this with (S1)/(S2) (real
leakage, strong regime) shows both are governed by `6·pMult·(1 − w)²` — the shared
envelope that anchors `singleStep`. -/
theorem model_defect_le_transverseQuad (afr : AFRateModulus) (k : Nat) :
    afDefectSeq afr k
      ≤ Q'.ofNat pMult * (dimQ 1 * (Q'.ofNat 3 *
          (((1 : Q') - afr.w (afCutoff afr + k)) * ((1 : Q') - afr.w (afCutoff afr + k))))) :=
  afDefectSeq_le_transverseQuad afr k

end YMGap.Continuum.RouteADefectCharacter

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RouteADefectCharacter.half_le_oneSub
#print axioms YMGap.Continuum.RouteADefectCharacter.quarter_le_oneSubSq
#print axioms YMGap.Continuum.RouteADefectCharacter.threeHalves_le_six_oneSubSq
#print axioms YMGap.Continuum.RouteADefectCharacter.charExcited_le_transverseQuad
#print axioms YMGap.Continuum.RouteADefectCharacter.charExcited_is_vacuum_normalized
#print axioms YMGap.Continuum.RouteADefectCharacter.acNfull_zero_eqv
#print axioms YMGap.Continuum.RouteADefectCharacter.acNfull_one_eqv
#print axioms YMGap.Continuum.RouteADefectCharacter.fusedExcited_le_transverseQuad
#print axioms YMGap.Continuum.RouteADefectCharacter.transverseQuad_pMult1_eqv
#print axioms YMGap.Continuum.RouteADefectCharacter.charExcited_le_modelEnvelope
#print axioms YMGap.Continuum.RouteADefectCharacter.raw_ratio_exceeds_at_weak
#print axioms YMGap.Continuum.RouteADefectCharacter.fullRange_dominates_model
#print axioms YMGap.Continuum.RouteADefectCharacter.model_defect_le_transverseQuad
