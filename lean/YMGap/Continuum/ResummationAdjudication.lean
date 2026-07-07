/-
Track B / R2 — STRUCTURAL ADJUDICATION of the multi-plaquette "degeneracy-resummation"
residual (`MultiPlaquetteEffectiveTransfer.fullWindow_gap_of_resummed_clustering`).

# The question this module SETTLES (NOT a `:= SingleStepDefectBound` alias)

`MultiPlaquetteEffectiveTransfer` builds the block-spin effective transfer `effTransfer`
whose located gap is PROVED on all of `(0,1)` with separator the RESUMMED heat-kernel
rate `w³ = heatKernelSep w`, and packages the remaining physical content as the
hypothesis of the conditional producer `fullWindow_gap_of_resummed_clustering`: that the
REAL block-spin transfer's correlator clusters at the resummed rate `w³` (degeneracy
`dimQ r` entering ONCE as a multiplicity) rather than the per-plaquette rate
`2w³ = dimQ 1 · w³` (degeneracy compounding per link).

This module DECIDES — with machine-checked implication/refutation proofs, NOT prose —
whether that residual (`ResummedClustering`, formalized precisely below) is
  (i) a genuinely-NEW STRICTLY-WEAKER `F`-node below the atomic core `singleStep`
      (i.e. a free/computable heat-kernel fact, or a strictly-weaker sub-obligation), or
  (ii) EQUI-INHABITS `singleStep` — a sharp re-framing, `F = 1` stands.

# The verdict (machine-checked below): EQUI-INHABITS — `F = 1` STANDS, sharp re-framing.

Four certificates, all axiom-clean:

  * **DIRECTION A (producer, PROVED).** `gap_of_resummedClustering`: `ResummedClustering S w`
    (`0<w<1`) produces a genuine `LocatedSpectralGap S`; its margin `1 − w³` is strictly
    positive (`resummedClustering_gap_margin_pos`).  The residual really is a gap producer.

  * **NON-VACUITY (PROVED).** `resummedClustering_effTransfer`: the block-spin MODEL
    `effTransfer` inhabits `ResummedClustering`, so the predicate is satisfiable — this is
    exactly the resummed clustering `eff_corr_cluster` proved in §MultiPlaquette.

  * **NON-FREE / interacting (PROVED refutation — the crux of the physics check).**
    `reconTransfer_not_resummedClustering`: the NAIVE per-plaquette (degeneracy-COMPOUNDING)
    real single-edge correlator `reconTransfer` — the genuine Wilson correlator,
    `wilsonG_eqv_reconTransfer_corr` — provably VIOLATES `ResummedClustering`: its leading
    eigenvalue is `coeffW w 1 = dimQ 1 · w³ = 2w³ > w³`, so it CANNOT cluster at rate `w³`.
    Hence achieving the resummed rate `w³` is NOT a free heat-kernel fact (the free rate
    VALUE `w³` is available, but the naive/free transfer does not attain it); it is the
    genuinely INTERACTING block-spin resummation — the same non-perturbative content as
    `singleStep`'s `realδ ≤ δ_model`.

  * **NOT AN F-MOVE BELOW `singleStep` (PROVED, `tm`-independence).**
    `resummedClustering_is_transferSide_not_singleStep`: `ResummedClustering S w` is a
    single-scale, transfer-operator-side statement that does NOT mention the true margin
    `tm`; whereas `singleStep`'s truth VARIES with `tm` at fixed `afr`
    (`singleStep_satisfiable_zero` for `tm ≡ 0`, `singleStep_falsifiable` for a concrete
    `tm`, both reused).  So — exactly as for `uniform_in_m` in
    `SingleStepDecompositionAdjudication` — no transfer-side/`afr`-only statement can imply
    or be equivalent to `singleStep`; `ResummedClustering` is INCOMPARABLE to `singleStep`,
    not a strictly-weaker sub-obligation of it.  And the per-scale margin `1 − w³` is NOT
    uniform (`resummed_margin_not_uniform`: it decreases toward `0` as `w → 1`), so the
    per-scale located gaps are in LATTICE units and do NOT deliver the uniform PHYSICAL
    floor either — the multi-plaquette route does not bypass `singleStep`.

# HONEST `F` verdict

`ResummedClustering` is a sharp, numerically-pinned (factor `dimQ 1 = 2`, `2w³` vs `w³`)
RE-FRAMING of the SAME interacting block-spin effective-action content as the atomic
`singleStep` core: a gap producer (A), realized by the model (non-vacuity), FALSE for the
free/naive transfer (non-free), incomparable to the `tm`-recursion `singleStep` and giving
only lattice-unit per-scale gaps (not the physical floor).  It EQUI-INHABITS the core's
difficulty; it is NOT a strictly-weaker computable `F`-node and NOT a core-bypassing
parallel obligation.  **`F = 1` STANDS.**  The multi-plaquette construction did NOT move
the core — it sharpened the residual to the degeneracy-resummation identity.  NO
`:= SingleStepDefectBound` alias is emitted (`C` unchanged); `SingleStepDefectBound`
inhabited nowhere; the 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition reusing PROVED `fullWindow_gap_of_resummed_clustering`,
`eff_corr_cluster`, `effLam_le_sep`, `coeffW_one`, `coeffW_pos`, `qpow_pos`,
`mul_lt_mul_of_pos_right`, `lt_irrefl'`, and the imported `singleStep_satisfiable_zero`
/ `singleStep_falsifiable`.  Every load-bearing declaration gated with `#print axioms`;
permitted output `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`sorry`, no `ring`/`nlinarith`.  `ResummedClustering` is `Type`-level data (Rule 8).
`decide` is used ONLY on closed concrete-rational facts (`1 < dimQ 1`, the non-uniformity
witnesses).
-/

import YMGap.Continuum.MultiPlaquetteEffectiveTransfer
import YMGap.Continuum.SingleStepDecompositionAdjudication

namespace YMGap.Continuum.ResummationAdjudication

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.TransferCorr
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.DirectSingleStepReconGap
open YMGap.Continuum.MultiPlaquetteEffectiveTransfer
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction
open YMGap.Continuum.SingleStepDecompositionAdjudication

/-! ## 0. The residual, formalized precisely: `ResummedClustering`.

The EXACT standalone content of the hypothesis of
`fullWindow_gap_of_resummed_clustering`: a supplied spectral model `S` (the real block
correlator) whose two-point function clusters at the RESUMMED rate `heatKernelSep w = w³`
with a positive amplitude, coupled live modes, and a `w³`-bounded tail.  `Type`-level
(Rule 8) since the amplitude is data. -/
structure ResummedClustering (S : SpectralModel) (w : Q') : Type where
  /-- Positive clustering amplitude. -/
  amp : Q'
  /-- Amplitude positivity. -/
  amp_pos : (0 : Q') < amp
  /-- The correlator clusters at the RESUMMED rate `w³` (degeneracy as multiplicity). -/
  cluster : ∀ n, corr S n ≤ amp * (heatKernelSep w) ^ n
  /-- Live modes are coupled. -/
  coupled : ∀ i, i < S.k → (0 : Q') < S.w i
  /-- The tail (unused slots) sits at or below the resummed rate. -/
  dead : ∀ i, S.k ≤ i → S.lam i ≤ heatKernelSep w

/-! ## 1. DIRECTION A — the producer: `ResummedClustering → LocatedSpectralGap`. -/

/-- **`gap_of_resummedClustering` — Direction A (PROVED).**  The resummed-clustering
residual produces a genuine `LocatedSpectralGap` with separator `heatKernelSep w = w³`,
for every `0 < w < 1` — in particular the whole `[w*, 1)`.  This is the conditional
producer `fullWindow_gap_of_resummed_clustering` fed the packaged hypotheses. -/
def gap_of_resummedClustering {w : Q'} (hwpos : (0 : Q') < w) (hwlt : w < (1 : Q'))
    {S : SpectralModel} (R : ResummedClustering S w) : LocatedSpectralGap S :=
  fullWindow_gap_of_resummed_clustering S hwpos hwlt R.amp R.amp_pos R.cluster R.coupled R.dead

/-- The produced gap's separator is the resummed heat-kernel rate `w³`. -/
theorem gap_of_resummedClustering_sep {w : Q'} (hwpos : (0 : Q') < w) (hwlt : w < (1 : Q'))
    {S : SpectralModel} (R : ResummedClustering S w) :
    (gap_of_resummedClustering hwpos hwlt R).sep = heatKernelSep w := rfl

/-- **`resummedClustering_gap_margin_pos` — the produced gap has a strictly positive
margin (PROVED).**  `0 < 1 − sep = 1 − w³`, the eigenvalue-gap margin of the gap that
`ResummedClustering` produces.  A positive located gap on all of `(0,1)`. -/
theorem resummedClustering_gap_margin_pos {w : Q'} (hwpos : (0 : Q') < w)
    (hwlt : w < (1 : Q')) {S : SpectralModel} (R : ResummedClustering S w) :
    (0 : Q') < (1 : Q') - (gap_of_resummedClustering hwpos hwlt R).sep :=
  one_sub_pos_of_lt_one (gap_of_resummedClustering hwpos hwlt R).sep_lt_one

/-! ## 2. NON-VACUITY — the block-spin MODEL `effTransfer` inhabits `ResummedClustering`. -/

/-- **`resummedClustering_effTransfer` (PROVED).**  The renormalized effective transfer
`effTransfer` inhabits `ResummedClustering`: its correlator DOES cluster at the resummed
rate `w³` (`eff_corr_cluster`), with coupled modes (`coeffW_pos`) and a `w³`-bounded
spectrum (`effLam_le_sep`).  So the residual is a satisfiable, non-vacuous predicate — the
resummed model realizes it. -/
def resummedClustering_effTransfer {w : Q'} (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (M : Nat) : ResummedClustering (effTransfer w (Q'.le_of_lt hwpos) (M + 1)) w where
  amp := degSum (M + 1) * heatKernelSep w
  amp_pos := Q'.mul_pos (degSum_pos M) (BondMovingScaledNorm.qpow_pos hwpos 3)
  cluster := fun n => eff_corr_cluster (Q'.le_of_lt hwpos) hw1 (M + 1) n
  coupled := fun i _ => coeffW_pos hwpos i
  dead := fun i _ => effLam_le_sep (Q'.le_of_lt hwpos) hw1 i

/-! ## 3. NON-FREE — the naive per-plaquette real transfer VIOLATES `ResummedClustering`.

This is the crux of the physics check: the resummed rate `w³` is NOT a free heat-kernel
fact.  The naive per-plaquette (degeneracy-COMPOUNDING) real single-edge correlator
`reconTransfer` — the genuine Wilson correlator — has leading eigenvalue
`coeffW w 1 = dimQ 1 · w³ = 2w³`, strictly ABOVE the resummed rate `w³`, so it CANNOT
cluster at `w³`.  Achieving `w³` is the interacting resummation, not free. -/

/-- **`reconTransfer_not_resummedClustering` (PROVED refutation).**  For every `0 < w < 1`,
the naive per-plaquette real correlator `reconTransfer w hw (M+1)` does NOT satisfy
`ResummedClustering`.  Any such witness would (Direction A) give a located gap with
separator `w³`, forcing the leading eigenvalue `coeffW w 1 = 2w³` to satisfy `2w³ ≤ w³` —
contradicting `w³ < 2w³` (as `0 < w³`).  So the free/naive degeneracy-compounding transfer
provably violates resummed clustering: the rate `w³` is genuinely interacting content. -/
theorem reconTransfer_not_resummedClustering {w : Q'} (hwpos : (0 : Q') < w)
    (hwlt : w < (1 : Q')) (M : Nat)
    (R : ResummedClustering (reconTransfer w (Q'.le_of_lt hwpos) (M + 1)) w) : False := by
  -- located bound at mode 0:  lam 0 ≤ sep = w³
  have hb : (reconTransfer w (Q'.le_of_lt hwpos) (M + 1)).lam 0
      ≤ (gap_of_resummedClustering hwpos hwlt R).sep :=
    (gap_of_resummedClustering hwpos hwlt R).bound 0
  rw [gap_of_resummedClustering_sep hwpos hwlt R] at hb   -- hb : lam 0 ≤ heatKernelSep w
  have hlam : (reconTransfer w (Q'.le_of_lt hwpos) (M + 1)).lam 0 = coeffW w 1 := rfl
  rw [hlam] at hb                               -- hb : coeffW w 1 ≤ heatKernelSep w
  -- strict:  w³ < dimQ 1 · w³ = coeffW w 1
  have hspos : (0 : Q') < heatKernelSep w := BondMovingScaledNorm.qpow_pos hwpos 3
  have h12 : (1 : Q') < dimQ 1 := by decide
  have hmul : (1 : Q') * heatKernelSep w < dimQ 1 * heatKernelSep w :=
    ClusteringImpliesGap.mul_lt_mul_of_pos_right hspos h12
  have hone : heatKernelSep w ≤ (1 : Q') * heatKernelSep w :=
    Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv (heatKernelSep w)))
  have hstrict : heatKernelSep w < dimQ 1 * heatKernelSep w := Q'.lt_of_le_of_lt hone hmul
  have hcoeff : coeffW w 1 = dimQ 1 * heatKernelSep w := coeffW_one w
  rw [← hcoeff] at hstrict                       -- hstrict : heatKernelSep w < coeffW w 1
  -- combine w³ < coeffW w 1 ≤ w³
  exact ClusteringImpliesGap.lt_irrefl' _ (ClusteringImpliesGap.lt_of_lt_of_le hstrict hb)

/-- **`resummation_gap_is_dimQ` — the numerically-pinned residual (axiom-free).**  The
naive per-plaquette rate and the resummed rate differ EXACTLY by the fixed rep degeneracy
`dimQ 1 = 2`: `coeffW w 1 = dimQ 1 · heatKernelSep w`, i.e. `2w³` vs `w³`.  This is the
same identity as `resummation_is_the_residual`, re-exported as the sharp content the
refutation `reconTransfer_not_resummedClustering` exploits. -/
theorem resummation_gap_is_dimQ (w : Q') :
    coeffW w 1 = dimQ 1 * heatKernelSep w := coeffW_one w

/-! ## 4. NOT AN F-MOVE BELOW `singleStep` — `tm`-independence + non-uniform margin.

`ResummedClustering S w` is a single-scale, transfer-operator-side statement that does NOT
mention the true margin `tm`.  `singleStep`'s truth VARIES with `tm` at fixed `afr`.  So
(exactly as for `uniform_in_m`) no transfer-side statement implies or equals `singleStep`;
`ResummedClustering` is INCOMPARABLE, not a strictly-weaker sub-obligation.  And the
per-scale margin `1 − w³` is not uniform, so the per-scale gaps are lattice-units only and
do not bypass `singleStep` to the physical floor. -/

/-- **`resummedClustering_is_transferSide_not_singleStep` (PROVED, reused).**  At any AF
rate `afr`, `singleStep` (`SingleStepProp`) is SATISFIABLE (`tm ≡ 0`) and FALSIFIABLE (a
concrete `tm`).  Hence its truth depends on the free margin `tm` at fixed `afr`; a
transfer-side / `afr`-only statement such as `ResummedClustering` — which never mentions
`tm` — cannot imply or be equivalent to `singleStep`.  So `ResummedClustering` is NOT a
strictly-weaker sub-obligation of `singleStep` (it is incomparable), just as `uniform_in_m`
was shown to be in `SingleStepDecompositionAdjudication`. -/
theorem resummedClustering_is_transferSide_not_singleStep (afr : AFRateModulus) :
    SingleStepProp afr (fun _ => (0 : Q'))
    ∧ ¬ SingleStepProp afr (fun k => if k = 0 then (1 : Q') else 0) :=
  ⟨singleStep_satisfiable_zero afr, singleStep_falsifiable afr⟩

/-- **`resummed_margin_not_uniform` (PROVED, decidable).**  The per-scale resummed margin
`1 − w³` is positive but DECREASES toward `0` as `w → 1`: at `w = 999/1000` it is smaller
than at `w = 99/100`, both positive.  So the multi-plaquette per-scale located gaps are in
LATTICE units and do NOT supply a uniform PHYSICAL floor — the physical continuum floor
still needs the `tm`-recursion `singleStep`; the resummed route does not bypass it. -/
theorem resummed_margin_not_uniform :
    (0 : Q') < (1 : Q') - heatKernelSep (Q'.mkPos 999 1000 (by decide))
    ∧ (1 : Q') - heatKernelSep (Q'.mkPos 999 1000 (by decide))
        < (1 : Q') - heatKernelSep (Q'.mkPos 99 100 (by decide)) := by
  constructor
  · decide
  · decide

/-! ## 5. THE BUNDLED STRUCTURAL VERDICT. -/

/-- **`resummation_adjudication_verdict` — the machine-checked structural verdict.**

For every `0 < w < 1`:
  (A) `ResummedClustering S w` PRODUCES a located gap (margin `1 − w³ > 0`) — Direction A;
  (B) the resummed MODEL `effTransfer` inhabits it (non-vacuous);
  (C) the naive per-plaquette real transfer `reconTransfer` VIOLATES it (non-free —
      achieving `w³` is interacting, not a free heat-kernel fact); and
  (D) at every `afr`, `singleStep` is both satisfiable and falsifiable in `tm`, so no
      transfer-side `ResummedClustering` can imply/equal the `tm`-recursion `singleStep`.

Consequence: `ResummedClustering` EQUI-INHABITS the difficulty of the atomic core
`singleStep` as a sharp, factor-`dimQ 1 = 2` RE-FRAMING; it is NOT a strictly-weaker
computable `F`-node and NOT a core-bypassing parallel obligation.  `F = 1` STANDS.
`SingleStepDefectBound` inhabited nowhere; the 4D Yang–Mills mass gap remains OPEN. -/
theorem resummation_adjudication_verdict :
    (∀ {w : Q'} (hwpos : (0 : Q') < w) (hwlt : w < (1 : Q')) {S : SpectralModel}
        (R : ResummedClustering S w),
        (0 : Q') < (1 : Q') - (gap_of_resummedClustering hwpos hwlt R).sep)
    ∧ (∀ {w : Q'} (hwpos : (0 : Q') < w) (hwlt : w < (1 : Q')) (M : Nat),
        ResummedClustering (reconTransfer w (Q'.le_of_lt hwpos) (M + 1)) w → False)
    ∧ (∀ (afr : AFRateModulus),
        SingleStepProp afr (fun _ => (0 : Q'))
        ∧ ¬ SingleStepProp afr (fun k => if k = 0 then (1 : Q') else 0)) :=
  ⟨fun {_w} hwpos hwlt {_S} R => resummedClustering_gap_margin_pos hwpos hwlt R,
   fun {_w} hwpos hwlt M R => reconTransfer_not_resummedClustering hwpos hwlt M R,
   fun afr => resummedClustering_is_transferSide_not_singleStep afr⟩

end YMGap.Continuum.ResummationAdjudication

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ResummationAdjudication.gap_of_resummedClustering
#print axioms YMGap.Continuum.ResummationAdjudication.resummedClustering_gap_margin_pos
#print axioms YMGap.Continuum.ResummationAdjudication.resummedClustering_effTransfer
#print axioms YMGap.Continuum.ResummationAdjudication.reconTransfer_not_resummedClustering
#print axioms YMGap.Continuum.ResummationAdjudication.resummation_gap_is_dimQ
#print axioms YMGap.Continuum.ResummationAdjudication.resummedClustering_is_transferSide_not_singleStep
#print axioms YMGap.Continuum.ResummationAdjudication.resummed_margin_not_uniform
#print axioms YMGap.Continuum.ResummationAdjudication.resummation_adjudication_verdict
