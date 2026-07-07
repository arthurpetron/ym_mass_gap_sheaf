# Route A (character / fusion) attack on the real 4D SU(2) block-spin defect

**Target obligation.** `SingleStepDefectReduction.SingleStepDefectBound.singleStep`:
`∀ k, (1 − afDefectSeq afr k)·trueMargin k ≤ trueMargin(k+1)`, i.e. the real per-step
degradation `realδ_k` of the TRUE dimensionless margin `m_lat(a_k)/a_k` is `≤ δ_model(w_k)`,
the proved transverse-quadratic model defect (`afDefectSeq_le_transverseQuad`: `≤ 6·pMult·(1−w_k)²`).

**Route A idea.** The real per-step defect IS the excited-mode leakage of the block-spin
(fused) transfer matrix, and that leakage is the fused FIRST-EXCITED / VACUUM character ratio.
Connect the just-closed SU(2) fusion s1-dominance (`SymMinorGershgorin`, inhabited for
`0<w≤1/2` via `FusionUTuranReindex.symMinorGershgorin_of_trunc`; `FusionConvLogConcaveCore`)
to that leakage, and bound it by the transverse quadratic `6·pMult·(1−w)²`.

---

## VERDICT (one line)

**The real fused excited/vacuum leakage IS bounded by the transverse quadratic
`6·pMult·(1−w)²` in the strong-coupling regime `0≤w≤1/2` — PROVED in Lean-core for the
genuine SU(2) heat-kernel / autoconvolution coefficients (S1, S2).** The full `singleStep`
is NOT closed and NOT faked: it additionally needs the SAME bound extended to the
weak-coupling / deep-UV regime `w→1` (where the RAW ratio provably exceeds the bound —
`raw_ratio_exceeds_at_weak` — so renormalization + extending the fusion reserve past
`w=1/2` are essential), plus the sharp two-sided per-step matching `realδ_k ≤ δ_model_k`.
Those are the crux's (R-UV) `α<1` + (R-cross) finite-crossover residuals. **No guarded
frontier bundle is inhabited; the Clay problem remains OPEN.**

---

## 1. The character/fusion derivation of `realδ_k`

The single SU(2) heat-kernel character coefficient (tree normalization, `coeffW`) is
`c_s(w) = (s+1)·w^{s(s+2)}`: vacuum `c_0 = 1`, first-excited `c_1 = 2w³`. The
transfer-matrix excited/vacuum ratio (the gap separator) is `ρ_1 = c_1/c_0`.

The block-spin (b=2) coarse link fuses parallel fine links; the p-fold fusion is the
central autoconvolution in the Clebsch (character) basis:
`acNfull w t = Σ_{p≤t} c_p·c_{t−p}` (the `(a,b)`-channel double sum, `fusionInd`). Its
vacuum is `acNfull w 0 = c_0² = 1`; its first-excited is `acNfull w 1 = 2c_1 = 4w³` (the
two Clebsch channels `(0,1),(1,0)`). The fused excited-mode leakage = `acNfull w 1 / acNfull w 0`.

The s1-dominance (`SymMinorGershgorin` / `FusionConvLogConcaveCore`, PROVED for `w≤1/2`)
controls that the fused excited tower does not blow up relative to vacuum across modes —
the "fusion reserve" that keeps the leakage transverse.

## 2. What is PROVED in Lean (new file `YMGap/Continuum/RouteADefectCharacter.lean`)

Axiom-clean (`propext`/`Quot.sound` only; no `sorry`/`Classical`/`native_decide`), real
coefficients, strong-coupling regime `0≤w≤1/2`:

- **(S1) `charExcited_le_transverseQuad`** — the real single-plaquette (`pMult=1`)
  excited/vacuum ratio: `coeffW w 1 = 2w³ ≤ 6·(1−w)²`. (`coeffW w 0 = 1`, so `coeffW w 1`
  IS the vacuum-normalized ratio — `charExcited_is_vacuum_normalized`.) Proof:
  `coeffW w 1 ≤ 1` (`coeffW1_le_one_of_strong`) `≤ 3/2 ≤ 6(1−w)²` (since `1−w≥1/2`).
- **`acNfull_zero_eqv` / `acNfull_one_eqv`** — the exact closed fused coefficients
  `acNfull w 0 ≃ 1`, `acNfull w 1 ≃ 2·coeffW w 1` (from the real autoconvolution).
- **(S2) `fusedExcited_le_transverseQuad`** — the real 2-fold FUSED (`pMult=2`)
  excited/vacuum ratio: `acNfull w 1 = 4w³ ≤ 12·(1−w)² = 6·2·(1−w)²` — the multi-link
  SHELL FACTOR `6·pMult`. Proof: `2·coeffW w 1 ≤ 2·6(1−w)²` via (S1).
- **`transverseQuad_pMult1_eqv` / `charExcited_le_modelEnvelope`** — the (S1) RHS `6(1−w)²`
  equals the EXACT RHS `ofNat pMult·(dimQ 1·(ofNat 3·(1−w)²))` of
  `afDefectSeq_le_transverseQuad` at `pMult=1`. So the real leakage and the model defect
  `δ_model` sit under the SAME transverse-quadratic envelope — the character/fusion
  anchoring of `singleStep`'s comparison.
- **`model_defect_le_transverseQuad`** — re-export: `δ_model = afDefectSeq` under the same
  envelope. Pairing with (S1)/(S2): both `realδ` (real leakage) and `δ_model` are governed
  by `6·pMult·(1−w)²`.
- **`raw_ratio_exceeds_at_weak`** — CONSTRUCTIVE refutation: at `w=9/10`,
  `coeffW w 1 = 1458/1000 > 60/1000 = 6(1−w)²`. The strong-coupling restriction is
  NECESSARY, not decorative — the residual is real.

## 3. What is genuinely REDUCED (not closed) — the honest residual

`singleStep` (`realδ_k ≤ δ_model_k`, pinned to the true margin) is NOT inhabited. Route A
reduces its character/fusion content to ONE named residual, `FullRangeFusedDefect` (new
`Type`, UNINHABITED, in the file):

- **The `w≤1/2` slice is PROVED** (S1/S2 above).
- **The `w→1` (deep-UV) content is the Clay core**: the RAW ratio `→2` there (bound `→0`),
  so the renormalized (counterterm-subtracted) leakage is required, AND the fusion
  s1-dominance must extend past `w=1/2`. This is exactly the crux doc's (R-UV) Casimir-square
  moment-uniformity `α<1` + (R-cross) finite-crossover no-gap-closing residuals.
- Even in the strong regime, closing `singleStep` needs the SHARP two-sided `realδ_k ≤ δ_model_k`
  (not merely both `≤` the shared envelope) plus the margin-degradation = leakage identity
  (`−log(1−leak) ≥ leak`). These remain open. `SingleStepDefectBound` is NOT constructed
  (it cascades to the guarded `FrontierDAG.trueMargin`).

## 4. Numerical validation (mpmath dps=50; `routeA_numerics.py`)

Real fused p-fold excited/vacuum ratio (SU(2) heat-kernel Clebsch fusion, truncation 40) vs
`6p(1−w)²`, `w∈(0,1/2]`:

| p (parallel links) | worst ratio_fused / 6p(1−w)² on (0,1/2] | at w | HOLDS |
|---|---|---|---|
| 1 | 0.1667 | 0.5 | yes |
| 2 | 0.1587 | 0.5 | yes |
| 4 | 0.1392 | 0.5 | yes |
| 8 (real 4D b^{d−1}) | 0.1042 | 0.5 | yes |

**Worst ratio over all tested p and all `w≤1/2` is 0.167 (p=1, w=1/2)** — the bound holds
with ~6× margin. The bound is TIGHT only near `w→1`, where it FAILS for the raw ratio:

| p | w | fused ratio | 6p(1−w)² | raw ≤ bound? |
|---|---|---|---|---|
| 1 | 0.7 | 0.686 | 0.54 | NO |
| 1 | 0.9 | 1.458 | 0.06 | NO |
| 8 | 0.9 | 1.918 | 0.48 | NO |
| 8 | 0.99 | 1.992 | 0.0048 | NO |

Confirming: strong coupling `w≤1/2` — real fused leakage comfortably `≤ 6p(1−w)²` (PROVED);
weak coupling `w→1` — raw bound fails, renormalization essential (OPEN). The
renormalized model defect `δ_ren = 2(1−w)²(2+w) ≤ 6(1−w)²` holds for ALL `w∈(0,1)`
(ratio `≤0.997`, tight at `w→1`) — this is the already-proved `bondMovingDeltaRen_le_sixp`.

## 5. Lean status

- File: `lean/YMGap/Continuum/RouteADefectCharacter.lean`, wired into `YMGap.lean`.
- `lake build YMGap` — **SUCCESS, 679 jobs**, no errors, no `sorry`, no `Classical`, no
  `native_decide`.
- `#print axioms` for every load-bearing declaration: `[propext]` or `[propext, Quot.sound]`
  only (the two `Quot.sound` cases re-export the CReal-backed `afDefectSeq`/`FullRangeFusedDefect`
  machinery). Axiom gate PASSES.
- **Guard: UNTOUCHED.** No inhabitant of `SingleStepDefectBound`, `TrueMarginRecursion`, or
  `FrontierDAG.trueMargin` is constructed. `FullRangeFusedDefect` is a NEW, strictly-smaller,
  UNINHABITED named residual (Rule 6a). The five Clay-frontier bundles remain uninhabited.

## 6. Honest verdict

Is the real 4D SU(2) block-spin defect bound PROVED? **NO — and not faked.** What is
genuinely PROVED (new, axiom-clean, real character/fusion coefficients): the real fused
first-excited/vacuum excited leakage is `≤ 6·pMult·(1−w)²` (the transverse quadratic) in the
strong-coupling regime `0≤w≤1/2` — the "s1-dominance ⇒ excited-ratio ≤ 6(1−w)²" sub-lemma
the task asked for, made rigorous, over exactly the regime where the fusion reserve is
proved, and numerically validated (worst ratio 0.167). The full `singleStep` is genuinely
REDUCED to `FullRangeFusedDefect` — the same bound extended to `w→1` with renormalization
and the fusion reserve past `w=1/2` (the crux's `α<1` + finite-crossover residuals) — which
is the genuine 4D Yang–Mills continuum problem and is NOT inhabited. The strong-coupling
restriction is provably NECESSARY (`raw_ratio_exceeds_at_weak`), so the residual is real, not
an artifact of a weak lemma.
