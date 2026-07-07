/-
Track B / R2 — THE RG-FLOW GAP-PRESERVATION ASSEMBLY, AUDITED:  does the RG flow
DERIVE the continuum gap `Λ > 0` from the PROVED strong-coupling IR anchor + the
PROVED AF summability + the adequacy engine, or is the per-step recursion the
irreducible residual?

# The question (the deepest reduction)

The RG flow runs from the IR (fixed spacing `a_0`, strong coupling, PROVED located
gap `1 − rho = 107/108`, `ClayScorecard.clay_fixed_spacing_met`) to the UV
(`a_k = a_0 b^{−k} → 0`, `w_k → 1`, asymptotic freedom).  The dimensionless margin
`trueMargin k = m_lat(a_k)/a_k`.  Assemble:

  * IR anchor            `0 < trueMargin 0`                       (PROVED: 107/108)
  * summability / floor  `∏(1 − δ_model_k) > 0`, `Σ δ_model < ∞`  (PROVED)
  * adequacy engine      telescoping ⟹ uniform positive floor     (PROVED, pure `Q'`)
  * the RECURSION        `(1 − δ_model_k)·trueMargin k ≤ trueMargin (k+1)`   (?)

`fullFloor_of_singleStep` shows the first three PROVED pieces + the recursion give
the entire positive continuum floor for the true margin.  So the ENTIRE remaining
input is the recursion `singleStep`.  This module packages that assembly explicitly
and audits, adversarially, the EXACT status of the recursion.

# The verdict (maximally adversarial, machine-checked)

**The RG flow does NOT derive gap-preservation.**  The assembly is complete EXCEPT
for one field, `SingleStepDefectBound.singleStep`, and that field is the genuine
irreducible residual — it is NOT proved.

`singleStep` is `realδ_k ≤ δ_model_k`:  the REAL 4D non-abelian multi-link
block-spin per-step defect of the true margin is bounded by the transverse quadratic
MODEL defect `δ_model = afDefectSeq`.  The MODEL side is PROVED — `δ_model` is
nonneg, `< 1`, summable, product-floor-positive, and `≤ 6·pMult·(1 − w)²`
(`model_defect_is_proved_transverse`, reusing `afDefectSeq_le_transverseQuad`).  What
is OPEN is that the REAL erosion is no worse than this proved model.  That is the
interacting-measure / fusion-local-CLT input (the earlier residuals), i.e. a per-step
form of the non-perturbative condensate positivity.  It is NOT a "small-erosion upper
bound that is provable": the summable/anchor-dominated smallness that IS proved is the
smallness of the MODEL `δ_model`, whereas `realδ ≤ δ_model` is a statement about the
real interacting theory, uninhabited.

Hence the campaign's proved pieces are:
  (a) the IR anchor `107/108`                  — PROVED (`clay_fixed_spacing_met`);
  (b) the AF summability + product floor        — PROVED;
  (c) the telescoping adequacy (floor from step) — PROVED (pure `Q'`);
  (d) the per-step recursion `realδ ≤ δ_model`  — **OPEN, the irreducible residual**.

`Λ > 0` does NOT assemble from (a)+(b)+(c) alone: (d) is required and is the genuine
4D Yang–Mills continuum input.  `SingleStepDefectBound` is NOT inhabited (per the
`CAPSTONE §4` caveat it is a bound on a free function field, hence vacuously fakeable
by a constant `trueMargin ≡ c`; that fake is REFUSED, and — being a per-step form of
the interacting-measure control — its genuine instance for the physical margin is
open).

# Guard / STOP

This module produces ONLY CONDITIONAL theorems (open binder `S : SingleStepDefectBound`
or open recursion hypotheses).  It inhabits NONE of the 5 guarded frontier types
(`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`,
`FrontierDAG`).  No STOP condition is tripped; the 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`; every load-bearing declaration gated with `#print axioms`; permitted
output `propext` / `Quot.sound`.  No `Classical.*`, no `native_decide`, no `sorry`.
Reuses only PROVED lemmas (`fullFloor_of_singleStep`, `afDefectSeq_le_transverseQuad`).
-/
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.RGFlowGapAssembly

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 1. THE ASSEMBLY — IR anchor + summability + adequacy + recursion ⟹ `Λ > 0`.

Given the single per-step recursion carrier `S : SingleStepDefectBound`, the IR
anchor `0 < trueMargin 0`, the uniform positive continuum floor, and the uniform
lower bound of the true margin by that floor at EVERY scale, all hold together — the
whole RG-flow gap-preservation packaged in one statement.  The floor and bound are
`fullFloor_of_singleStep` (which internally uses only the PROVED model summability +
product floor + the recursion `S.singleStep`); the IR anchor is `S.trueMargin0_pos`. -/
theorem rgFlow_gap_from_singleStep (S : SingleStepDefectBound) :
    (0 : Q') < S.trueMargin 0
      ∧ (0 : Q') < (defectRecursion_of_singleStep S).prodFloor
      ∧ ∀ k : Nat, (defectRecursion_of_singleStep S).prodFloor ≤ S.trueMargin k :=
  ⟨S.trueMargin0_pos, fullFloor_of_singleStep S⟩

/-- **The positive continuum floor is the STRONG-COUPLING product floor scaled by the
IR anchor.**  `prodFloor = afFloorEps · trueMargin 0 > 0` — the PROVED positive
survival-product floor `afFloorEps > 0` (from AF summability) times the PROVED IR
anchor `trueMargin 0 = 107/108`.  This exhibits `Λ ≥ prodFloor` as the product of two
PROVED-positive quantities — GIVEN the recursion `S.singleStep`. -/
theorem continuum_floor_pos (S : SingleStepDefectBound) :
    (0 : Q') < (defectRecursion_of_singleStep S).prodFloor :=
  (fullFloor_of_singleStep S).1

/-! ## 2. THE MODEL SIDE IS PROVED — the residual is `realδ ≤ δ_model`, nothing else. -/

/-- **The MODEL per-step defect is the PROVED transverse quadratic.**  `δ_model_k =
afDefectSeq S.afr k ≤ 6·pMult·(1 − w_k)²` (`= pMult · dimQ 1 · 3 · (1 − w)²`).  So the
model erosion is genuinely small and its summability/product-floor are proved.  This
pins the OPEN content of the recursion to exactly `realδ_k ≤ δ_model_k`
(`S.singleStep`), NOT to any property of the model itself. -/
theorem model_defect_is_proved_transverse (S : SingleStepDefectBound) (k : Nat) :
    afDefectSeq S.afr k
      ≤ Q'.ofNat pMult * (dimQ 1 * (Q'.ofNat 3 *
          (((1 : Q') - S.afr.w (afCutoff S.afr + k))
            * ((1 : Q') - S.afr.w (afCutoff S.afr + k))))) :=
  afDefectSeq_le_transverseQuad S.afr k

/-! ## 3. THE RESIDUAL, ISOLATED — the recursion is the ONLY open input.

`rgFlow_gap_conditional` states the continuum floor as a function of the recursion
hypothesis ALONE, with every other ingredient (anchor positivity, model defect
nonneg/`≤1`, product floor) supplied by PROVED lemmas via `defectRecursion_of_singleStep`.
The hypotheses are exactly: (i) the IR anchor `0 < trueMargin 0`, and (ii) the per-step
recursion.  There is no third open input — confirming the recursion is the sole residual. -/
theorem rgFlow_gap_conditional
    (afr : AFRateCalibration.AFRateModulus) (trueMargin : Nat → Q')
    (hAnchor : (0 : Q') < trueMargin 0)
    (hRecursion : ∀ k : Nat,
      (1 - afDefectSeq afr k) * trueMargin k ≤ trueMargin (k + 1)) :
    (0 : Q') < (defectRecursion_of_singleStep
        { afr := afr, trueMargin := trueMargin
          trueMargin0_pos := hAnchor, singleStep := hRecursion }).prodFloor
      ∧ ∀ k : Nat, (defectRecursion_of_singleStep
        { afr := afr, trueMargin := trueMargin
          trueMargin0_pos := hAnchor, singleStep := hRecursion }).prodFloor
        ≤ trueMargin k :=
  fullFloor_of_singleStep
    { afr := afr, trueMargin := trueMargin
      trueMargin0_pos := hAnchor, singleStep := hRecursion }

/-! ## 4. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **PROVED (axiom-clean):**
  * `rgFlow_gap_from_singleStep` — the full assembly: IR anchor + PROVED
    summability/adequacy + the recursion ⟹ uniform positive continuum floor for the
    true margin.
  * `continuum_floor_pos` — `Λ ≥ prodFloor = afFloorEps · trueMargin 0 > 0`
    (product of two PROVED-positive quantities), GIVEN the recursion.
  * `model_defect_is_proved_transverse` — the MODEL per-step defect `δ_model` is the
    PROVED transverse quadratic `≤ 6·pMult·(1 − w)²`.
  * `rgFlow_gap_conditional` — the continuum floor as a function of the recursion
    hypothesis ALONE, exhibiting it as the SOLE open input.

**VERDICT.**  The RG flow does NOT DERIVE gap-preservation from the proved pieces.
The IR anchor (`107/108`, `clay_fixed_spacing_met`), the AF summability / product
floor, and the telescoping adequacy engine are ALL PROVED — but they assemble `Λ > 0`
ONLY GIVEN the per-step recursion `singleStep : realδ_k ≤ δ_model_k`.  That recursion
is the genuine irreducible residual: it asserts the REAL 4D non-abelian multi-link
block-spin erosion is bounded by the proved transverse quadratic MODEL, which is the
interacting-measure / fusion-local-CLT input (a per-step form of the non-perturbative
condensate positivity).  It is NOT a provable smallness bound — the proved smallness is
of the MODEL `δ_model`; `realδ ≤ δ_model` is a statement about the real interacting
theory and is UNINHABITED.  `SingleStepDefectBound` is NOT inhabited (its constant-margin
fake is refused).  No guarded bundle is inhabited; nothing is faked; the 4D Yang–Mills
mass gap remains OPEN. -/
theorem rgFlowGapAssembly_honesty : True := trivial

end YMGap.Continuum.RGFlowGapAssembly

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RGFlowGapAssembly.rgFlow_gap_from_singleStep
#print axioms YMGap.Continuum.RGFlowGapAssembly.continuum_floor_pos
#print axioms YMGap.Continuum.RGFlowGapAssembly.model_defect_is_proved_transverse
#print axioms YMGap.Continuum.RGFlowGapAssembly.rgFlow_gap_conditional
