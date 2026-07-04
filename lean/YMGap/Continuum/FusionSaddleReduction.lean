/-
Track 11.7-fusion / R2 — **the honest CG-fusion ↔ additive-convolution reduction of the
`p = 2` saddle eigenvalue-shift `bulkShiftBound` onto the Tier-0 curvature datum
`XMeanSecondDiffLeOne`, gated behind two sharply-named bridge residuals.**

# What this module does (read first — load-bearing honesty)

`FusionKernelStatement.SaddleLocalCLT.bulkShiftBound` (the vacuum-normalized fusion
eigenvalue-shift `fusionEig N w p s − eigA w s ≤ 1/12`) is the single discrete SU(2)
fusion local-CLT residual on the mass-gap δ-loop critical path.  The Tier-0 route
(`MeanExpConvexProgress` / `XMeanSecondDiffProgress`) built a parallel curvature ladder
(`mu_eq`, `casimir_secondDiff_eq_two`, `XMeanSecondDiffLeOne : d2x ≤ 1`) — but that
ladder lives entirely on the ADDITIVE diagonal autoconvolution `acN w (s+1) s`, NOT on
the Clebsch–Gordan-truncated fusion coefficient `bondMovedCoeff N w 2 s = fusionPow …`.

**The honest finding (verified against the object definitions):** the fusion
`bulkShiftBound` does NOT reduce to the Tier-0 residual by instantiation.  Two
independent gaps block a mechanical rewrite:

  * **Object gap** — the saddle side carries the CG indicator `fusionInd`
    (`|a−b| ≤ s ≤ a+b`, parity), while the Tier-0 machinery (`mu_eq`, `xmomN`,
    `acnFmom`) is built on the plain additive convolution `acN`.  No lemma equates
    `bondMovedCoeff N w 2` with `acN`; the two coincide only in the untruncated
    additive limit.  This is a MISSING NAMED coordinate identity.
  * **Differential-order gap** — `bulkShiftBound` is a POINTWISE first-order shift;
    `XMeanSecondDiffLeOne` is a SECOND-difference (curvature) bound.  Curvature →
    pointwise-shift needs a discrete double summation anchored at the `s = 0` vacuum
    tie — an analytic step, not algebra.

So this module does the ONLY sound thing: it **relocates** `bulkShiftBound` (at the
genuine 4D exponent `p = 2`) onto Tier-0 *plus two new named-open residuals*, and
proves the composition genuinely (axiom-clean `Q'`).  It does NOT claim closure, and it
does NOT inhabit any residual.

# The two named bridge residuals (NAMED-OPEN, never inhabited)

  * `FusionAdditiveBridge N w` — **the sharp missing coordinate identity**: at `p = 2`,
    the CG-truncated fusion coefficient equals the additive autoconvolution,
    `bondMovedCoeff N w 2 s ≃ acN w (s+1) s` for every mode.  This is the object that a
    "CG-fusion = additive-conv modulo truncation" comparison would supply; it is a
    discrete-local-CLT-depth research step, left UNINHABITED.
  * `CurvatureToShift N w` — **the curvature ⟹ pointwise-shift anchor integration**:
    the (additive-coordinate) integrated form of the Tier-0 second-difference bound,
    `acN w (s+1) s ≤ (eigA w s + 1/12)·(dimQ s · bmc(0))`, produced FROM a
    `XMeanSecondDiffLeOne w` witness.  This carries the discrete double summation /
    vacuum-anchor content that turns a curvature bound into a pointwise shift; also
    UNINHABITED.

# What is PROVED here (axiom-clean `Q'`)

  * `fusionEig_p2_le_of_bridge` — the GENUINE transport: given the coordinate bridge,
    any additive-coordinate upper bound `acN w (s+1) s ≤ C·denom` transports to the
    fusion eigenvalue `fusionEig N w 2 s ≤ C` (`divPos_le_of_le_mul` after rewriting the
    numerator along the bridge).  This is the piece that makes the additive-coordinate
    Tier-0 estimate BEAR on the fusion object.
  * `bulkShiftBound_p2_of_tier0` — THE REDUCTION: from a `FusionAdditiveBridge`, a
    Tier-0 `XMeanSecondDiffLeOne`, and a `CurvatureToShift`, the `p = 2` wiring carrier
    `SaddleLocalCLT N w 2` is inhabited (its open field `bulkShiftBound` discharged by
    transport + `sub_le_of_le_add`).  All three inputs are named-open; the conclusion is
    therefore NOT unconditional.
  * `gap_reduction_p2_of_tier0` — the composite: the reduction reaches the δ-loop
    capstone `DeltaFrontierLedger.GapReductionConclusion` (through the existing
    `FusionKernelStatement.saddle_gap_reduction`), showing the two bridges plus Tier-0
    close the whole critical path at `p = 2`.

# What is NAMED-OPEN (NOT inhabited, NOT faked)

  * `FusionAdditiveBridge N w`, `CurvatureToShift N w` — the two new bridge residuals.
  * `MeanExpConvexProgress.XMeanSecondDiffLeOne w` — the pre-existing Tier-0 curvature
    datum (`d2x ≤ 1`, tight at the even-`s`, `w → 0` two-point tie).
  * The GENERAL `p ≥ 2` exponent — even the additive `mu_eq` has no `p`-body analogue,
    so this reduction is genuinely `p = 2` only; general `p` remains the irreducible
    discrete SU(2) fusion local-CLT core.

# HONEST VERDICT

A sharp RELOCATION + genuine transport machinery, NOT a closure.  The `p = 2` fusion
`bulkShiftBound` is factored through Tier-0 `XMeanSecondDiffLeOne` PLUS two named-open
bridges (`FusionAdditiveBridge`, `CurvatureToShift`); both new residuals and the Tier-0
datum saturate at the SAME even-`s`, `w → 0` corner, so the local-CLT crux is moved, not
removed.  General `p ≥ 2` is untouched.  The Clay Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` order/`eqv` arithmetic (`divPos_le_of_le_mul`, `le_of_eqv`, `le_trans'`,
`sub_le_of_le_add`) plus composition over the already-green δ-loop engine.  Every
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.  All
witnesses are `Type`-level data; the two new bridges are named uninhabited interfaces.
-/

import YMGap.Continuum.FusionKernelStatement
import YMGap.Continuum.MeanExpConvexProgress

namespace YMGap.Continuum.FusionSaddleReduction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.MeanExpConvexProgress
open YMGap.Continuum.FusionKernelStatement

/-! ## 1. The two named bridge residuals (NAMED-OPEN, never inhabited) -/

/-- **`FusionAdditiveBridge N w` — the sharp missing coordinate identity.**  At the
genuine 4D exponent `p = 2`, the Clebsch–Gordan-TRUNCATED fusion coefficient
`bondMovedCoeff N w 2 s = fusionPow N (coeffW w) 2 s` (carrying the CG indicator
`fusionInd`) equals the ADDITIVE diagonal autoconvolution `acN w (s+1) s =
Σ_{p<s+1} coeffW w p · coeffW w (s−p)` on which the Tier-0 curvature ladder
(`mu_eq`, `xmomN`, `acnFmom`) is built.  The two objects coincide only in the
untruncated additive limit, so this equality is a genuine "CG-fusion = additive-conv
modulo truncation" comparison — a discrete-local-CLT-depth research step.  NAMED-OPEN
(never `sorry`, never inhabited). -/
structure FusionAdditiveBridge (N : Nat) (w : Q') : Type where
  /-- The `p = 2` CG ↔ additive coordinate identity, per mode. -/
  bmc2_eq_acN : ∀ s, (bondMovedCoeff N w 2 s).eqv (acN w (s + 1) s)

/-- **`CurvatureToShift N w` — the curvature ⟹ pointwise-shift anchor integration.**
The Tier-0 datum `XMeanSecondDiffLeOne w` is a SECOND-difference (curvature) bound
`d2x ≤ 1`; the fusion residual needs a POINTWISE first-order shift.  This structure
carries the analytic step that integrates the former into the latter, IN ADDITIVE
COORDINATES: from a `XMeanSecondDiffLeOne w` witness it produces the per-mode
autoconvolution shift bound

    acN w (s+1) s  ≤  (eigA w s + 1/12) · (dimQ s · bondMovedCoeff N w 2 0),

i.e. the additive-coordinate form of `fusionEig − eigA ≤ 1/12` PRIOR to the CG
transport.  The discrete double summation anchored at the `s = 0` vacuum tie lives
here.  NAMED-OPEN (never `sorry`, never inhabited). -/
structure CurvatureToShift (N : Nat) (w : Q') : Type where
  /-- Curvature (`XMeanSecondDiffLeOne`) integrated to the additive-coordinate pointwise
  shift bound. -/
  shiftBound : XMeanSecondDiffLeOne w →
    ∀ s, acN w (s + 1) s
        ≤ (eigA w s + q112) * (dimQ s * bondMovedCoeff N w 2 0)

/-! ## 2. The genuine transport lemma (PROVED) -/

/-- **`fusionEig_p2_le_of_bridge` — the transport that makes the additive estimate bear
on the fusion object.**  Given the coordinate bridge `B` (`bmc(2,s) ≃ acN(s+1,s)`), any
additive-coordinate upper bound `acN w (s+1) s ≤ C · (dimQ s · bmc(0))` transports to
the vacuum-normalized fusion eigenvalue: `fusionEig N w 2 s ≤ C`.  Rewrite the numerator
`bmc(2,s)` along the bridge, then `divPos_le_of_le_mul`. -/
theorem fusionEig_p2_le_of_bridge {N : Nat} {w : Q'}
    (B : FusionAdditiveBridge N w) (s : Nat) {C : Q'}
    (h0' : (0 : Q') < dimQ s * bondMovedCoeff N w 2 0)
    (hle : acN w (s + 1) s ≤ C * (dimQ s * bondMovedCoeff N w 2 0)) :
    fusionEig N w 2 s h0' ≤ C := by
  show Q'.divPos (bondMovedCoeff N w 2 s) (dimQ s * bondMovedCoeff N w 2 0) h0' ≤ C
  have hbmc : bondMovedCoeff N w 2 s ≤ C * (dimQ s * bondMovedCoeff N w 2 0) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (B.bmc2_eq_acN s)) hle
  exact Q'.divPos_le_of_le_mul _ _ h0' hbmc

/-! ## 3. THE REDUCTION (PROVED composition; conditional on three named-open inputs) -/

/-- **`bulkShiftBound_p2_of_tier0` — THE REDUCTION.**  From
  * `B  : FusionAdditiveBridge N w`  (the CG ↔ additive coordinate identity, `p = 2`),
  * `H  : XMeanSecondDiffLeOne w`    (the Tier-0 curvature datum, `d2x ≤ 1`), and
  * `Anc : CurvatureToShift N w`     (curvature ⟹ additive pointwise shift),
the `p = 2` wiring carrier `SaddleLocalCLT N w 2` is inhabited: its load-bearing open
field `bulkShiftBound` is discharged by transporting `Anc.shiftBound H s` through the
bridge (`fusionEig_p2_le_of_bridge`) and rearranging (`sub_le_of_le_add`).  ALL THREE
inputs are named-open, so this does NOT unconditionally inhabit `SaddleLocalCLT`; it is
the honest relocation of the `p = 2` fusion residual onto Tier-0 + two bridges.  The
moduli `A`, `eta` are neutral placeholder DATA (the genuine leading exponent `−log w`
lives at the `CReal` level and is not needed for the `Q'`-level shift). -/
def bulkShiftBound_p2_of_tier0 {N : Nat} {w : Q'}
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w 2 0)
    (B : FusionAdditiveBridge N w)
    (H : XMeanSecondDiffLeOne w)
    (Anc : CurvatureToShift N w) :
    SaddleLocalCLT N w 2 h0' where
  A := 0
  eta := 0
  bulkShiftBound := fun s => by
    have hle : acN w (s + 1) s
        ≤ (eigA w s + q112) * (dimQ s * bondMovedCoeff N w 2 0) :=
      Anc.shiftBound H s
    have hE : fusionEig N w 2 s (h0' s) ≤ eigA w s + q112 :=
      fusionEig_p2_le_of_bridge B s (h0' s) hle
    -- goal: fusionEig − eigA ≤ 1/12, i.e. fusionEig + -(eigA) ≤ 1/12
    exact Q'.sub_le_of_le_add hE

/-- **`gap_reduction_p2_of_tier0` — the composite reaches the δ-loop capstone.**  The
`p = 2` reduction, chained through `FusionKernelStatement.saddle_gap_reduction`, yields
the full δ-loop `GapReductionConclusion` for the bond-moved bulk spectrum `fusionEig`.
So the two named bridges (`FusionAdditiveBridge`, `CurvatureToShift`) plus the Tier-0
datum `XMeanSecondDiffLeOne` close the entire mass-gap δ-loop critical path AT `p = 2`. -/
theorem gap_reduction_p2_of_tier0 {N : Nat} {w : Q'}
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w 2 0)
    (B : FusionAdditiveBridge N w)
    (H : XMeanSecondDiffLeOne w)
    (Anc : CurvatureToShift N w)
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hN : 1 ≤ N)
    (hnc : (1 : Q') - w ≤ q112) :
    DeltaFrontierLedger.GapReductionConclusion N w 2
      (saddleToLocalization h0' (bulkShiftBound_p2_of_tier0 h0' B H Anc) hnc).eig' :=
  saddle_gap_reduction h0' (bulkShiftBound_p2_of_tier0 h0' B H Anc)
    hw0 hw1 hN (by decide) hnc

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `fusionEig_p2_le_of_bridge` — the CG-transport of an additive-coordinate upper
    bound onto the fusion eigenvalue.
  * `bulkShiftBound_p2_of_tier0` — THE REDUCTION: `FusionAdditiveBridge` +
    `XMeanSecondDiffLeOne` + `CurvatureToShift` ⟹ `SaddleLocalCLT N w 2` (`p = 2`).
  * `gap_reduction_p2_of_tier0` — the composite into the δ-loop capstone.

NAMED OPEN (Type-level structure, never `sorry`, never inhabited):
  * `FusionAdditiveBridge N w` — the CG ↔ additive coordinate identity (`p = 2`).
  * `CurvatureToShift N w` — curvature ⟹ additive pointwise shift (the vacuum-anchor
    double-summation content).
  * `MeanExpConvexProgress.XMeanSecondDiffLeOne w` — the pre-existing Tier-0 curvature
    datum (`d2x ≤ 1`, corner-tight).

HONESTY NOTE (why this is NOT the requested "collapse to Tier-0 by instantiation").
The saddle side (`bondMovedCoeff = fusionPow`, CG indicator `fusionInd`) and the Tier-0
machinery (`acN`, `mu_eq`, `xmomN`) are DIFFERENT objects that agree only in the
untruncated additive limit, and `bulkShiftBound` (pointwise, first-order) is a lower
differential order than `XMeanSecondDiffLeOne` (second difference).  Hence NO mechanical
rewrite exists; the two bridge residuals above are exactly the two missing steps, each a
discrete-local-CLT-depth research item.  General `p ≥ 2` is untouched (the additive
`mu_eq` has no `p`-body analogue).

HONEST VERDICT.  A sharp relocation + genuine transport machinery, NOT a closure.  The
Clay Yang–Mills mass gap remains OPEN (reduction mode). -/

end YMGap.Continuum.FusionSaddleReduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionSaddleReduction.fusionEig_p2_le_of_bridge
#print axioms YMGap.Continuum.FusionSaddleReduction.bulkShiftBound_p2_of_tier0
#print axioms YMGap.Continuum.FusionSaddleReduction.gap_reduction_p2_of_tier0
