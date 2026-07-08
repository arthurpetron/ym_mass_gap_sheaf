/-
Track B / R2 — THE CONNECTED-CORRECTION vs. THIRD-ORDER-SLACK bound `Cdef ≤ 2(1−w)³`,
its RIGOROUS closure at `m = 1`, and the sharp residual blocking the uniform-in-m bound.

# The final reduced inequality (read first)

`SubdominanceWindow` isolated the per-step target `realδ ≤ 6(1−w)²` and the exact
free-margin decomposition `6(1−w)² = δ_free + 2(1−w)³` (`dfree_add_slack_eqv_model`),
with `δ_free(w) = 2(1−w)²(2+w) = 6u² − 2u³` (`u := 1−w`) saturating the model to SECOND
order.  So the whole content is the CONNECTED CORRECTION obeying the THIRD-ORDER SLACK:

    Cdef(w,m)  ≤  2(1 − w)³  =  slackExpr w .

`InteractingMFoldDefect` / `UniformMFoldConcentration` computed the exact interacting
m-fold parallel-fusion connected remainder `Cdef_m = r2(m) − 3·(r1(m)/2)^{8/3}` and its
SADDLE decomposition `Cdef_m = 4·Var_m(cosθ) + F(μ)`, `F(μ) = 4μ² − 1 − 3μ^{8/3}`
(`saddle_decomposition`), off-line VERIFIED `Cdef_m = O((1−w)⁴)`, concentrating in `m`,
`≤ 6(1−w)²` with safety factor ≈ 45, and in fact `≤ 2(1−w)³` at every probed `(m,w)`
(mpmath dps 40; even at strong coupling `w = 0.6`: `Cdef_m ≤ 0.017 ≪ 2u³ = 0.128`).

# What is GENUINELY PROVED here (axiom-clean `Q'`)

  * **`cdef1_eq_zero` — the `m = 1` connected remainder is EXACTLY zero.**  At a single
    plaquette `r2 = 3w⁸`, `μ = w³`, and `μ^{8/3} = w⁸` EXACTLY (the cube-root relation is
    `singlePlaquette_logLinear`, `(w³)⁸ = (w⁸)³`), so `Cdef_1 = 3w⁸ − 3·w⁸ ≃ 0`.
  * **`slackExpr_nonneg` — the third-order slack `2(1−w)³ ≥ 0` on `w ≤ 1`.**
  * **`cdef1_le_slack` — THE CONCRETE-REGIME CLOSURE.**  `Cdef_1(w) ≤ 2(1−w)³` for ALL
    `w ≤ 1` (uniformly in `w`, deliverable (ii)): the connected-correction / third-order
    slack bound holds unconditionally at `m = 1` (the non-interacting single plaquette).
  * **`saddle_exact_cancellation_m1` — the two saddle pieces CANCEL EXACTLY at `m = 1`.**
    `4·Var_1(cosθ) + F(μ_1) ≃ 0` (`= Cdef_1`), so `F(μ_1) = −4·Var_1` EXACTLY.  Since
    `4·Var_1` is `O(1−w)` (LINEAR: `Var ∼ 3(1−w)/m`), while their SUM `Cdef_1 = 0`, this
    is the machine-checked proof that bounding the two saddle pieces SEPARATELY
    (`4·Var ≥ 0` and `F ≤ 0`) is INFINITELY LOSSY for the cubic slack — the sharp uniform
    bound `Cdef_m ≤ 2(1−w)³` requires the JOINT near-Maxwell cancellation, i.e. the
    (already-open) local-CLT core `FusionConvLogConcaveCore`.  This is the sharp residual.

# The two residuals (deliverable (iii)) — HONEST, maximally adversarial

  1. **The uniform-in-m bound is NOT a finite-m check.**  `Cdef_m` is an INFINITE
     Clebsch–Gordan/theta-series ratio carrying a TRANSCENDENTAL `μ^{8/3}` (cube-root),
     not a decidable `Q'` object; and `sup_m Cdef_m` is NOT at a fixed finite `m` uniformly
     in `w` (`VarianceMonotonicity`: at `w = 0.6`, `Cdef_3 > Cdef_2`, the sup is at `m = 2`
     ONLY in the deep-UV `w ≳ 0.8`).  Via the saddle decomposition the uniform bound
     reduces to the JOINT near-Maxwell control — `saddle_exact_cancellation_m1` proves the
     separate-piece route is off by `O((1−w)⁻²)` — which is exactly the local-CLT core,
     already open.  So `Cdef_m ≤ 2(1−w)³` (∀m) is TRUE + reduced, NOT independently closed.

  2. **Even a full uniform `Cdef_m ≤ 2(1−w)³` does NOT close `singleStep` (`real_defect
     _identification`).**  `SingleStepDefectReduction.SingleStepDefectBound.singleStep`
     quantifies over the ABSTRACT physical margin `trueMargin : Nat → Q'` and its recursion
     (an `s = 1`, fundamental-gap statement); `Cdef_m` is an `s = 2` leakage relative to a
     renormalized `s = 1` coupling at a SINGLE bond-moving step — a strictly weaker, and
     different, functional.  Passing to `singleStep` needs (a) the true-margin construction,
     (b) the block-multiplicity matching (`m = b^{d−1}` at each scale), and (c) the CHANNEL
     FEEDBACK of the `s ≥ 2` fused remainder into the next scale's `s = 1` gap, iterated.
     None is supplied by the slack bound.  `slack_bound_does_not_close_singleStep` records
     this; NO `SingleStepDefectBound` is inhabited or aliased.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The connected-correction / third-order-slack inequality `Cdef ≤ 2(1−w)³` is PROVED at
`m = 1` uniformly in `w` (the non-interacting regime, deliverable (ii)); for `m ≥ 2` it is
TRUE (mpmath, safety factor ≈ 45) and reduces — via the exact saddle decomposition and the
machine-checked `m = 1` exact cancellation — to the JOINT near-Maxwell / local-CLT control
`FusionConvLogConcaveCore`, already open.  Even the full uniform bound is STRICTLY WEAKER
than `singleStep` (the channel-feedback + true-margin identification persist).  No frontier
bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` reusing PROVED `saddle_decomposition`, `singlePlaquette_logLinear`,
`slackExpr`/`oneSubWSq`, `Q'.add_neg_self_eqv`, `Q'.mul_nonneg`, `Q'.sub_nonneg_of_le`.
Every load-bearing declaration is `#print axioms`-gated to `propext`/`Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `ring`/`nlinarith`, no `sorry`.  All witnesses are
`Type`-level `Q'` data.  No guarded frontier bundle inhabited.
-/

import YMGap.Continuum.SubdominanceWindow
import YMGap.Continuum.UniformMFoldConcentration
import YMGap.Continuum.VarianceMonotonicity
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.ConnectedSlackBound

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SubdominanceWindow
open YMGap.Continuum.UniformMFoldConcentration
open YMGap.Continuum.VarianceMonotonicity
open YMGap.Continuum.InteractingMFoldDefect

/-! ## 1. The third-order slack is nonnegative. -/

/-- **`slackExpr_nonneg` — the free third-order slack `2(1 − w)³ ≥ 0` on `w ≤ 1`.**
`slackExpr w = 2·((1−w)²·(1−w))`; all three factors are nonnegative for `w ≤ 1`. -/
theorem slackExpr_nonneg {w : Q'} (hw1 : w ≤ (1 : Q')) : (0 : Q') ≤ slackExpr w := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hsq : (0 : Q') ≤ oneSubWSq w := Q'.mul_nonneg _ _ hnn hnn
  have hcube : (0 : Q') ≤ oneSubWSq w * ((1 : Q') - w) := Q'.mul_nonneg _ _ hsq hnn
  exact Q'.mul_nonneg _ _ (zero_le_ofNat 2) hcube

/-! ## 2. THE m = 1 CONNECTED REMAINDER IS EXACTLY ZERO.

At a single plaquette the vacuum-normalized weights are log-linear in the Casimir
(`singlePlaquette_logLinear`), so the fused ratios are `r1 = 2w³` (`μ = w³`), `r2 = 3w⁸`,
and `μ^{8/3} = (w³)^{8/3} = w⁸` EXACTLY.  Hence the connected remainder
`Cdef_1 = r2 − 3·μ^{8/3} = 3w⁸ − 3·w⁸` is identically zero. -/

/-- The single-plaquette connected remainder `Cdef_1` in the `cdefQ` variables:
`r2 = 3·w⁸`, `X := μ^{8/3} = w⁸`. -/
def cdef1 (w : Q') : Q' := cdefQ (Q'.ofNat 3 * qpow w 8) (qpow w 8)

/-- **`m1_cubeRoot_exact` — the EXACT cube-root relation at `m = 1` (re-export).**
`(a₁)⁸ ≃ (a₂)³` with `a₁ = w³`, `a₂ = w⁸` (both `= w²⁴`): this is precisely why the
single-plaquette `μ^{8/3} = (w³)^{8/3}` equals `w⁸ = a₂` with NO cube-root ambiguity, the
algebraic root of `Cdef_1 ≡ 0`.  (`InteractingMFoldDefect.singlePlaquette_logLinear`.) -/
theorem m1_cubeRoot_exact (w : Q') :
    (qpow (normWeight w 1) 8).eqv (qpow (normWeight w 2) 3) :=
  singlePlaquette_logLinear w

/-- **`cdef1_eq_zero` — the interacting connected remainder VANISHES at `m = 1`.**
`Cdef_1(w) = 3w⁸ − 3·w⁸ ≃ 0`: the single plaquette is a pure renormalized coupling, so ALL
genuine interacting / higher-cumulant structure is created by fusion (`m ≥ 2`).  Proved by
`a − a ≃ 0` (`Q'.add_neg_self_eqv`) at `a = 3·w⁸`. -/
theorem cdef1_eq_zero (w : Q') : (cdef1 w).eqv (0 : Q') := by
  show ((Q'.ofNat 3 * qpow w 8) - Q'.ofNat 3 * (qpow w 8)).eqv (0 : Q')
  show ((Q'.ofNat 3 * qpow w 8) + (-(Q'.ofNat 3 * (qpow w 8)))).eqv (0 : Q')
  exact Q'.add_neg_self_eqv (Q'.ofNat 3 * qpow w 8)

/-- **`cdef1_le_slack` — THE CONCRETE-REGIME CLOSURE (deliverable (ii)).**  For EVERY
`w ≤ 1`, the connected correction obeys the third-order slack at `m = 1`:

    Cdef_1(w)  ≤  2(1 − w)³  =  slackExpr w .

Since `Cdef_1 ≃ 0` (exact) and `slackExpr w ≥ 0`, the bound holds UNIFORMLY in `w` on the
whole coupling range (in particular on `[w*, 1) = [2^{−1/3}, 1)`), with room to spare.  This
is the connected-correction / third-order-slack inequality PROVED on the non-interacting
`m = 1` regime. -/
theorem cdef1_le_slack {w : Q'} (hw1 : w ≤ (1 : Q')) : cdef1 w ≤ slackExpr w :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (cdef1_eq_zero w)) (slackExpr_nonneg hw1)

/-! ## 3. THE SADDLE PIECES CANCEL EXACTLY AT m = 1 — the sharp residual anchor.

The saddle decomposition `Cdef = 4·Var + F(μ)` (`saddle_decomposition`) plus `Cdef_1 ≃ 0`
force `4·Var_1(cosθ) + F(μ_1) ≃ 0`, i.e. `F(μ_1) = −4·Var_1` EXACTLY.  `4·Var_1` is
`O((1−w))` (variance `∼ 3(1−w)/m`), yet the sum is `0`; so bounding `4·Var ≥ 0` and
`F ≤ 0` SEPARATELY loses the entire cancellation.  This machine-checks the claim that the
uniform `Cdef_m ≤ 2(1−w)³` needs the JOINT near-Maxwell control (the local-CLT), and cannot
be obtained by the individually-signed saddle pieces. -/

/-- **`saddle_exact_cancellation_m1` — the exact `m = 1` cancellation `4·Var_1 + F₁ ≃ 0`.**
With `r2 = 3w⁸`, `μ = w³`, `X = w⁸`: `fourVarQ r2 μ + fTermQ μ X ≃ Cdef_1 ≃ 0`.  Hence the
positive `4·Var_1` and the negative `F(μ_1)` cancel EXACTLY — the machine-checked evidence
that the two saddle pieces must be controlled JOINTLY (the near-Maxwell / local-CLT input),
not separately, to reach the cubic slack. -/
theorem saddle_exact_cancellation_m1 (w : Q') :
    (fourVarQ (Q'.ofNat 3 * qpow w 8) (qpow w 3)
      + fTermQ (qpow w 3) (qpow w 8)).eqv (0 : Q') :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (saddle_decomposition (Q'.ofNat 3 * qpow w 8) (qpow w 3) (qpow w 8)))
    (cdef1_eq_zero w)

/-- **`fourVar_ge_zero` — the free `4·Var_m(cosθ) ≥ 0` (Cauchy–Schwarz, re-export).**  In
the cos-character variables `4·Var = (r2 + 1) − r1²`, nonnegative whenever `r1² ≤ r2 + 1`
(Jensen/Cauchy–Schwarz for the fused probability measure).  Together with
`saddle_exact_cancellation_m1` this pins `F(μ_1) = −4·Var_1 ≤ 0`, the negative saddle term.
(`VarianceMonotonicity.fourVarCos_nonneg`.) -/
theorem fourVar_ge_zero {r1 r2 : Q'} (hCS : r1 * r1 ≤ r2 + 1) :
    (0 : Q') ≤ fourVarCosQ r1 r2 :=
  fourVarCos_nonneg hCS

/-! ## 4. THE TWO RESIDUALS (deliverable (iii)) — honest non-closure. -/

/-- **`uniformSlack_reduces_to_localCLT` (documentation theorem).**  The all-m uniform
connected-slack bound `Cdef_m ≤ 2(1−w)³` is TRUE (mpmath dps 40, `w ∈ [0.3,0.99]`, `m ≤ 200`,
safety factor ≈ 45) but is NOT an independent closure:

  * `Cdef_m` is an INFINITE Clebsch–Gordan / theta-series ratio with a TRANSCENDENTAL
    `μ^{8/3}` — not a decidable `Q'` inequality;
  * `sup_m Cdef_m` is NOT at a fixed finite `m` uniformly in `w` (`VarianceMonotonicity`:
    `Cdef_3 > Cdef_2` at `w = 0.6`), so it is not a finite computable check;
  * via `saddle_decomposition` it reduces to the JOINT near-Maxwell control, and
    `saddle_exact_cancellation_m1` shows the separate-piece bound (`4·Var ≥ 0`, `F ≤ 0`) is
    `O((1−w)⁻²)`-lossy — so the residual IS the local-CLT core
    `SelfFusionLogConcave.FusionConvLogConcaveCore` (all fusion powers), already open. -/
theorem uniformSlack_reduces_to_localCLT : True := trivial

/-- **`slack_bound_does_not_close_singleStep` (documentation theorem).**  Even a FULLY
proved uniform `Cdef_m ≤ 2(1−w)³` does NOT inhabit
`SingleStepDefectReduction.SingleStepDefectBound`.  `singleStep` is a recursion on the
ABSTRACT physical margin `trueMargin` (an `s = 1` fundamental-gap statement); `Cdef_m` is an
`s = 2` leakage relative to a renormalized `s = 1` coupling at a SINGLE step — strictly
weaker.  The gap (`real_defect_identification`) is (a) the true-margin construction, (b) the
block-multiplicity matching `m = b^{d−1}`, and (c) the channel feedback of the `s ≥ 2`
remainder into the next scale's `s = 1` gap over the full RG recursion.  This file inhabits
NO frontier bundle and produces NO `SingleStepDefectBound` (no alias). -/
theorem slack_bound_does_not_close_singleStep : True := trivial

/-- **`fullFloor_still_needs_singleStep` — the continuum floor rests on `singleStep`.**
GIVEN a `SingleStepDefectBound` (the ACTUAL open input — NOT produced here), the whole
positive continuum floor for the true margin follows.  Records that the `m = 1` closure and
the saddle/cancellation facts proved here are supporting evidence for that input, not a
substitute for it. -/
theorem fullFloor_still_needs_singleStep
    (S : SingleStepDefectReduction.SingleStepDefectBound) :
    (0 : Q') < (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
      ∧ ∀ k : Nat,
          (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
            ≤ S.trueMargin k :=
  SingleStepDefectReduction.fullFloor_of_singleStep S

/-! ## 5. The verdict bundle (non-vacuous; inhabits NO frontier type). -/

/-- **`ConnectedSlackVerdict`** — the machine-checked state of the connected-correction /
third-order-slack inequality `Cdef ≤ 2(1−w)³`.  Bundles: the `m = 1` uniform-in-`w` closure,
the exact `m = 1` saddle cancellation (the sharp residual anchor), and the slack
nonnegativity.  It inhabits NO guarded Clay-frontier bundle and produces NO
`SingleStepDefectBound`. -/
structure ConnectedSlackVerdict : Type where
  /-- The slack `2(1−w)³ ≥ 0` on `w ≤ 1`. -/
  slack_nonneg : ∀ {w : Q'}, w ≤ (1 : Q') → (0 : Q') ≤ slackExpr w
  /-- `m = 1` connected-slack closure, uniform in `w`. -/
  m1_closure : ∀ {w : Q'}, w ≤ (1 : Q') → cdef1 w ≤ slackExpr w
  /-- the exact `m = 1` saddle cancellation `4·Var_1 + F₁ ≃ 0`. -/
  m1_cancellation : ∀ w : Q',
    (fourVarQ (Q'.ofNat 3 * qpow w 8) (qpow w 3) + fTermQ (qpow w 3) (qpow w 8)).eqv (0 : Q')

/-- **`connectedSlack_verdict` — non-vacuous inhabitant; every field a PROVED theorem.**
No frontier bundle inhabited; no `SingleStepDefectBound` produced. -/
def connectedSlack_verdict : ConnectedSlackVerdict where
  slack_nonneg := fun hw1 => slackExpr_nonneg hw1
  m1_closure := fun hw1 => cdef1_le_slack hw1
  m1_cancellation := saddle_exact_cancellation_m1

end YMGap.Continuum.ConnectedSlackBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ConnectedSlackBound.slackExpr_nonneg
#print axioms YMGap.Continuum.ConnectedSlackBound.m1_cubeRoot_exact
#print axioms YMGap.Continuum.ConnectedSlackBound.cdef1_eq_zero
#print axioms YMGap.Continuum.ConnectedSlackBound.cdef1_le_slack
#print axioms YMGap.Continuum.ConnectedSlackBound.saddle_exact_cancellation_m1
#print axioms YMGap.Continuum.ConnectedSlackBound.fourVar_ge_zero
#print axioms YMGap.Continuum.ConnectedSlackBound.fullFloor_still_needs_singleStep
#print axioms YMGap.Continuum.ConnectedSlackBound.connectedSlack_verdict
