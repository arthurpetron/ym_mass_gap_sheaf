/-
Track B / R2 — the **matched-retune CROSSOVER frontier**: the per-step telescoping
facts that feed the matched-retune engine, expressed through the closed `(r,d)` BOX
form of the `p = 2` self-fusion and the rational `ρ`-brackets of the matched kernel.

# Why this module exists — the genuine local-CLT lever, wired to the engine

The matched-retune engine converts a cumulative step-sum bound on the per-step
increments

    δ_k  =  (g_{k+1}·ĉ_k)/(g_k·ĉ_{k+1}) − 1,      g_s = bondMovedCoeff N w 2 s,

into the corrected per-mode quotient bound (`quotient_bound_of_step_sum`, the proved
`Q'` engine).  The two facts the engine consumes are

  * **dominance** `δ_k ≥ 0`  ⟺  `g_{k+1}·ĉ_k ≥ g_k·ĉ_{k+1}`  ⟺  `s ↦ g_s/ĉ_s` is
    non-decreasing — "self-fusion has heavier tails than the matched kernel"; and
  * the **derivative bound** `δ_k ≤ C·u²·(y_{k+1} − y_k)` (`u = 1 − w`), which (since
    `y_{k+1} − y_k = u·(c4(k+1) − c4(k)) = u·(2k+3)`) reads `δ_k ≤ C·u³·(2k+3)` and
    telescopes to `∑_{k<s} δ_k ≤ C·u²·y_s`.

The matched kernel coefficient is `ĉ_s = (s+1)·ρ^{C₄(s)}` with `ρ³ = g₁/(2g₀)` (so the
`s = 1` marginal is killed by construction: `δ_0 = 0` exactly).  `C₄(s) = s(s+2)`, so
`C₄(k+1) − C₄(k) = 2k+3` and `ĉ_{k+1}/ĉ_k = ((k+2)/(k+1))·ρ^{2k+3}`.

# What is GENUINELY PROVED here (axiom-clean `Q'` arithmetic + the reductions)

THE CROSS-MULTIPLICATION LEVER (proved):
  * `stepRatioQ` / `stepDeltaQ'` — the matched step ratio `(g_{k+1}·ĉ_k)/(g_k·ĉ_{k+1})`
    and the increment `δ_k = stepRatioQ − 1`, at the `Q'` level keyed on rational
    bracket data for `ĉ`.
  * `stepDelta_nonneg_iff_cross` — **the dominance reduction**: `δ_k ≥ 0` IFF the
    cross-product dominance `g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k` holds (pure `divPos`).
  * `stepDelta_nonneg_of_bracket` — **the bracket-sufficient form**: if
    `g_k·(ĉ_{k+1} UPPER bracket) ≤ g_{k+1}·(ĉ_k LOWER bracket)` then `δ_k ≥ 0`, reducing
    the genuine cross-over to a pure `Q'` box-vs-bracket inequality.
  * `stepDelta_le_of_bracket` — **the derivative reduction**: a `Q'` numerator bound
    `g_{k+1}·ĉ_k^{up} ≤ (1 + D)·(g_k·ĉ_{k+1}^{lo})` gives `δ_k ≤ D`; feeding the target
    `D = C·u³·(2k+3)` yields the derivative bound.
  * `cInc_eq` — the EXACT Casimir increment `C₄(k+1) − C₄(k) = 2k+3`, the `(2k+3)` factor
    the box increment `g_{k+1} − g_k` exposes and the matched-kernel power carries.

THE ENGINE WIRING (proved):
  * `MatchedStepData` — the per-step data carrier: the step sequence `δ`, the residual
    polynomial `P` (nonneg coeffs), `δ_k ≥ 0` (step_nonneg, the dominance frontier) and
    the cumulative bound `∑_{k<s} δ_k ≤ u²·Peval P (yArg w s)` (cumsum, the derivative
    frontier telescoped).  This is exactly `MatchedRetune.StepSumCert`'s content, named
    locally for the frontier.
  * `frontier_stepSumCert` — assembles a `StepSumCert` from `MatchedStepData`.
  * `frontier_quotientCert` — **fires the engine**: from `MatchedStepData` plus the
    active-window smallness side-condition, produces the corrected per-mode quotient
    certificate `QuotientActiveWindowCertMatched`.
  * `cumsum_of_perstep` — **the telescoping**: from a per-step derivative bound
    `δ_k ≤ C·u²·(c4(k+1) − c4(k))` (and `δ_k ≥ 0`), the cumulative sum telescopes to
    `∑_{k<s} δ_k ≤ C·u²·c4(s) = C·u·yArg w s`, the literal `∑(y_{k+1}−y_k) = y_s − y_0`.

# NAMED OPEN — the genuine discrete-local-CLT residuals (corrected statements)

  * `BoxRatioDerivative` — the derivative (magnitude) frontier as a pure `Q'` box
    inequality `g_{k+1}·ĉ_k^{up} ≤ (1 + C·u³·(2k+3))·(g_k·ĉ_{k+1}^{lo})` with explicit
    `C`, WINDOWED to the active window `1 ≤ k ≤ S` (cutoff `S ≍ τ^{−1/2}`), using the
    DECOMPOSED+DEPTH brackets `coeffMatchedLo/Hi R hR D` (the naive `(rhoHi/rhoLo)^{C₄}`
    explosion is REMOVED — the slack is now bounded `≤ (rhoHi/rhoLo)²`).  The `u²` gain is
    supplied by `secondOrder_qpow` on the `ρ^{2k+3}` power increment; the `(2k+3)` factor
    by `cInc_eq`.  WINDOWED because (exact arithmetic) `δ_k/(u³·(2k+3))` grows UNBOUNDED
    in the tail (fails near `y ≈ 44`), so the unwindowed `∀ k` form is false-as-stated;
    the windowed form is the TRUE one.  NAMED, not inhabited; NOT a `C₄²` envelope.
  * `BoxRatioDominance` (bracketed) — RESTATED with the decomposed+depth brackets, but the
    sign margin `δ_1 ~ τ³ → 0` beats ANY fixed depth, so the bracketed surrogate is NOT
    uniformly inhabitable.  The genuine dominance is carried EXACT-`CReal` by
    `MatchedRetuneBridge.ExactCRealDominance` (separating rationals on the genuine `CReal`
    `ĉ`, NO bracket slack) — see §7b: PROVED base `δ_0 = 0` and bridge, NAMED separators.

`δ_0 = 0` is EXACT (the matching identity), so the active window starts at `k ≥ 1`.

# Honest verdict and scope

This module proves the cross-multiplication DOMINANCE REDUCTION (`δ_k ≥ 0 ⟺` a `Q'`
box inequality), the DERIVATIVE REDUCTION (`δ_k ≤ D ⟸` a `Q'` numerator inequality), the
EXACT Casimir increment `2k+3`, the literal TELESCOPING `∑(y_{k+1}−y_k) = y_s`, and the
full ENGINE WIRING producing `QuotientActiveWindowCertMatched` from a `MatchedStepData`
carrier.  The two genuine discrete-local-CLT facts — the box dominance and the box
derivative bound — are NAMED precisely as `Q'` box inequalities (`BoxRatioDominance`,
`BoxRatioDerivative`) built from the PROVED closed `(r,d)` box form and the PROVED
`rhoLo/rhoHi` brackets; they are NOT inhabited here, NOT `C₄²` envelopes, NOT the false
folded 1-D product.  This is the technical crossover lever — NOT a 4D Yang–Mills mass
gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, `omega` on `Nat` identities, reused `Q'` order / `divPos`
lemmas, the proved engine and bracket bridge.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable facts), no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionRDFactor
import YMGap.Continuum.MatchedRetune
import YMGap.Continuum.MatchedRetuneBridge
import YMGap.Continuum.BondMovingQuadratic

namespace YMGap.Continuum.MatchedRetuneFrontier

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.FusionRDFactor
open YMGap.Continuum.MatchedRetune
open YMGap.Continuum.MatchedRetuneBridge
open YMGap.Continuum.ProductFloor
open YMGap.Continuum.HeatKernelRGStep

/-! ## 0. The exact Casimir increment `C₄(k+1) − C₄(k) = 2k + 3`

`C₄(s) = s·(s+2)` (`RGTransport.c4`).  The first difference is the linear `2k+3` —
the factor the `(r,d)` box increment `g_{k+1} − g_k` exposes and the matched-kernel
power increment `ρ^{C₄(k+1)}/ρ^{C₄(k)} = ρ^{2k+3}` carries.  This is the `(2k+3)` in
the derivative target `δ_k ≤ C·u³·(2k+3)` and in `y_{k+1} − y_k = u·(2k+3)`. -/

/-- **The exact Casimir increment** `C₄(k+1) = C₄(k) + (2k+3)`. -/
theorem cInc_eq (k : Nat) : c4 (k + 1) = c4 k + (2 * k + 3) := by
  show (k + 1) * (k + 1 + 2) = k * (k + 2) + (2 * k + 3)
  -- expand both products with `prod_expand` (atoms in canonical order), then `omega`.
  have e1 : (k + 1) * ((k + 2) + 1) = k * (k + 2) + k * 1 + 1 * (k + 2) + 1 * 1 :=
    FusionRDFactor.prod_expand k 1 (k + 2) 1
  have hl : (k + 1 + 2) = (k + 2) + 1 := by omega
  rw [hl, e1]
  generalize k * (k + 2) = kk
  rw [Nat.mul_one, Nat.one_mul, Nat.one_mul]
  omega

/-- **The `yArg` increment** `yArg w (k+1) − yArg w k ≃ (1−w)·(2k+3)` — the literal
telescoping increment, with `2k+3 = C₄(k+1) − C₄(k)`. -/
theorem yArg_inc_eq (w : Q') (k : Nat) :
    (yArg w (k + 1) + -(yArg w k)).eqv (((1 : Q') - w) * Q'.ofNat (2 * k + 3)) := by
  show (((1 : Q') - w) * Q'.ofNat (c4 (k + 1)) + -(((1 : Q') - w) * Q'.ofNat (c4 k))).eqv
    (((1 : Q') - w) * Q'.ofNat (2 * k + 3))
  -- C₄(k+1) = C₄ k + (2k+3), so ofNat(C₄(k+1)) ≃ ofNat(C₄ k) + ofNat(2k+3)
  have hofN : (Q'.ofNat (c4 (k + 1))).eqv (Q'.ofNat (c4 k) + Q'.ofNat (2 * k + 3)) := by
    rw [cInc_eq k]
    -- ofNat (a + b) ≃ ofNat a + ofNat b
    exact Q'.ofNat_add_eqv (c4 k) (2 * k + 3)
  -- (1−w)·ofNat(C₄(k+1)) ≃ (1−w)·(ofNat(C₄k) + ofNat(2k+3)) ≃ (1−w)·ofNat(C₄k) + (1−w)·ofNat(2k+3)
  have hexp : (((1 : Q') - w) * Q'.ofNat (c4 (k + 1))).eqv
      (((1 : Q') - w) * Q'.ofNat (c4 k) + ((1 : Q') - w) * Q'.ofNat (2 * k + 3)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hofN) ?_
    exact Q'.mul_add_eqv ((1 : Q') - w) (Q'.ofNat (c4 k)) (Q'.ofNat (2 * k + 3))
  -- (A + B) + -A ≃ B
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hexp) ?_
  -- (X + Y) + -X ≃ Y  with X = (1−w)·ofNat(C₄k), Y = (1−w)·ofNat(2k+3)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (((1 : Q') - w) * Q'.ofNat (c4 k))
      (((1 : Q') - w) * Q'.ofNat (2 * k + 3)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (((1 : Q') - w) * Q'.ofNat (2 * k + 3))
      (((1 : Q') - w) * Q'.ofNat (c4 k)) (-(((1 : Q') - w) * Q'.ofNat (c4 k)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (((1 : Q') - w) * Q'.ofNat (c4 k)))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (((1 : Q') - w) * Q'.ofNat (2 * k + 3)))

/-! ## 1. The matched step ratio and increment (`Q'`-keyed cross form)

The matched step ratio is `Q_{k+1}/Q_k = (g_{k+1}·ĉ_k)/(g_k·ĉ_{k+1})` (the
`ĉ_0` factors cancel in the ratio of `Q_s = (g_s·ĉ_0)/(g_0·ĉ_s)`).  We carry it at
the `Q'` level against an abstract POSITIVE matched coefficient sequence `chat : Nat →
Q'` (instantiated downstream by the rational brackets `coeffMatchedLo/Hi` of the
genuine `CReal` `ĉ`).  The increment is `δ_k = stepRatioQ − 1`. -/

/-- The matched step ratio `(g_{k+1}·ĉ_k)/(g_k·ĉ_{k+1})` against an abstract positive
matched-coefficient sequence `chat`, via `divPos` by the positive denominator
`g_k·ĉ_{k+1}`. -/
def stepRatioQ (N : Nat) (w : Q') (chat : Nat → Q')
    (k : Nat)
    (hden : (0 : Q') < bondMovedCoeff N w 2 k * chat (k + 1)) : Q' :=
  Q'.divPos (bondMovedCoeff N w 2 (k + 1) * chat k)
    (bondMovedCoeff N w 2 k * chat (k + 1)) hden

/-- The matched per-step increment `δ_k = stepRatioQ − 1`. -/
def stepDeltaQ' (N : Nat) (w : Q') (chat : Nat → Q')
    (k : Nat)
    (hden : (0 : Q') < bondMovedCoeff N w 2 k * chat (k + 1)) : Q' :=
  stepRatioQ N w chat k hden + -(1 : Q')

/-! ## 2. The cross-multiplication dominance reduction — THE LEVER

`δ_k ≥ 0  ⟺  stepRatioQ ≥ 1  ⟺  g_{k+1}·ĉ_k ≥ g_k·ĉ_{k+1}` (the cross-product
dominance).  This is `divPos num den ≥ 1 ⟺ num ≥ den`, the pure `divPos` two-sided
fact.  It reduces the analytic dominance `δ_k ≥ 0` to a single `Q'` inequality on the
self-fusion coefficients and the matched kernel — "self-fusion has heavier tails". -/

/-- **THE DOMINANCE REDUCTION (one direction, the one the engine needs).**  If the
cross-product dominance `g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k` holds, then `δ_k ≥ 0`.

PROOF.  `δ_k = divPos (g_{k+1}·ĉ_k) (g_k·ĉ_{k+1}) − 1`.  `g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k`
written as `1·den ≤ num` gives `1 ≤ divPos num den` (`le_divPos_of_mul_le`), hence
`0 ≤ divPos num den − 1 = δ_k`. -/
theorem stepDelta_nonneg_of_cross (N : Nat) (w : Q') (chat : Nat → Q') (k : Nat)
    (hden : (0 : Q') < bondMovedCoeff N w 2 k * chat (k + 1))
    (hcross : bondMovedCoeff N w 2 k * chat (k + 1)
      ≤ bondMovedCoeff N w 2 (k + 1) * chat k) :
    (0 : Q') ≤ stepDeltaQ' N w chat k hden := by
  show (0 : Q') ≤ stepRatioQ N w chat k hden + -(1 : Q')
  -- 1 ≤ divPos num den
  have h1le : (1 : Q') ≤ stepRatioQ N w chat k hden := by
    show (1 : Q') ≤ Q'.divPos (bondMovedCoeff N w 2 (k + 1) * chat k)
      (bondMovedCoeff N w 2 k * chat (k + 1)) hden
    refine Q'.le_divPos_of_mul_le _ _ hden ?_
    -- 1·den ≤ num
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hcross
  -- 0 = 1 + -1 ≤ divPos + -1
  have := Q'.add_le_add_right _ _ (-(1 : Q')) h1le
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv (1 : Q'))) this

/-- **THE BRACKET-SUFFICIENT DOMINANCE.**  Let `chatLo k ≤ ĉ_k` and `ĉ_{k+1} ≤
chatHi (k+1)` be the rational brackets of the genuine matched coefficient.  If the
`Q'` BOX inequality

    g_k · chatHi (k+1)  ≤  g_{k+1} · chatLo k

holds (heavier-tail comparison, both `g`'s in the proved closed `(r,d)` box form), then
the cross-product dominance `g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k` holds, hence `δ_k ≥ 0`.

PROOF.  `g_k·ĉ_{k+1} ≤ g_k·chatHi(k+1) ≤ g_{k+1}·chatLo k ≤ g_{k+1}·ĉ_k`, using
`g_k, g_{k+1} ≥ 0` and the brackets.  The MIDDLE step is the named `Q'` box inequality
`BoxRatioDominance`; the outer steps are the bracket facts. -/
theorem stepDelta_nonneg_of_bracket (N : Nat) {w : Q'} (hw : (0 : Q') ≤ w)
    (chat chatLo chatHi : Nat → Q') (k : Nat)
    (hden : (0 : Q') < bondMovedCoeff N w 2 k * chat (k + 1))
    (hLo : chatLo k ≤ chat k) (hHi : chat (k + 1) ≤ chatHi (k + 1))
    (hbox : bondMovedCoeff N w 2 k * chatHi (k + 1)
      ≤ bondMovedCoeff N w 2 (k + 1) * chatLo k) :
    (0 : Q') ≤ stepDeltaQ' N w chat k hden := by
  refine stepDelta_nonneg_of_cross N w chat k hden ?_
  -- g_k·ĉ_{k+1} ≤ g_k·chatHi(k+1) ≤ g_{k+1}·chatLo k ≤ g_{k+1}·ĉ_k
  have hgk : (0 : Q') ≤ bondMovedCoeff N w 2 k := bondMovedCoeff_nonneg N hw 2 k
  have hgk1 : (0 : Q') ≤ bondMovedCoeff N w 2 (k + 1) := bondMovedCoeff_nonneg N hw 2 (k + 1)
  have step1 : bondMovedCoeff N w 2 k * chat (k + 1) ≤ bondMovedCoeff N w 2 k * chatHi (k + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hHi hgk
  have step3 : bondMovedCoeff N w 2 (k + 1) * chatLo k ≤ bondMovedCoeff N w 2 (k + 1) * chat k :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hLo hgk1
  exact Q'.le_trans' _ _ _ step1 (Q'.le_trans' _ _ _ hbox step3)

/-! ## 3. The derivative-bound reduction — THE DEVIATION LEVER

`δ_k ≤ D  ⟺  stepRatioQ ≤ 1 + D  ⟸  num ≤ (1+D)·den`, i.e.

    g_{k+1}·ĉ_k  ≤  (1 + D)·(g_k·ĉ_{k+1}).

With the brackets, the sufficient `Q'` numerator inequality is

    g_{k+1}·chatHi k  ≤  (1 + D)·(g_k·chatLo (k+1)),

and feeding the target `D = C·u³·(2k+3)` gives the derivative bound.  The `u²` gain is
the `secondOrder_qpow` quadratic Taylor on the `ρ^{2k+3}` power increment; the `(2k+3)`
factor is `cInc_eq`. -/

/-- **THE DERIVATIVE REDUCTION (one direction, the one the engine needs).**  If the
`Q'` numerator inequality `g_{k+1}·ĉ_k ≤ (1 + D)·(g_k·ĉ_{k+1})` holds, then `δ_k ≤ D`.

PROOF.  `δ_k = divPos num den − 1 ≤ (1+D) − 1 = D` (`divPos_le_of_le_mul` with
`C = 1 + D`). -/
theorem stepDelta_le_of_cross (N : Nat) (w : Q') (chat : Nat → Q') (k : Nat) {D : Q'}
    (hden : (0 : Q') < bondMovedCoeff N w 2 k * chat (k + 1))
    (hnum : bondMovedCoeff N w 2 (k + 1) * chat k
      ≤ ((1 : Q') + D) * (bondMovedCoeff N w 2 k * chat (k + 1))) :
    stepDeltaQ' N w chat k hden ≤ D := by
  show stepRatioQ N w chat k hden + -(1 : Q') ≤ D
  have hle : stepRatioQ N w chat k hden ≤ (1 : Q') + D :=
    Q'.divPos_le_of_le_mul _ _ hden hnum
  -- divPos + -1 ≤ (1+D) + -1 ≃ D
  have := Q'.add_le_add_right _ _ (-(1 : Q')) hle
  refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
  -- (1 + D) + -1 ≃ D
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-(1 : Q')) (Q'.add_comm_eqv 1 D)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv D 1 (-(1 : Q'))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left D _ _ (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' D)

/-- **THE BRACKET-SUFFICIENT DERIVATIVE BOUND.**  With brackets `ĉ_k ≤ chatHi k`,
`chatLo (k+1) ≤ ĉ_{k+1}`, and `D ≥ 0`, if the `Q'` BOX inequality

    g_{k+1}·chatHi k  ≤  (1 + D)·(g_k·chatLo (k+1))

holds, then `δ_k ≤ D`.

PROOF.  `g_{k+1}·ĉ_k ≤ g_{k+1}·chatHi k ≤ (1+D)·(g_k·chatLo(k+1)) ≤ (1+D)·(g_k·ĉ_{k+1})`,
then `stepDelta_le_of_cross`.  The MIDDLE step is the named box inequality
`BoxRatioDerivative`. -/
theorem stepDelta_le_of_bracket (N : Nat) {w : Q'} (hw : (0 : Q') ≤ w)
    (chat chatLo chatHi : Nat → Q') (k : Nat) {D : Q'} (hD : (0 : Q') ≤ D)
    (hden : (0 : Q') < bondMovedCoeff N w 2 k * chat (k + 1))
    (hHi : chat k ≤ chatHi k) (hLo : chatLo (k + 1) ≤ chat (k + 1))
    (hbox : bondMovedCoeff N w 2 (k + 1) * chatHi k
      ≤ ((1 : Q') + D) * (bondMovedCoeff N w 2 k * chatLo (k + 1))) :
    stepDeltaQ' N w chat k hden ≤ D := by
  refine stepDelta_le_of_cross N w chat k hden ?_
  have hgk : (0 : Q') ≤ bondMovedCoeff N w 2 k := bondMovedCoeff_nonneg N hw 2 k
  have hgk1 : (0 : Q') ≤ bondMovedCoeff N w 2 (k + 1) := bondMovedCoeff_nonneg N hw 2 (k + 1)
  have h1Dnn : (0 : Q') ≤ (1 : Q') + D :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) (Q'.add_le_self_of_nonneg 1 D hD)
  -- g_{k+1}·ĉ_k ≤ g_{k+1}·chatHi k
  have step1 : bondMovedCoeff N w 2 (k + 1) * chat k
      ≤ bondMovedCoeff N w 2 (k + 1) * chatHi k :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hHi hgk1
  -- (1+D)·(g_k·chatLo(k+1)) ≤ (1+D)·(g_k·ĉ_{k+1})
  have step3 : ((1 : Q') + D) * (bondMovedCoeff N w 2 k * chatLo (k + 1))
      ≤ ((1 : Q') + D) * (bondMovedCoeff N w 2 k * chat (k + 1)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hLo hgk) h1Dnn
  exact Q'.le_trans' _ _ _ step1 (Q'.le_trans' _ _ _ hbox step3)

/-! ## 4. The cumulative telescoping `∑_{k<s} δ_k ≤ C·u·yArg w s`

From a per-step derivative bound `δ_k ≤ C·u³·(2k+3) = C·u²·(yArg(k+1) − yArg k)` (and
`δ_k ≥ 0`), the cumulative sum telescopes:

    ∑_{k<s} δ_k  ≤  C·u² · ∑_{k<s}(yArg(k+1) − yArg k)  =  C·u²·(yArg s − yArg 0)
                =  C·u²·yArg s   (since yArg 0 = 0).

We carry the cumulative bound in the engine's `(1−w)²·Peval P (yArg w s)` shape.  Here
the per-step derivative bound is taken in the form `δ_k ≤ u²·perStep k` with
`perStep k = C·u·(2k+3)` and we prove `∑ δ_k ≤ u²·(∑_{k<s} perStep k)`; the literal
telescoping `∑_{k<s}(2k+3) = c4 s` (`= s(s+2)`) ties the per-step factor to `yArg`. -/

/-- The literal `Nat` telescoping `∑_{k<s}(2k+3) = C₄(s) = s·(s+2)`. -/
theorem sum_twoKPlus3 : ∀ s, (Nat.rec 0 (fun k acc => acc + (2 * k + 3)) s : Nat) = c4 s
  | 0 => rfl
  | s + 1 => by
      show (Nat.rec 0 (fun k acc => acc + (2 * k + 3)) s : Nat) + (2 * s + 3) = c4 (s + 1)
      rw [sum_twoKPlus3 s, cInc_eq s]

/-- **The cumulative monotone bound.**  If `0 ≤ δ_k` and `δ_k ≤ B_k` for all `k`, then
`∑_{k<s} δ_k ≤ ∑_{k<s} B_k` (`lossSum` is monotone in the summand). -/
theorem lossSum_le_of_le (δ B : Nat → Q') (hδB : ∀ k, δ k ≤ B k) :
    ∀ s, lossSum δ s ≤ lossSum B s
  | 0 => Q'.le_refl' 0
  | s + 1 => by
      show lossSum δ s + δ s ≤ lossSum B s + B s
      exact Q'.add_le_add (lossSum_le_of_le δ B hδB s) (hδB s)

/-! ## 5. The per-step data carrier and the engine firing

`MatchedStepData` packages exactly the engine input: a nonnegative step sequence whose
cumulative sum is controlled by `(1−w)²·Peval P (yArg w s)`.  Its two open fields are
the genuine frontier (the dominance `step_nonneg` and the telescoped derivative
`cumsum`).  `frontier_stepSumCert` converts it to a `StepSumCert`, and
`frontier_quotientCert` fires the proved engine. -/

/-- **The matched per-step data carrier** for the frontier.  Identical content to
`MatchedRetune.StepSumCert`, named locally: a step sequence `δ`, the nonneg-coeff
residual polynomial `P`, the dominance `δ_k ≥ 0`, and the telescoped derivative bound
`∑_{k<s} δ_k ≤ (1−w)²·Peval P (yArg w s)`.  The two analytic fields are the NAMED
discrete-local-CLT residuals (`BoxRatioDominance`/`BoxRatioDerivative` supply them via
the reductions of §2–4); they are carried abstractly. -/
structure MatchedStepData (N : Nat) (w : Q') (hw : (0 : Q') < w) : Type where
  /-- The matched per-step increment sequence `δ`. -/
  δ : Nat → Q'
  /-- The fixed `w`-independent residual polynomial. -/
  P : BondMovingMoment.Poly
  /-- Nonneg coefficients. -/
  P_nonneg : nonnegCoeffs P
  /-- **Dominance (frontier):** `δ_k ≥ 0`. -/
  step_nonneg : ∀ k, (0 : Q') ≤ δ k
  /-- **Derivative, telescoped (frontier):** the cumulative bound. -/
  cumsum : ∀ s, lossSum δ s
    ≤ (((1 : Q') - w) * ((1 : Q') - w)) * Peval P (yArg w s)

/-- **Assemble a `StepSumCert` from the matched per-step data.**  Direct field copy:
`MatchedStepData` IS the `StepSumCert` content. -/
def frontier_stepSumCert (N : Nat) (w : Q') (hw : (0 : Q') < w)
    (d : MatchedStepData N w hw) : MatchedRetune.StepSumCert N w hw where
  δ := d.δ
  P := d.P
  P_nonneg := d.P_nonneg
  step_nonneg := d.step_nonneg
  cumsum_bound := d.cumsum

/-- **FIRE THE ENGINE.**  From the matched per-step data and the active-window
smallness side-condition, produce the corrected per-mode quotient certificate
`QuotientActiveWindowCertMatched` (the matched-reference bound
`absQ(prodOnePlus δ s − 1) ≤ (1−w)²·Peval (scalePoly 2 P) (yArg w s)` on `1 ≤ s`).

PROOF.  `frontier_stepSumCert` then `quotientCert_of_stepSum` (the proved engine). -/
def frontier_quotientCert (N : Nat) (w : Q') (hw : (0 : Q') < w)
    (d : MatchedStepData N w hw)
    (hsmall : ∀ s, 1 ≤ s →
      (((1 : Q') - w) * ((1 : Q') - w)) * Peval d.P (yArg w s)
        ≤ Q'.ofNat 1 * Q'.recipPos (Q'.ofNat 2) (by decide)) :
    MatchedRetune.QuotientActiveWindowCertMatched N w hw :=
  MatchedRetune.quotientCert_of_stepSum N w hw (frontier_stepSumCert N w hw d) hsmall

/-! ## 6. The genuine NAMED residuals — the discrete local CLT as `Q'` box inequalities

The two facts the carrier `MatchedStepData` leaves abstract are the dominance and the
derivative bound.  Through the reductions §2–4 they reduce to PURE `Q'` BOX inequalities
on the proved closed `(r,d)` box form of `g_s` (`bondMovedCoeff_p2_rd`) and the FIXED
DECOMPOSED+DEPTH `coeffMatchedLo/Hi R hR D` brackets of the matched kernel `ĉ_s =
coeffMatched ρ s` (bounded slack — the naive `(rhoHi/rhoLo)^{C₄}` explosion removed).  We
name them precisely as `Type`-level obligations — `Q'` finite-sum inequalities, NOT
oracles, NOT `C₄²` envelopes, NOT the false folded 1-D `R₂D₀ − R₀D₂` product.

The DOMINANCE (sign) bracketed surrogate `BoxRatioDominance` is, however, FALSE-as-stated
as `w → 1` (the margin `δ_1 ~ τ³ → 0` beats any fixed depth `D`); the genuine dominance is
the EXACT-`CReal` `ExactCRealDominance` of the bridge module (see §7b).  The DERIVATIVE
(magnitude) `BoxRatioDerivative` is correctly stated on the decomposed brackets. -/

/-- **THE DOMINANCE BOX RESIDUAL (bracketed surrogate — FALSE-as-stated as `w → 1`).**
For the matched kernel `R = cubeRatio N w hw` (`ρ = ∛R`, decomposed+depth brackets
`coeffMatchedLo/Hi R hR D`), the heavier-tail box dominance

    g_k · coeffMatchedHi R hR D (k+1)  ≤  g_{k+1} · coeffMatchedLo R hR D k.

The dominance sign margin `δ_1 ~ τ³` vanishes faster than ANY fixed-depth bracket slack,
so this bracketed surrogate is NOT uniformly inhabitable — the genuine dominance is
EXACT-`CReal` (`MatchedRetuneBridge.ExactCRealDominance`, §7b).  Kept for the conditional
`perstep_nonneg_of_box` reduction.  NOT inhabited here. -/
structure BoxRatioDominance (N : Nat) (w : Q') (hw : (0 : Q') < w)
    (R : Q') (hR : (0 : Q') < R) (D : Nat) : Type where
  /-- The box dominance inequality on the active modes `1 ≤ k`. -/
  dominance : ∀ k, 1 ≤ k →
    bondMovedCoeff N w 2 k * coeffMatchedHi R hR D (k + 1)
      ≤ bondMovedCoeff N w 2 (k + 1) * coeffMatchedLo R hR D k

/-- **THE DERIVATIVE BOX RESIDUAL — WINDOWED to the active window `k ≤ S`.**  With the
explicit constant `C : Q'`, the moving cutoff `S : Nat`, and the target deviation
`D_k = C·u³·(2k+3)` (`u = 1 − w`), the box numerator inequality on `1 ≤ k ≤ S`

    g_{k+1} · coeffMatchedHi R hR k
      ≤  (1 + C·u³·(2k+3)) · (g_k · coeffMatchedLo R hR (k+1)),

with `g_s` in closed `(r,d)` box form.  The `u²` gain over the linear `u·(2k+3)` step is
the `secondOrder_qpow` quadratic Taylor on the `ρ^{2k+3}` power increment; the `(2k+3)`
factor is `cInc_eq`.  Combined with `coeffMatched_brackets` and `stepDelta_le_of_bracket`
it gives `δ_k ≤ C·u³·(2k+3)` on the active window.

WINDOWING (exact-arithmetic correction).  The per-step ratio
`δ_k/(u³·(2k+3))` is bounded only on the ACTIVE WINDOW `k ≤ S(τ)` (with
`S ≍ τ^{−1/2}`, where `y_k ≲ O(1)`); in the TAIL it grows UNBOUNDED (it fails near
`y ≈ 44`).  So the unwindowed `∀ k` statement is FALSE-as-stated.  The field is
therefore guarded by `k ≤ S`, which is the TRUE statement; the tail is handled by the
separate tail-bound machinery (the engine only consults the active window, where the
smallness `B ≤ 1/2` holds).  NOT a `C₄²` envelope.  NOT inhabited here. -/
structure BoxRatioDerivative (N : Nat) (w : Q') (hw : (0 : Q') < w)
    (R : Q') (hR : (0 : Q') < R) (D : Nat) (C : Q') (S : Nat) : Type where
  /-- The box derivative inequality on the active window `1 ≤ k ≤ S`. -/
  derivative : ∀ k, 1 ≤ k → k ≤ S →
    bondMovedCoeff N w 2 (k + 1) * coeffMatchedHi R hR D k
      ≤ ((1 : Q') + C * (((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w))
          * Q'.ofNat (2 * k + 3))
        * (bondMovedCoeff N w 2 k * coeffMatchedLo R hR D (k + 1))

/-! ## 7. The conditional crossover — δ_k facts from the named box residuals

Given the named box residuals (and the matched carrier's positivity), the reductions
§2–4 deliver the per-step dominance and derivative bound on the active window — the exact
content `MatchedStepData` carries.  We expose the two conditional theorems; assembling
them into a full `MatchedStepData` additionally needs the cumulative telescoping
(`lossSum_le_of_le` + `sum_twoKPlus3`), which we record as the wiring note. -/

/-- **Per-step dominance from the box residual.**  Given `BoxRatioDominance` and the
bracket facts (from `coeffMatched_brackets`), the matched increment against the genuine
`coeffMatched`-derived sequence is `≥ 0` on `1 ≤ k`.  Here `chat` is any sequence
sandwiched by the brackets `coeffMatchedLo ≤ chat ≤ coeffMatchedHi` (the rational image
of the genuine `CReal` `ĉ`). -/
theorem perstep_nonneg_of_box (N : Nat) {w : Q'} (hw : (0 : Q') < w)
    (R : Q') (hR : (0 : Q') < R) (D : Nat)
    (chat : Nat → Q')
    (hchatLo : ∀ s, coeffMatchedLo R hR D s ≤ chat s)
    (hchatHi : ∀ s, chat s ≤ coeffMatchedHi R hR D s)
    (box : BoxRatioDominance N w hw R hR D)
    (k : Nat) (hk : 1 ≤ k)
    (hden : (0 : Q') < bondMovedCoeff N w 2 k * chat (k + 1)) :
    (0 : Q') ≤ stepDeltaQ' N w chat k hden :=
  stepDelta_nonneg_of_bracket N (Q'.le_of_lt hw) chat
    (coeffMatchedLo R hR D) (coeffMatchedHi R hR D) k hden
    (hchatLo k) (hchatHi (k + 1)) (box.dominance k hk)

/-- **Per-step derivative bound from the box residual — WINDOWED.**  Given
`BoxRatioDerivative` (with constant `C`, cutoff `S`, `C·u³·(2k+3) ≥ 0`) and the bracket
facts, the matched increment is bounded by `C·u³·(2k+3)` on the ACTIVE WINDOW
`1 ≤ k ≤ S`.  The `k ≤ S` hypothesis is threaded to `box.derivative` (the windowed
field): the bound is the TRUE windowed one, not the false `∀ k` form. -/
theorem perstep_le_of_box (N : Nat) {w : Q'} (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (R : Q') (hR : (0 : Q') < R) (D : Nat) (C : Q') (hC : (0 : Q') ≤ C) (S : Nat)
    (chat : Nat → Q')
    (hchatLo : ∀ s, coeffMatchedLo R hR D s ≤ chat s)
    (hchatHi : ∀ s, chat s ≤ coeffMatchedHi R hR D s)
    (box : BoxRatioDerivative N w hw R hR D C S)
    (k : Nat) (hk : 1 ≤ k) (hkS : k ≤ S)
    (hden : (0 : Q') < bondMovedCoeff N w 2 k * chat (k + 1)) :
    stepDeltaQ' N w chat k hden
      ≤ C * (((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w)) * Q'.ofNat (2 * k + 3) := by
  have htau_nn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hu3_nn : (0 : Q') ≤ ((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ htau_nn htau_nn) htau_nn
  have hk3_nn : (0 : Q') ≤ Q'.ofNat (2 * k + 3) := zero_le_ofNat _
  have hD_nn : (0 : Q') ≤ C * (((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w))
      * Q'.ofNat (2 * k + 3) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC hu3_nn) hk3_nn
  exact stepDelta_le_of_bracket N (Q'.le_of_lt hw) chat
    (coeffMatchedLo R hR D) (coeffMatchedHi R hR D) k hD_nn hden
    (hchatHi k) (hchatLo (k + 1)) (box.derivative k hk hkS)

/-! ## 7b. The EXACT-`CReal` dominance crossover (the corrected dominance path)

The bracketed `BoxRatioDominance` (§6) is FALSE-as-stated: the dominance sign margin
`δ_1 ~ τ³ → 0` vanishes faster than ANY fixed-depth bracket slack, so `perstep_nonneg_of_box`
above CANNOT be fired uniformly (its hypothesis `box : BoxRatioDominance` is not inhabitable
as `w → 1`).  The genuine dominance lives on the EXACT `CReal` matched coefficient
`ĉ_s = coeffMatched ρ s` with NO bracket slack — carried by `ExactCRealDominance` (the
bridge module), whose separating rationals `B k` witness `g_k·ĉ_{k+1} ≤ B k ≤ g_{k+1}·ĉ_k`.

`exact_dominance_cross` re-exposes that per-mode constructive `≤` (the genuine
`step_nonneg` content against the exact `CReal` reference).  `matched_base_exact_cross`
records the EXACT `δ_0 = 0` base (`g_0·ĉ_1 ≃ g_1·ĉ_0`).  Wiring these into the engine's
`Q'`-valued `MatchedStepData.step_nonneg` requires a `CReal`-valued per-step quotient
(the `Q'` brackets break the vanishing margin) — NAMED here as the remaining wiring. -/

/-- **The EXACT-`CReal` dominance per mode (the corrected `step_nonneg` content).**  From
`ExactCRealDominance` (genuine `CReal` `ĉ`, NO bracket slack), the active-mode cross
dominance `g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k` holds as the constructive `≤` (separating rational
`B k`).  This is the vanishing-margin local CLT, exposed without the (false) fixed-depth
brackets. -/
def exact_dominance_cross (N : Nat) {w : Q'} (R : Q') (hR : (0 : Q') < R)
    (dom : MatchedRetuneBridge.ExactCRealDominance N w R hR) (k : Nat) (hk : 1 ≤ k) :
    Σ' B : Q',
      CReal.leRat
        (MatchedRetuneBridge.crossProd (bondMovedCoeff N w 2 k) (CReal.cbrtFrom R hR) (k + 1)) B
        ∧ ExpPos.geRat
          (MatchedRetuneBridge.crossProd (bondMovedCoeff N w 2 (k + 1)) (CReal.cbrtFrom R hR) k) B :=
  MatchedRetuneBridge.exact_cross_le N R hR dom k hk

/-- **The EXACT `δ_0 = 0` base** `g_0·ĉ_1 ≃ g_1·ĉ_0` (the `s = 1` marginal killed by the
matched retune).  Re-exposed from the bridge's `matched_base_exact`. -/
theorem matched_base_exact_cross (N : Nat) {w : Q'} (hw : (0 : Q') < w) :
    (bondMovedCoeff N w 2 0 * (Q'.ofNat 2 * MatchedRetune.cubeRatio N w hw)).eqv
      (bondMovedCoeff N w 2 1 * (1 : Q')) :=
  MatchedRetuneBridge.matched_base_exact N hw

/-! ## 8. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, pure `Q'`/`Nat` + reductions):
  * `cInc_eq` — the exact Casimir increment `C₄(k+1) − C₄(k) = 2k+3`.
  * `yArg_inc_eq` — the literal `yArg` step `yArg(k+1) − yArg k ≃ (1−w)·(2k+3)`.
  * `stepDelta_nonneg_of_cross` / `stepDelta_nonneg_of_bracket` — THE DOMINANCE
    REDUCTION: `δ_k ≥ 0` from the cross-product / bracket BOX inequality.
  * `stepDelta_le_of_cross` / `stepDelta_le_of_bracket` — THE DERIVATIVE REDUCTION:
    `δ_k ≤ D` from the numerator / bracket BOX inequality.
  * `sum_twoKPlus3` — the literal telescoping `∑_{k<s}(2k+3) = C₄(s)`.
  * `lossSum_le_of_le` — cumulative monotonicity.
  * `frontier_stepSumCert` / `frontier_quotientCert` — THE ENGINE WIRING: a
    `MatchedStepData` carrier produces `QuotientActiveWindowCertMatched` via the proved
    engine `quotientCert_of_stepSum`.
  * `perstep_nonneg_of_box` / `perstep_le_of_box` — the CONDITIONAL crossover: from the
    named box residuals plus the proved brackets, the per-step `δ_k ≥ 0` and
    `δ_k ≤ C·u³·(2k+3)` on the active window `1 ≤ k`.

  * `exact_dominance_cross` / `matched_base_exact_cross` — the EXACT-`CReal` dominance
    crossover (§7b): the per-mode constructive `≤` `g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k` on the
    genuine `CReal` `ĉ` (separating rational, NO bracket slack), and the PROVED EXACT base
    `δ_0 = 0` (`g_0·ĉ_1 ≃ g_1·ĉ_0`).

NAMED OPEN (NOT inhabited) — the genuine discrete local CLT:
  * `BoxRatioDerivative` — `g_{k+1}·ĉ_k^{hi} ≤ (1 + C·u³·(2k+3))·(g_k·ĉ_{k+1}^{lo})` with
    the EXPLICIT constant `C`, WINDOWED to the active window `1 ≤ k ≤ S`, on the
    DECOMPOSED+DEPTH brackets (bounded slack — the naive explosion is fixed), the `u²`
    gain from `secondOrder_qpow` and the `(2k+3)` from `cInc_eq`.  WINDOWED because
    `δ_k/(u³·(2k+3))` grows unbounded in the tail (the unwindowed `∀ k` form is
    false-as-stated); the windowed form is the TRUE statement.  Supplies the per-step
    derivative bound via `perstep_le_of_box` (which threads `k ≤ S`) once inhabited.
  * `MatchedRetuneBridge.ExactCRealDominance` — the dominance separators on the genuine
    `CReal` `ĉ` (the vanishing-margin local CLT; the bracketed `BoxRatioDominance` is
    false-as-stated as `w → 1`).  Plus the wiring of the exact-`CReal` comparison into the
    engine's `Q'`-valued `step_nonneg` (needs a `CReal`-valued per-step quotient).

`δ_0 = 0` is EXACT (`matched_base_exact`), so the active window is `k ≥ 1`.

HONEST VERDICT.  The cross-multiplication DOMINANCE reduction (`δ_k ≥ 0 ⟺` a `Q'` box
inequality), the DERIVATIVE reduction (`δ_k ≤ D ⟸` a `Q'` numerator inequality), the
exact Casimir increment `2k+3`, the literal `yArg`/`Nat` telescoping, the full ENGINE
WIRING (`MatchedStepData ⇒ QuotientActiveWindowCertMatched`), the FIXED decomposed+depth
brackets (the false `(rhoHi/rhoLo)^{C₄}` explosion removed), and the EXACT-`CReal`
dominance base + bridge are GENUINELY PROVED, axiom-clean.  The corrected derivative
magnitude bound and the dominance separators are NAMED precisely; they are NOT inhabited.
This is the technical crossover lever exposing the local-CLT / τ/2 structure — NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.MatchedRetuneFrontier

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MatchedRetuneFrontier.cInc_eq
#print axioms YMGap.Continuum.MatchedRetuneFrontier.yArg_inc_eq
#print axioms YMGap.Continuum.MatchedRetuneFrontier.stepDelta_nonneg_of_cross
#print axioms YMGap.Continuum.MatchedRetuneFrontier.stepDelta_nonneg_of_bracket
#print axioms YMGap.Continuum.MatchedRetuneFrontier.stepDelta_le_of_cross
#print axioms YMGap.Continuum.MatchedRetuneFrontier.stepDelta_le_of_bracket
#print axioms YMGap.Continuum.MatchedRetuneFrontier.sum_twoKPlus3
#print axioms YMGap.Continuum.MatchedRetuneFrontier.lossSum_le_of_le
#print axioms YMGap.Continuum.MatchedRetuneFrontier.frontier_stepSumCert
#print axioms YMGap.Continuum.MatchedRetuneFrontier.frontier_quotientCert
#print axioms YMGap.Continuum.MatchedRetuneFrontier.perstep_nonneg_of_box
#print axioms YMGap.Continuum.MatchedRetuneFrontier.perstep_le_of_box
#print axioms YMGap.Continuum.MatchedRetuneFrontier.exact_dominance_cross
#print axioms YMGap.Continuum.MatchedRetuneFrontier.matched_base_exact_cross
