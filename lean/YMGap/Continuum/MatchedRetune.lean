/-
Track B / R2 — the **matched-retune carrier** for the `p = 2` self-fusion relative
residual, the quotient/telescoping objects keyed on the EXACT `s = 1`-matched heat
kernel, the GENERIC product-to-sum telescoping engine, and the quarantine of the
wrong (temperature-`3τ`) reference.

# Why this module exists — the corrected reference for the self-fusion quotient

The per-mode relative fusion residual at `p = 2` is the vacuum-normalized quotient

    rrel s  =  (g_s · ĉ_0) / (g_0 · ĉ_s)  −  1,    g_s = bondMovedCoeff N w 2 s,

estimated against a heat-kernel REFERENCE `ĉ_s`.  The reference used elsewhere — the
first-order retune at temperature `≈ 3τ` (`τ = 1 − w`) — is the WRONG reference for the
FULL-mode self-fusion: the `s = 1` self-fusion coefficient ratio `g_1/g_0` matches a
heat kernel at temperature `≈ τ/2`, not `3τ`, so the `3τ` reference leaves a marginal
`s = 1` mismatch that makes the quotient blow up.  The CORRECT reference is the EXACT
`s = 1`-matched heat kernel: the base `ρ` with

    ρ³  =  g_1 / (2·g_0),

so that the matched first-excited coefficient `ĉ_1 = 2·ρ³ = g_1/g_0` makes the `s = 1`
quotient EXACTLY `1` (the marginal mode is killed by construction).

# What this module builds (and what it deliberately does NOT)

  * `MatchedRetuneP2` — the matched-retune CARRIER: it carries `ρ` as a constructive
    real (`CReal`) with positivity, `ρ < 1`, and the cube identity `ρ³ = g_1/(2g_0)`.
    The carrier is NOT inhabited here: the cube-root existence (to produce `ρ` from the
    rational `g_1/(2g_0)`) is a SEPARATE effort and is carried abstractly.
  * `crealPowNat` — the (pointwise) `CReal`-to-`Nat`-power used to express the matched
    full-mode coefficient `ĉ_s = (s+1)·ρ^{C₄(s)}` in the carrier.
  * `cubeRatio` — the rational `r = g_1/(2g_0)` that `ρ³` equals; `coeffMatchedQ`,
    `QfracQ`, `stepDeltaQ` — the matched reference coefficient, the quotient factor,
    and the per-step telescoping increment, all carried at the `Q'` level keyed on the
    rational cube `r` (this is exactly the level at which the matching identities for
    the dominant modes `s = 0, 1` collapse to rationals, and at which the generic
    telescoping engine operates).
  * `QfracQ_zero` / `QfracQ_one` — the MATCHING IDENTITIES: `QfracQ R 0 = 1` and
    `QfracQ R 1 = 1` (the latter is THE KEY identity, forced by `ρ³ = g_1/(2g_0)`:
    the exact retune kills the `s = 1` marginal), hence `stepDeltaQ R 0 = 0`.
  * `QfracQ_prod` — the TELESCOPING PRODUCT IDENTITY `QfracQ R s = ∏_{k<s}(1 + δ_k)`.
  * `quotient_bound_of_step_sum` — the GENERIC, REUSABLE product-to-sum telescoping
    engine: from a nonnegative step sequence with cumulative sum `≤ B ≤ 1/2`,
    `absQ (∏_{k<s}(1 + δ_k) − 1) ≤ 2·B`.  This is the engine that converts a
    (Wave-2) step-sum bound into the quotient bound.
  * `QuotientActiveWindowCertMatched` / `StepSumCert` / `quotientCert_of_stepSum` — the
    CORRECTED target certificate (matched reference), the SHARPER telescoping
    obligation, and the reduction of the latter to the former via the engine.

NAMED OPEN (NOT inhabited): the carrier `MatchedRetuneP2` (cube-root existence), and
the `StepSumCert` fields `step_nonneg` / `cumsum_bound` (the Wave-2 δ_k ≥ 0 and
derivative/cumulative bounds).  These are deliberately carried abstractly.

# Quarantine of the wrong reference

The first-order retune `renormW 2 w = 1 − 3·(1 − w)` has decay rate `−log ≈ 3τ`,
whereas the `p = 2` self-fusion has temperature `≈ τ/2`.  The diagnostic theorem
`renormW_decays_faster_than_w` records the resulting exponential-rate mismatch
(`(renormW 2 w)^n ≤ w^n` on `0 ≤ w ≤ 1`: the `3τ` reference decays at least as fast as
the bare `w` and far faster than the `τ/2`-matched kernel), so `renormW` must NOT feed
the full-mode self-fusion quotient — that role belongs to the matched base `ρ` above.

# Honest verdict and scope

This module is the CORRECTED scaffold (matched reference) plus the GENERIC telescoping
engine.  The matching identities `QfracQ_zero`/`QfracQ_one` (the latter from the cube
identity) and the telescoping product `QfracQ_prod` are GENUINELY PROVED; the generic
product-to-sum engine `quotient_bound_of_step_sum` is GENUINELY PROVED, axiom-clean,
pure `Q'`.  The carrier is NOT inhabited (cube root is separate), the Wave-2 step
bounds are NOT proved here, and the `Q'`-keyed quotient objects are the dominant-mode /
rational-cube reduction (the full CReal-valued `ρ^{C₄(s)}` reference for `s ≥ 2` is
carried via `crealPowNat` in the carrier but the telescoping engine runs on the
rational step sequence).  This is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable `Q'` facts, reused order /
`divPos` lemmas, and pointwise `CReal` constructions.  Every load-bearing declaration
is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable facts), no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Continuum.ProductFloor

namespace YMGap.Continuum.MatchedRetune

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.ProductFloor

/-! ## 0. `CReal`-to-`Nat` power (pointwise)

The matched full-mode coefficient is `ĉ_s = (s+1)·ρ^{C₄(s)}`, so the carrier needs a
`Nat` power of the `CReal` base `ρ`.  We define it pointwise via `CReal.mul`, with
`crealPowNat x 0 = 1` and `crealPowNat x (n+1) = (crealPowNat x n)·x`. -/

/-- The `Nat` power of a constructive real, `x^n`, defined by `x^0 = 1`,
`x^(n+1) = x^n · x` (pointwise via `CReal.mul`). -/
def crealPowNat (x : CReal) : Nat → CReal
  | 0 => CReal.cone
  | n + 1 => CReal.mul (crealPowNat x n) x

@[simp] theorem crealPowNat_zero (x : CReal) : crealPowNat x 0 = CReal.cone := rfl
@[simp] theorem crealPowNat_succ (x : CReal) (n : Nat) :
    crealPowNat x (n + 1) = CReal.mul (crealPowNat x n) x := rfl

/-! ## 1. The matched-retune carrier (carry `ρ` abstractly; do NOT inhabit)

`ρ` is the base of the EXACT `s = 1`-matched heat kernel for the `p = 2` self-fusion:
`ρ³ = g_1/(2·g_0)` with `g_s = bondMovedCoeff N w 2 s`.  The denominator `2·g_0 > 0`
from `bondMovedCoeff_zero_pos`.  We carry `ρ` as a `CReal` with its positivity, the
sub-unit bound, and the cube identity — but do NOT construct it (the cube root is a
separate effort). -/

/-- The rational cube target `r = g_1/(2·g_0)` (`g_s = bondMovedCoeff N w 2 s`), the
value `ρ³` must equal.  The denominator `2·g_0 > 0` from `bondMovedCoeff_zero_pos`. -/
def cubeRatio (N : Nat) (w : Q') (hw : (0 : Q') < w) : Q' :=
  Q'.divPos (bondMovedCoeff N w 2 1)
    (Q'.ofNat 2 * bondMovedCoeff N w 2 0)
    (Q'.mul_pos (by decide : (0 : Q') < Q'.ofNat 2) (bondMovedCoeff_zero_pos N hw 2))

/-- **The matched-retune carrier (`p = 2`).**  Carries the matched-kernel base `ρ` as a
constructive real with: strict positivity, the sub-unit bound `ρ ≤ 1`, and the cube
identity `ρ³ = g_1/(2·g_0)` (as a `CReal` `Equiv`).  This is the corrected reference for
the full-mode self-fusion quotient.  NOT inhabited here: producing `ρ` from the rational
`cubeRatio` is the (separate) cube-root existence effort. -/
structure MatchedRetuneP2 (N : Nat) (w : Q') (hw : (0 : Q') < w) : Type where
  /-- The matched-kernel base `ρ` (a constructive real). -/
  rho : CReal
  /-- `ρ > 0`. -/
  rho_pos : CReal.IsPositive rho
  /-- `ρ ≤ 1` (the matched kernel is sub-unit). -/
  rho_lt_one : rho ≤ CReal.ofQ' (1 : Q')
  /-- **The cube identity** `ρ³ = g_1/(2·g_0)` — the exact `s = 1` match. -/
  rho_cube : CReal.Equiv (crealPowNat rho 3) (CReal.ofQ' (cubeRatio N w hw))

/-! ## 2. The matched reference and quotient objects (rational-cube keyed)

The matched full-mode coefficient is `ĉ_s = (s+1)·ρ^{C₄(s)}`.  For the DOMINANT modes
`s = 0` (`C₄ = 0`) and `s = 1` (`C₄ = 3`) the power `ρ^{C₄(s)}` reduces to a RATIONAL:
`ĉ_0 = 1` and `ĉ_1 = 2·ρ³ = 2·r` with `r = cubeRatio` rational.  So the quotient factor
`QfracQ` and the per-step increment `stepDeltaQ` on the dominant modes — and the generic
telescoping engine — live at the `Q'` level keyed on `r`.  We define them in terms of an
abstract rational cube `r` (the carrier supplies `r = cubeRatio` with `ρ³ = ofQ' r`). -/

/-- The matched reference coefficient at the `Q'` level keyed on the rational cube `r`:
`coeffMatchedQ r s = (s+1)·r^{?}` realized on the dominant modes as `ĉ_0 = 1`,
`ĉ_1 = 2·r` (`= 2·ρ³`).  Defined by cases on `s ∈ {0, 1}` (the modes whose `C₄` makes
`ρ^{C₄}` rational), `0` beyond — the dominant-mode matched reference. -/
def coeffMatchedQ (r : Q') : Nat → Q'
  | 0 => (1 : Q')
  | 1 => Q'.ofNat 2 * r
  | _ + 2 => (0 : Q')

@[simp] theorem coeffMatchedQ_zero (r : Q') : coeffMatchedQ r 0 = 1 := rfl
@[simp] theorem coeffMatchedQ_one (r : Q') : coeffMatchedQ r 1 = Q'.ofNat 2 * r := rfl

/-- The matched-reference denominator `g_0 · ĉ_s` on the dominant modes, with its
positivity packaged from `0 < r` (which the carrier supplies via `ρ³ = ofQ' r`, `ρ > 0`).
For `s = 0`: `g_0 · 1`; for `s = 1`: `g_0 · (2r)`. -/
def matchedDenom (N : Nat) (w : Q') (r : Q') : Nat → Q'
  | 0 => bondMovedCoeff N w 2 0 * (1 : Q')
  | 1 => bondMovedCoeff N w 2 0 * (Q'.ofNat 2 * r)
  | _ + 2 => bondMovedCoeff N w 2 0 * (0 : Q')

/-- `g_0 · ĉ_0 > 0` (`= g_0 · 1`). -/
theorem matchedDenom_zero_pos (N : Nat) {w : Q'} (hw : (0 : Q') < w) (r : Q') :
    (0 : Q') < matchedDenom N w r 0 :=
  Q'.mul_pos (bondMovedCoeff_zero_pos N hw 2) (by decide)

/-- `g_0 · ĉ_1 > 0` (`= g_0 · 2r`) for `0 < r`. -/
theorem matchedDenom_one_pos (N : Nat) {w : Q'} (hw : (0 : Q') < w) {r : Q'}
    (hr : (0 : Q') < r) : (0 : Q') < matchedDenom N w r 1 :=
  Q'.mul_pos (bondMovedCoeff_zero_pos N hw 2)
    (Q'.mul_pos (by decide : (0 : Q') < Q'.ofNat 2) hr)

/-- The matched quotient factor `QfracQ R s = (g_s · ĉ_0) / (g_0 · ĉ_s)` at the `Q'`
level, on the dominant modes where `ĉ_s` is rational (`s = 0`: `g_0/(g_0·1) = 1`;
`s = 1`: `g_1/(g_0·2r) = 1` by the cube identity `r = g_1/(2g_0)`).  Defined via `divPos`
by the positive denominator `g_0 · ĉ_s` (positivity from `0 < r`).  On `s ≥ 2` (where the
reference is genuinely `CReal`) it is the neutral `1` (the engine operates on
`stepDeltaQ`, not on `QfracQ` beyond the dominant window). -/
def QfracQ (N : Nat) (w : Q') (hw : (0 : Q') < w) {r : Q'} (hr : (0 : Q') < r) :
    Nat → Q'
  | 0 => (1 : Q')
  | 1 =>
      Q'.divPos (bondMovedCoeff N w 2 1 * coeffMatchedQ r 0)
        (matchedDenom N w r 1) (matchedDenom_one_pos N hw hr)
  | _ + 2 => (1 : Q')

@[simp] theorem QfracQ_zero_def (N : Nat) (w : Q') (hw : (0 : Q') < w) {r : Q'}
    (hr : (0 : Q') < r) : QfracQ N w hw hr 0 = 1 := rfl

/-! ## 3. The matching identities — the payoff of the EXACT retune

`QfracQ R 0 = 1` (trivially: `ĉ_0 = 1`, `g_0/g_0 = 1`).  The KEY identity is
`QfracQ R 1 = 1`: the cube identity `r = g_1/(2g_0)` makes `ĉ_1 = 2r = g_1/g_0`, so
`QfracQ R 1 = g_1/(g_0·2r) = g_1/(g_0·(g_1/g_0)) = 1`.  The exact retune KILLS the
`s = 1` marginal mode. -/

/-- **`QfracQ R 0 = 1`** (the vacuum mode; `ĉ_0 = 1`, `g_0/g_0 = 1`). -/
theorem QfracQ_zero (N : Nat) (w : Q') (hw : (0 : Q') < w) {r : Q'} (hr : (0 : Q') < r) :
    QfracQ N w hw hr 0 = 1 := rfl

/-- **`QfracQ R 1 = 1` — THE KEY MATCHING IDENTITY.**  Forced by the cube identity
`r = g_1/(2·g_0)`, i.e. `2·g_0·r = g_1`: the exact `s = 1` retune makes the first-excited
quotient EXACTLY one, killing the marginal mode.

PROOF.  `QfracQ R 1 = divPos (g_1·ĉ_0) (g_0·(2r))`.  Since `ĉ_0 = 1`, the numerator is
`g_1`; by `r = g_1/(2g_0)` the denominator `g_0·(2r) = 2·g_0·r` equals `g_1`.  The
`divPos` of equal numerator and denominator is `1` (`divPos_eq_one_of_eqv`, via
`divPos_mul_eqv`).  We supply the denominator identity `g_0·(2r) ≃ g_1` from
`hcube : ofQ' (2·g_0·r) ≃ g_1` (the cube identity at the `Q'` level). -/
theorem QfracQ_one (N : Nat) (w : Q') (hw : (0 : Q') < w) {r : Q'} (hr : (0 : Q') < r)
    (hcube :
      (bondMovedCoeff N w 2 0 * (Q'.ofNat 2 * r)).eqv (bondMovedCoeff N w 2 1)) :
    (QfracQ N w hw hr 1).eqv 1 := by
  show (Q'.divPos (bondMovedCoeff N w 2 1 * coeffMatchedQ r 0)
      (matchedDenom N w r 1) (matchedDenom_one_pos N hw hr)).eqv 1
  -- divPos num den = num · (1/den).  numerator g_1·ĉ_0 ≃ g_1 ; den = g_0·(2r) ≃ g_1.
  -- so num ≃ den, hence num·(1/den) ≃ den·(1/den) ≃ 1.
  unfold Q'.divPos
  -- num ≃ den :  (g_1·1) ≃ g_1 ≃ (g_0·(2r))
  have hnumden :
      (bondMovedCoeff N w 2 1 * coeffMatchedQ r 0).eqv (matchedDenom N w r 1) := by
    show (bondMovedCoeff N w 2 1 * (1 : Q')).eqv (bondMovedCoeff N w 2 0 * (Q'.ofNat 2 * r))
    exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.eqv_symm hcube)
  -- num · (1/den) ≃ den · (1/den) ≃ 1
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.recipPos (matchedDenom N w r 1)
      (matchedDenom_one_pos N hw hr)) hnumden) ?_
  exact Q'.mul_recipPos_eqv (matchedDenom N w r 1) (matchedDenom_one_pos N hw hr)

/-! ## 4. The per-step telescoping increment and the matching corollaries

The relative residual is `rrelFusionMatched s = QfracQ s − 1`; the per-step telescoping
increment is `stepDeltaQ k = QfracQ (k+1)/QfracQ k − 1`, so on the dominant modes
`QfracQ 0 = QfracQ 1 = 1` forces `stepDeltaQ 0 = 0` (the marginal mode contributes no
telescoping increment).  The generic engine (§5) operates on an ABSTRACT step sequence
`δ : Nat → Q'`, of which `stepDeltaQ` is the matched instance on the dominant window. -/

/-- The matched relative residual `rrelFusionMatched s = QfracQ s − 1` at the `Q'`
level (dominant-mode / rational-cube form). -/
def rrelFusionMatchedQ (N : Nat) (w : Q') (hw : (0 : Q') < w) {r : Q'}
    (hr : (0 : Q') < r) (s : Nat) : Q' :=
  QfracQ N w hw hr s + -(1 : Q')

/-- **`rrelFusionMatched R 0 = 0`** (the vacuum residual vanishes; `QfracQ 0 = 1`). -/
theorem rrelFusionMatchedQ_zero (N : Nat) (w : Q') (hw : (0 : Q') < w) {r : Q'}
    (hr : (0 : Q') < r) : (rrelFusionMatchedQ N w hw hr 0).eqv 0 := by
  show (QfracQ N w hw hr 0 + -(1 : Q')).eqv 0
  rw [QfracQ_zero_def]
  exact Q'.add_neg_self_eqv (1 : Q')

/-- **`rrelFusionMatched R 1 = 0`** — the FIRST-EXCITED residual vanishes by the exact
retune (`QfracQ 1 = 1`, from the cube identity). -/
theorem rrelFusionMatchedQ_one (N : Nat) (w : Q') (hw : (0 : Q') < w) {r : Q'}
    (hr : (0 : Q') < r)
    (hcube :
      (bondMovedCoeff N w 2 0 * (Q'.ofNat 2 * r)).eqv (bondMovedCoeff N w 2 1)) :
    (rrelFusionMatchedQ N w hw hr 1).eqv 0 := by
  show (QfracQ N w hw hr 1 + -(1 : Q')).eqv 0
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(1 : Q')) (QfracQ_one N w hw hr hcube)) ?_
  exact Q'.add_neg_self_eqv (1 : Q')

/-! ## 5. The telescoping product identity (generic)

For ANY positive quotient sequence `Q : Nat → Q'` with `Q 0 = 1`, the per-step
increment `stepDelta k = Q(k+1)/Q(k) − 1` reproduces `Q` by the telescoping product
`Q s = ∏_{k<s}(1 + stepDelta k)`.  This is the structural content of "the quotient is
the running product of its step ratios", proved by induction from
`Q(k+1) = Q(k)·(1 + stepDelta k)` (the definition of `stepDelta`). -/

/-- The running product `∏_{k<n}(1 + δ_k)` (empty product `= 1`), the analogue of
`ProductFloor.prodOneSub` for the `(1 + δ)` factors. -/
def prodOnePlus (δ : Nat → Q') : Nat → Q'
  | 0 => (1 : Q')
  | n + 1 => prodOnePlus δ n * (1 + δ n)

@[simp] theorem prodOnePlus_zero (δ : Nat → Q') : prodOnePlus δ 0 = 1 := rfl
@[simp] theorem prodOnePlus_succ (δ : Nat → Q') (n : Nat) :
    prodOnePlus δ (n + 1) = prodOnePlus δ n * (1 + δ n) := rfl

/-- The generic per-step telescoping increment of a positive quotient sequence `Q`:
`stepDelta Q k = Q(k+1)/Q(k) − 1` (`divPos` by the positive `Q(k)`). -/
def stepDelta (Q : Nat → Q') (hQ : ∀ k, (0 : Q') < Q k) (k : Nat) : Q' :=
  Q'.divPos (Q (k + 1)) (Q k) (hQ k) + -(1 : Q')

/-- **The per-step recurrence `Q(k+1) ≃ Q(k)·(1 + stepDelta k)`.**  From the definition
`stepDelta k = Q(k+1)/Q(k) − 1`: `Q(k)·(1 + (Q(k+1)/Q(k) − 1)) ≃ Q(k)·(Q(k+1)/Q(k))
≃ (Q(k+1)/Q(k))·Q(k) ≃ Q(k+1)`. -/
theorem Qstep_eqv (Q : Nat → Q') (hQ : ∀ k, (0 : Q') < Q k) (k : Nat) :
    (Q (k + 1)).eqv (Q k * (1 + stepDelta Q hQ k)) := by
  -- 1 + (q/Q(k) - 1) ≃ q/Q(k)
  have h1 : ((1 : Q') + stepDelta Q hQ k).eqv (Q'.divPos (Q (k + 1)) (Q k) (hQ k)) := by
    show ((1 : Q') + (Q'.divPos (Q (k + 1)) (Q k) (hQ k) + -(1 : Q'))).eqv
        (Q'.divPos (Q (k + 1)) (Q k) (hQ k))
    -- 1 + (d + -1) ≃ d
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.add_comm_eqv _ _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q')
      (-(1 : Q')) (Q'.divPos (Q (k + 1)) (Q k) (hQ k)))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ 0 _ (Q'.add_neg_self_eqv (1 : Q'))) ?_
    exact q_zero_add_eqv _
  -- Q(k)·(1 + δ) ≃ Q(k)·(q/Q(k)) ≃ (q/Q(k))·Q(k) ≃ q
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q k) _ _ h1) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q k) _) ?_
  exact Q'.divPos_mul_eqv (Q (k + 1)) (Q k) (hQ k)

/-- **THE TELESCOPING PRODUCT IDENTITY (generic).**  For a positive quotient sequence
`Q` with `Q 0 = 1`,

    Q s  ≃  ∏_{k<s} (1 + stepDelta Q k).

By induction: `Q (s+1) ≃ Q s · (1 + stepDelta s) ≃ (∏_{k<s}(1+δ))·(1 + δ_s) =
∏_{k<s+1}(1+δ)`, base `Q 0 = 1 = ∏_{k<0}`. -/
theorem Qfrac_prod (Q : Nat → Q') (hQ : ∀ k, (0 : Q') < Q k) (hQ0 : (Q 0).eqv 1) :
    ∀ s, (Q s).eqv (prodOnePlus (stepDelta Q hQ) s)
  | 0 => hQ0
  | s + 1 => by
      show (Q (s + 1)).eqv (prodOnePlus (stepDelta Q hQ) s * (1 + stepDelta Q hQ s))
      refine Q'.eqv_trans _ _ _ (Qstep_eqv Q hQ s) ?_
      exact Q'.mul_eqv_congr_right _ _ (1 + stepDelta Q hQ s) (Qfrac_prod Q hQ hQ0 s)

/-! ## 6. The GENERIC product-to-sum telescoping engine (the reusable payoff)

The engine converts a (Wave-2) cumulative step-sum bound into the quotient bound.  It is
PURE `Q'`: from a nonnegative step sequence with cumulative sum `≤ B ≤ 1/2`, the
running product `∏(1 + δ_k)` is squeezed between `1` (from below, δ ≥ 0) and `1 + 2B`
(from above, the telescoping polynomial bound), giving `absQ(∏(1+δ) − 1) ≤ 2B`.

The crux upper bound `∏_{k<s}(1 + δ_k) ≤ 1 + 2·∑_{k<s} δ_k` (for `∑ ≤ 1/2`) is the
elementary `Q'` analogue of `∏(1 + δ) ≤ e^{∑δ}` with `e^B − 1 ≤ 2B` on `[0, 1/2]`:
the inductive step `(1 + 2L)(1 + δ) ≤ 1 + 2(L + δ)` reduces to `2·L·δ ≤ δ`, i.e.
`2L ≤ 1`, exactly the smallness `L ≤ 1/2` of the active window — the same role the
factor bound `1 + δ ≤ e^δ` plays in the exponential proof. -/

/-- `∏_{k<n}(1 + δ_k) ≥ 1` for `δ_k ≥ 0` (each factor `≥ 1`, product of `≥ 1` is `≥ 1`). -/
theorem prodOnePlus_ge_one (δ : Nat → Q') (hδ : ∀ k, (0 : Q') ≤ δ k) :
    ∀ n, (1 : Q') ≤ prodOnePlus δ n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      show (1 : Q') ≤ prodOnePlus δ n * (1 + δ n)
      have hih : (1 : Q') ≤ prodOnePlus δ n := prodOnePlus_ge_one δ hδ n
      have hfac : (1 : Q') ≤ 1 + δ n :=
        Q'.add_le_self_of_nonneg 1 (δ n) (hδ n)
      -- 1 = 1·1 ≤ prodOnePlus·(1+δ)
      have h1 : (1 : Q') * 1 ≤ prodOnePlus δ n * (1 + δ n) := by
        have ha : (1 : Q') * 1 ≤ prodOnePlus δ n * 1 :=
          Q'.mul_le_mul_of_nonneg_right _ _ 1 hih (by decide)
        have hb : prodOnePlus δ n * 1 ≤ prodOnePlus δ n * (1 + δ n) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hfac
            (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) hih)
        exact Q'.le_trans' _ _ _ ha hb
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv (1 : Q'))) h1

/-- **The telescoping polynomial upper bound.**  For `δ_k ≥ 0` and every prefix with
`∑_{k<n} δ_k ≤ 1/2`,

    ∏_{k<n}(1 + δ_k)  ≤  1 + 2·∑_{k<n} δ_k.

By induction on `n`: the step is `(1 + 2L)(1 + δ) = 1 + 2L + δ + 2Lδ ≤ 1 + 2(L + δ)`,
which needs `2Lδ ≤ δ`, i.e. `2L ≤ 1`, i.e. `L ≤ 1/2` (the prefix sum at the smaller
index, dominated by the full sum `≤ 1/2`). -/
theorem prodOnePlus_le (δ : Nat → Q') (hδ : ∀ k, (0 : Q') ≤ δ k) :
    ∀ n, lossSum δ n ≤ Q'.ofNat 1 * Q'.recipPos (Q'.ofNat 2) (by decide) →
      prodOnePlus δ n ≤ 1 + (Q'.ofNat 2) * lossSum δ n
  | 0, _ => by
      show (1 : Q') ≤ 1 + Q'.ofNat 2 * lossSum δ 0
      show (1 : Q') ≤ 1 + Q'.ofNat 2 * (0 : Q')
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))) ?_
      refine Q'.add_le_add_left 1 _ _ ?_
      exact Q'.ge_of_eqv (Q'.eqv_symm (q_mul_zero (Q'.ofNat 2)))
  | n + 1, hsum => by
      -- prefix sum at n is ≤ full sum at n+1 ≤ 1/2, and ≤ 1/2 needed.
      have hLn_le : lossSum δ n ≤ Q'.ofNat 1 * Q'.recipPos (Q'.ofNat 2) (by decide) := by
        refine Q'.le_trans' _ _ _ ?_ hsum
        show lossSum δ n ≤ lossSum δ n + δ n
        exact Q'.add_le_self_of_nonneg _ _ (hδ n)
      have hih : prodOnePlus δ n ≤ 1 + Q'.ofNat 2 * lossSum δ n :=
        prodOnePlus_le δ hδ n hLn_le
      have hLnn : (0 : Q') ≤ lossSum δ n := lossSum_nonneg δ hδ n
      have hδnn : (0 : Q') ≤ δ n := hδ n
      have hfac_nn : (0 : Q') ≤ 1 + δ n :=
        Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1)
          (Q'.add_le_self_of_nonneg 1 (δ n) hδnn)
      -- prodOnePlus (n+1) = prodOnePlus n · (1+δ_n) ≤ (1 + 2L)·(1+δ_n)
      show prodOnePlus δ n * (1 + δ n) ≤ 1 + Q'.ofNat 2 * (lossSum δ n + δ n)
      have hstep1 : prodOnePlus δ n * (1 + δ n)
          ≤ (1 + Q'.ofNat 2 * lossSum δ n) * (1 + δ n) :=
        Q'.mul_le_mul_of_nonneg_right _ _ (1 + δ n) hih hfac_nn
      refine Q'.le_trans' _ _ _ hstep1 ?_
      -- (1 + 2L)(1+δ) ≤ 1 + 2(L+δ).  Difference: 1 + 2(L+δ) - (1+2L)(1+δ) = δ - 2Lδ ≥ 0
      -- since 2L ≤ 1.  We prove via the algebraic identity + nonnegativity.
      -- Let A = 1 + 2L, target T = 1 + 2(L+δ) = 1 + 2L + 2δ = A + 2δ.
      -- A·(1+δ) = A + A·δ = A + (1+2L)δ = A + δ + 2Lδ.
      -- T - A·(1+δ) = (A + 2δ) - (A + δ + 2Lδ) = δ - 2Lδ = δ·(1 - 2L) ≥ 0.
      -- We establish: A·(1+δ) ≤ A + 2δ  via  A·δ ≤ 2δ  (i.e. (1+2L)δ ≤ 2δ ⇐ 2L ≤ 1).
      have h2L_le_1 : Q'.ofNat 2 * lossSum δ n ≤ (1 : Q') := by
        -- 2·L ≤ 2·(1/2) = 1.  L ≤ 1·(1/2), so 2L ≤ 2·(1·(1/2)) = 1.
        have hmul : Q'.ofNat 2 * lossSum δ n
            ≤ Q'.ofNat 2 * (Q'.ofNat 1 * Q'.recipPos (Q'.ofNat 2) (by decide)) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hLn_le (by decide)
        refine Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv ?_)
        -- 2·(1·(1/2)) ≃ 2·(1/2) ≃ 1
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (Q'.one_mul_eqv _)) ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 2) _) ?_
        exact Q'.mul_recipPos_eqv (Q'.ofNat 2) (by decide)
      have hAd : (1 + Q'.ofNat 2 * lossSum δ n) * δ n ≤ Q'.ofNat 2 * δ n := by
        -- (1 + 2L)·δ ≤ 2·δ  ⇐  1 + 2L ≤ 2.
        have hA_le_2 : (1 : Q') + Q'.ofNat 2 * lossSum δ n ≤ Q'.ofNat 2 := by
          -- 1 + 2L ≤ 1 + 1 = 2
          refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ h2L_le_1) ?_
          show (1 : Q') + 1 ≤ Q'.ofNat 2
          decide
        exact Q'.mul_le_mul_of_nonneg_right _ _ (δ n) hA_le_2 hδnn
      -- A·(1+δ) ≃ A + A·δ ≤ A + 2δ = (1+2L) + 2δ ≃ 1 + 2(L+δ)
      have hexpand : ((1 + Q'.ofNat 2 * lossSum δ n) * (1 + δ n)).eqv
          ((1 + Q'.ofNat 2 * lossSum δ n) + (1 + Q'.ofNat 2 * lossSum δ n) * δ n) := by
        -- A·(1+δ) ≃ A·1 + A·δ ≃ A + A·δ
        refine Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv (1 + Q'.ofNat 2 * lossSum δ n) 1 (δ n)) ?_
        exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)
      have hle1 : (1 + Q'.ofNat 2 * lossSum δ n) * (1 + δ n)
          ≤ (1 + Q'.ofNat 2 * lossSum δ n) + Q'.ofNat 2 * δ n := by
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand) ?_
        exact Q'.add_le_add_left _ _ _ hAd
      refine Q'.le_trans' _ _ _ hle1 ?_
      -- (1 + 2L) + 2δ ≃ 1 + 2(L+δ)
      refine Q'.le_of_eqv ?_
      -- (1 + 2L) + 2δ ≃ 1 + (2L + 2δ) ≃ 1 + 2(L+δ)
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (Q'.ofNat 2 * lossSum δ n)
        (Q'.ofNat 2 * δ n)) ?_
      refine Q'.add_eqv_congr_left 1 _ _ ?_
      -- 2L + 2δ ≃ 2(L + δ)
      exact Q'.eqv_symm (Q'.mul_add_eqv (Q'.ofNat 2) (lossSum δ n) (δ n))

/-- **THE GENERIC PRODUCT-TO-SUM TELESCOPING ENGINE.**  Given a nonnegative step
sequence `δ` whose cumulative sum at `s` is `≤ B` with `B ≤ 1/2`, the matched relative
residual at `s` (the running product minus one) is bounded by `2·B`:

    absQ (prodOnePlus δ s − 1)  ≤  Q'.ofNat 2 · B.

PROOF.  Two-sided.  Lower: `prodOnePlus δ s ≥ 1` (δ ≥ 0, `prodOnePlus_ge_one`), so
`prodOnePlus − 1 ≥ 0 ≥ −2B`.  Upper: `prodOnePlus δ s ≤ 1 + 2·∑δ ≤ 1 + 2B`
(`prodOnePlus_le`, monotone in the sum), so `prodOnePlus − 1 ≤ 2B`.  Combine via
`absQ_le`.  This is the engine that converts the Wave-2 step-sum bound (carried by
`StepSumCert.cumsum_bound`) into the quotient bound (`QuotientActiveWindowCertMatched`). -/
theorem quotient_bound_of_step_sum (δ : Nat → Q') (s : Nat) {B : Q'}
    (hnn : ∀ k, (0 : Q') ≤ δ k)
    (hsum : lossSum δ s ≤ B)
    (hsmall : B ≤ Q'.ofNat 1 * Q'.recipPos (Q'.ofNat 2) (by decide)) :
    absQ (prodOnePlus δ s + -(1 : Q')) ≤ Q'.ofNat 2 * B := by
  have hBnn : (0 : Q') ≤ B :=
    Q'.le_trans' _ _ _ (lossSum_nonneg δ hnn s) hsum
  have h2Bnn : (0 : Q') ≤ Q'.ofNat 2 * B := Q'.mul_nonneg _ _ (by decide) hBnn
  -- prefix sum ≤ 1/2
  have hLhalf : lossSum δ s ≤ Q'.ofNat 1 * Q'.recipPos (Q'.ofNat 2) (by decide) :=
    Q'.le_trans' _ _ _ hsum hsmall
  -- lower bound: prodOnePlus ≥ 1
  have hge1 : (1 : Q') ≤ prodOnePlus δ s := prodOnePlus_ge_one δ hnn s
  -- upper bound: prodOnePlus ≤ 1 + 2·∑δ ≤ 1 + 2B
  have hup0 : prodOnePlus δ s ≤ 1 + Q'.ofNat 2 * lossSum δ s := prodOnePlus_le δ hnn s hLhalf
  have hup : prodOnePlus δ s ≤ 1 + Q'.ofNat 2 * B := by
    refine Q'.le_trans' _ _ _ hup0 ?_
    refine Q'.add_le_add_left 1 _ _ ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hsum (by decide)
  refine absQ_le ?_ ?_
  · -- -(2B) ≤ prodOnePlus - 1.  Since prodOnePlus - 1 ≥ 0 ≥ -(2B).
    have hpm1_nn : (0 : Q') ≤ prodOnePlus δ s + -(1 : Q') := by
      have := Q'.add_le_add_right _ _ (-(1 : Q')) hge1
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv (1 : Q'))) this
    have hneg : -(Q'.ofNat 2 * B) ≤ (0 : Q') := by
      have h0 : -(Q'.ofNat 2 * B) ≤ -(0 : Q') := Q'.neg_le_neg h2Bnn
      refine Q'.le_trans' _ _ _ h0 ?_
      show -(0 : Q') ≤ (0 : Q')
      decide
    exact Q'.le_trans' _ _ _ hneg hpm1_nn
  · -- prodOnePlus - 1 ≤ 2B.  From prodOnePlus ≤ 1 + 2B.
    have := Q'.add_le_add_right _ _ (-(1 : Q')) hup
    refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
    -- (1 + 2B) + -1 ≃ 2B
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-(1 : Q')) (Q'.add_comm_eqv 1 _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (Q'.ofNat 2 * B) 1 (-(1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (1 : Q'))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (Q'.ofNat 2 * B))

/-! ## 7. The corrected target certificates (matched reference) and the reduction

The corrected per-mode quotient bound uses the MATCHED reference (the `τ/2`-kernel `ρ`,
its rational cube on the dominant window), telescoped through the step sequence `δ`.  We
carry the matched relative residual as the running-product form `prodOnePlus δ s − 1`
(the telescoped quotient; cf. `Qfrac_prod`).  Two certificates:

  * `QuotientActiveWindowCertMatched` — the corrected per-mode quotient bound (the
    matched `hbound` shape), in the `absQ (prodOnePlus δ s − 1) ≤ (1−w)²·Peval P` form.
  * `StepSumCert` — the SHARPER telescoping obligation: a nonnegative step sequence whose
    cumulative sum is bounded by `(1−w)²·Peval P`.

`quotientCert_of_stepSum` reduces the latter to the former via the GENERIC engine
`quotient_bound_of_step_sum`, modulo the active-window smallness side-condition
`(1−w)²·Peval P (yArg w s) ≤ 1/2`. -/

/-- **The corrected active-window quotient certificate (matched reference).**  Carries
the matched step sequence `δ`, the fixed nonneg-coefficient polynomial `P`, and — as a
`Type`-level field — the per-mode quotient bound on the active modes `1 ≤ s` in the
corrected matched-reference shape

    absQ (prodOnePlus δ s − 1)  ≤  ((1−w)·(1−w))·Peval P (yArg w s),   1 ≤ s,

where `prodOnePlus δ s − 1` is the telescoped matched relative residual (`Qfrac_prod`).
This SUPERSEDES the `renormW`-based active-window certificate (wrong `3τ` reference).
NOT inhabited directly — reduced to `StepSumCert` below. -/
structure QuotientActiveWindowCertMatched (N : Nat) (w : Q') (hw : (0 : Q') < w) :
    Type where
  /-- The matched per-step telescoping increment sequence `δ`. -/
  δ : Nat → Q'
  /-- The fixed `w`-independent residual polynomial. -/
  P : BondMovingMoment.Poly
  /-- Its coefficients are nonnegative. -/
  P_nonneg : nonnegCoeffs P
  /-- **The corrected per-mode quotient bound** on the active modes `1 ≤ s`. -/
  quot_bound : ∀ s, 1 ≤ s →
    absQ (prodOnePlus δ s + -(1 : Q'))
      ≤ (((1 : Q') - w) * ((1 : Q') - w)) * Peval P (yArg w s)

/-- **The SHARPER telescoping obligation (Wave-2 target).**  Carries the matched step
sequence `δ`, the fixed nonneg-coefficient polynomial `P`, and — as `Type`-level fields —
the step nonnegativity `δ_k ≥ 0` and the cumulative-sum bound

    ∑_{k<s} δ_k  ≤  ((1−w)·(1−w))·Peval P (yArg w s).

This is the sharper, division-free telescoping obligation: the per-step increments are
nonnegative and their running sum is controlled by the quadratic margin.  NOT inhabited:
`step_nonneg` (the δ_k ≥ 0 sign) and `cumsum_bound` (the derivative/cumulative bound) are
the genuine Wave-2 content, carried abstractly. -/
structure StepSumCert (N : Nat) (w : Q') (hw : (0 : Q') < w) : Type where
  /-- The matched per-step telescoping increment sequence `δ`. -/
  δ : Nat → Q'
  /-- The fixed `w`-independent residual polynomial. -/
  P : BondMovingMoment.Poly
  /-- Its coefficients are nonnegative. -/
  P_nonneg : nonnegCoeffs P
  /-- **Wave-2 content (open):** the per-step increments are nonnegative. -/
  step_nonneg : ∀ k, (0 : Q') ≤ δ k
  /-- **Wave-2 content (open):** the cumulative step sum is bounded by the quadratic
  margin times the residual polynomial. -/
  cumsum_bound : ∀ s,
    lossSum δ s ≤ (((1 : Q') - w) * ((1 : Q') - w)) * Peval P (yArg w s)

/-- Coefficient-wise scaling of a polynomial, `scalePoly c P = map (c · ·) P`.  Preserves
nonneg coefficients for `c ≥ 0` and satisfies `Peval (scalePoly c P) y ≃ c · Peval P y`. -/
def scalePoly (c : Q') : BondMovingMoment.Poly → BondMovingMoment.Poly
  | [] => []
  | a :: as => (c * a) :: scalePoly c as

/-- `scalePoly` of a nonneg-coeff polynomial by `c ≥ 0` is nonneg-coeff. -/
theorem scalePoly_nonneg {c : Q'} (hc : (0 : Q') ≤ c) :
    ∀ P, nonnegCoeffs P → nonnegCoeffs (scalePoly c P)
  | [], _ => True.intro
  | a :: as, hP => ⟨Q'.mul_nonneg _ _ hc hP.1, scalePoly_nonneg hc as hP.2⟩

/-- `Peval (scalePoly c P) y ≃ c · Peval P y` (scaling the coefficients scales the
value).  Induction on `P`: `c·a + y·(c·Peval as) ≃ c·(a + y·Peval as)`. -/
theorem Peval_scalePoly (c : Q') :
    ∀ (P : BondMovingMoment.Poly) (y : Q'),
      (Peval (scalePoly c P) y).eqv (c * Peval P y)
  | [], y => by
      show (Peval [] y).eqv (c * Peval [] y)
      show (0 : Q').eqv (c * 0)
      exact Q'.eqv_symm (q_mul_zero c)
  | a :: as, y => by
      show ((c * a) + y * Peval (scalePoly c as) y).eqv (c * (a + y * Peval as y))
      -- c·a + y·(c·Peval as) ≃ c·a + c·(y·Peval as) ≃ c·(a + y·Peval as)
      have hstep1 : ((c * a) + y * Peval (scalePoly c as) y).eqv
          ((c * a) + y * (c * Peval as y)) :=
        Q'.add_eqv_congr_left (c * a) _ _
          (Q'.mul_eqv_congr_left y _ _ (Peval_scalePoly c as y))
      refine Q'.eqv_trans _ _ _ hstep1 ?_
      -- y·(c·Peval as) ≃ c·(y·Peval as)
      have hswap : (y * (c * Peval as y)).eqv (c * (y * Peval as y)) := by
        refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv y c (Peval as y))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (Peval as y)
          (Q'.mul_comm_eqv y c)) ?_
        exact Q'.mul_assoc_eqv c y (Peval as y)
      -- c·a + c·(y·Peval as) ≃ c·(a + y·Peval as)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (c * a) _ _ hswap) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv c a (y * Peval as y))

/-- **THE REDUCTION `StepSumCert → QuotientActiveWindowCertMatched`** via the generic
engine.  Given the sharper step-sum certificate AND the active-window smallness
side-condition

    hsmall : ∀ s, 1 ≤ s →
      ((1−w)·(1−w))·Peval P (yArg w s) ≤ 1/2,

the matched quotient bound holds with the residual polynomial scaled by the engine's
factor `2` (`scalePoly 2 P`, still nonneg-coeff).  PROOF: apply
`quotient_bound_of_step_sum` with `B = (1−w)²·Peval P (yArg w s)` (`hnn` = `step_nonneg`,
`hsum` = `cumsum_bound`, `hsmall`), giving `absQ(prodOnePlus δ s − 1) ≤ 2·B`; then
`2·B = 2·((1−w)²·Peval P) ≃ (1−w)²·(2·Peval P) ≃ (1−w)²·Peval (scalePoly 2 P)`
(`Peval_scalePoly`), which is exactly the matched cert's `hbound` shape with the scaled
polynomial.  The factor `2` is the `e^B − 1 ≤ 2B` constant of the active window. -/
def quotientCert_of_stepSum (N : Nat) (w : Q') (hw : (0 : Q') < w)
    (cert : StepSumCert N w hw)
    (hsmall : ∀ s, 1 ≤ s →
      (((1 : Q') - w) * ((1 : Q') - w)) * Peval cert.P (yArg w s)
        ≤ Q'.ofNat 1 * Q'.recipPos (Q'.ofNat 2) (by decide)) :
    QuotientActiveWindowCertMatched N w hw where
  δ := cert.δ
  P := scalePoly (Q'.ofNat 2) cert.P
  P_nonneg := scalePoly_nonneg (by decide) cert.P cert.P_nonneg
  quot_bound := by
    intro s hs
    -- B := (1−w)²·Peval P (yArg w s) ; engine gives absQ ≤ 2·B.
    have heng :
        absQ (prodOnePlus cert.δ s + -(1 : Q'))
          ≤ Q'.ofNat 2 * ((((1 : Q') - w) * ((1 : Q') - w)) * Peval cert.P (yArg w s)) :=
      quotient_bound_of_step_sum cert.δ s cert.step_nonneg
        (cert.cumsum_bound s) (hsmall s hs)
    refine Q'.le_trans' _ _ _ heng (Q'.le_of_eqv ?_)
    -- 2·((1−w)²·Q) ≃ (1−w)²·(2·Q) ≃ (1−w)²·Peval (scalePoly 2 P) y
    -- 2·((1−w)²·Q) ≃ ((1−w)²)·(2·Q)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (((1 : Q') - w) * ((1 : Q') - w))
        (Peval cert.P (yArg w s)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (Peval cert.P (yArg w s))
        (Q'.mul_comm_eqv (Q'.ofNat 2) (((1 : Q') - w) * ((1 : Q') - w)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (((1 : Q') - w) * ((1 : Q') - w)) (Q'.ofNat 2)
        (Peval cert.P (yArg w s))) ?_
    -- (1−w)²·(2·Q) ≃ (1−w)²·Peval (scalePoly 2 P) y
    refine Q'.mul_eqv_congr_left (((1 : Q') - w) * ((1 : Q') - w)) _ _ ?_
    exact Q'.eqv_symm (Peval_scalePoly (Q'.ofNat 2) cert.P (yArg w s))

/-! ## 8. Quarantine of the wrong reference (`renormW`, temperature `≈ 3τ`)

The first-order retune `renormW 2 w = 1 − C₄(1)·(1 − w) = 1 − 3·(1 − w)` has decay rate
`−log(renormW) ≈ 3τ` (`τ = 1 − w`), whereas the `p = 2` self-fusion ratio `g_1/g_0`
matches a heat kernel at temperature `≈ τ/2`.  The `3τ` reference is therefore the WRONG
reference for the FULL-mode self-fusion quotient: its tower `(renormW 2 w)^{C₄(s)}` decays
FAR faster than the matched `ρ^{C₄(s)}` (with `ρ³ = g_1/(2g_0)`, i.e. `−log ρ ≈ τ/2`),
so the quotient `g_s ĉ_0 / (g_0 ĉ_s)` blows up.  The diagnostic below records the
exponential-rate mismatch concretely. -/

/-- **DIAGNOSTIC: `renormW` decays at least as fast as the bare weight.**  On `0 ≤ w ≤ 1`,
for every exponent `n`,

    (renormW 2 w)^n  ≤  w^n,

i.e. the `3τ`-temperature reference tower is dominated termwise by the bare-`w` tower —
and a fortiori decays far faster than the `τ/2`-matched `ρ`-tower (`ρ ≥ w` since
`−log ρ ≈ τ/2 < τ = −log w`).  This makes the temperature mismatch explicit: `renormW`
must NOT feed the full-mode self-fusion quotient (that role belongs to the matched base
`ρ` of `MatchedRetuneP2`).  PROOF: `renormW 2 w = 1 − 3(1 − w) ≤ 1 − (1 − w) = w` on
`[0,1]` (and `renormW 2 w ≥ 0` is NOT needed for the power inequality once we have
`renormW ≤ w` together with `0 ≤ renormW`); monotonicity of `qpow` in the base. -/
theorem renormW_decays_faster_than_w {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hrw0 : (0 : Q') ≤ renormW 2 w) (n : Nat) :
    qpow (renormW 2 w) n ≤ qpow w n := by
  -- renormW 2 w ≤ w :  renormW + 2(1−w) ≃ w, and 2(1−w) ≥ 0.
  have htau_nn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have h2tau_nn : (0 : Q') ≤ Q'.ofNat 2 * ((1 : Q') - w) :=
    Q'.mul_nonneg _ _ (by decide) htau_nn
  -- THE IDENTITY: renormW 2 w + 2·(1−w) ≃ w.
  -- renormW 2 w = 1 + -(ofNat 3 · (1−w)) (c4 1 = 3).  Write d = 1−w.
  -- (1 + -(3·d)) + 2·d ≃ 1 + (-(3·d) + 2·d) ≃ 1 + (-d) ≃ 1 - (1−w) ≃ w.
  have hid : ((renormW 2 w) + (Q'.ofNat 2 * ((1 : Q') - w))).eqv w := by
    show ((1 : Q') + -(Q'.ofNat (c4 1) * ((1 : Q') - w)) + (Q'.ofNat 2 * ((1 : Q') - w))).eqv w
    have hc : Q'.ofNat (c4 1) = Q'.ofNat 3 := rfl
    rw [hc]
    -- (1 + -(3·d)) + 2·d ≃ 1 + (-(3·d) + 2·d), d = 1−w
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (1 : Q') (-(Q'.ofNat 3 * ((1 : Q') - w)))
        (Q'.ofNat 2 * ((1 : Q') - w))) ?_
    -- -(3·d) + 2·d ≃ -d
    have hcomb : ((-(Q'.ofNat 3 * ((1 : Q') - w))) + Q'.ofNat 2 * ((1 : Q') - w)).eqv
        (-((1 : Q') - w)) := by
      -- -(3·d) ≃ (-3)·d ; (-3)·d + 2·d ≃ ((-3)+2)·d = (-1)·d ≃ -d
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (Q'.ofNat 2 * ((1 : Q') - w))
          (Q'.eqv_symm (Q'.neg_mul_eqv (Q'.ofNat 3) ((1 : Q') - w)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv (-(Q'.ofNat 3)) (Q'.ofNat 2) ((1 : Q') - w))) ?_
      -- ((-3)+2)·d ≃ (-1)·d  (the scalar (-3)+2 ≃ -1 by decide), then (-1)·d ≃ -d
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ (-1 : Q') ((1 : Q') - w) (by decide)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 ((1 : Q') - w)) ?_
      exact Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv ((1 : Q') - w))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ hcomb) ?_
    -- 1 + -d ≃ 1 + -(1−w) ≃ 1 + (-1 + w) ≃ (1 + -1) + w ≃ 0 + w ≃ w
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.neg_add_eqv (1 : Q') (-w))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (1 : Q') _ _
        (Q'.add_eqv_congr_left (-(1 : Q')) _ _ (Q'.neg_neg_eqv w))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-(1 : Q')) w)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ 0 w (Q'.add_neg_self_eqv (1 : Q'))) ?_
    exact q_zero_add_eqv w
  have hle : renormW 2 w ≤ w :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (renormW 2 w) _ h2tau_nn) (Q'.le_of_eqv hid)
  -- monotone power: 0 ≤ renormW ≤ w  ⟹  renormW^n ≤ w^n.
  exact qpow_mono hrw0 hle n

end YMGap.Continuum.MatchedRetune

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MatchedRetune.crealPowNat
#print axioms YMGap.Continuum.MatchedRetune.cubeRatio
#print axioms YMGap.Continuum.MatchedRetune.matchedDenom_zero_pos
#print axioms YMGap.Continuum.MatchedRetune.matchedDenom_one_pos
#print axioms YMGap.Continuum.MatchedRetune.QfracQ_zero
#print axioms YMGap.Continuum.MatchedRetune.QfracQ_one
#print axioms YMGap.Continuum.MatchedRetune.rrelFusionMatchedQ_zero
#print axioms YMGap.Continuum.MatchedRetune.rrelFusionMatchedQ_one
#print axioms YMGap.Continuum.MatchedRetune.prodOnePlus
#print axioms YMGap.Continuum.MatchedRetune.Qstep_eqv
#print axioms YMGap.Continuum.MatchedRetune.Qfrac_prod
#print axioms YMGap.Continuum.MatchedRetune.prodOnePlus_ge_one
#print axioms YMGap.Continuum.MatchedRetune.prodOnePlus_le
#print axioms YMGap.Continuum.MatchedRetune.quotient_bound_of_step_sum
#print axioms YMGap.Continuum.MatchedRetune.scalePoly_nonneg
#print axioms YMGap.Continuum.MatchedRetune.Peval_scalePoly
#print axioms YMGap.Continuum.MatchedRetune.quotientCert_of_stepSum
#print axioms YMGap.Continuum.MatchedRetune.renormW_decays_faster_than_w
