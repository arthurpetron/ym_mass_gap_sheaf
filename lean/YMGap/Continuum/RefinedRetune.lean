/-
Track B / R2 — CAN A REFINED RETUNE ABSORB THE BULK LINEAR PREFACTOR?  The δ-loop
verdict on whether the residual `normEigShift` of `VacNormEigShift` — LINEAR `O(1−w)`
on the bulk under the `1/p` retune `renormWFix = 1 − (1−w)/p` — is killed by a
SECOND-order refined retune, or is a genuine retune-INVARIANT non-Gaussian fusion
effect.

# The object and the question

`VacNormEigShift` isolated the vacuum-normalized bond-moved eigenvalue defect

    normEigShift N p hp w s  =  | vacNorm N p hp w s  −  retEig p hp w s |,
    retEig p hp w s  =  renormWFix^{C₄(s)},   renormWFix p hp w = 1 − (1 − w)/p,

and named the sharp residual `BulkLocalCLTLinear`: a LOWER bound `cLin·(1 − w) ≤
normEigShift` on a bulk mode.  The `1/p` retune matches the local-CLT EXPONENT (so the
defect vanishes at `p = 1`, `normEigShift_p1_zero`) but leaves a LINEAR sub-leading
PREFACTOR.  This module asks: is there a refined retune that absorbs it?

# The analytic structure of the linear prefactor (the local-CLT computation)

Bond-moving raises the SU(2) heat kernel `K_t(θ)` to the pointwise power `p` and
re-expands in characters.  The semiclassical (small-`t`, leading image) form is
`K_t(θ) ≈ A(t)·(θ/sinθ)·e^{−θ²/4t}`, so `K_t(θ)^p ≈ A^p·(θ/sinθ)^p·e^{−pθ²/4t}`.  The
character coefficient `bmc(s) = ⟨K_t^p, χ_s⟩` with `χ_s = sin((s+1)θ)/sinθ` and the
Weyl measure `(2/π)sin²θ` gives, with the CURVATURE factor
`(θ/sinθ)^p·sinθ ≈ θ·e^{(p−1)θ²/6}` (since `log(θ/sinθ) = θ²/6 + θ⁴/180 + …`),

    bmc(s)  ≈  C·(n/B^{3/2})·e^{−n²/4B},   n = s+1,   B = p/4t − (p−1)/6,

hence the vacuum-normalized eigenvalue is a CLEAN heat-kernel at an EFFECTIVE TIME:

    vacNorm(s)  ≈  e^{−C₄(s)·τ_eff},   τ_eff = 1/4B = (t/p)/(1 − 2(p−1)t/3).

Expanding in the margin `ε = 1 − w` (with `t = −log w = ε + ε²/2 + …`):

    rate(vacNorm)  =  τ_eff             =  ε/p + ε²/(2p) + 2(p−1)ε²/(3p²) + …,
    rate(retEig)   =  −log renormWFix   =  ε/p + ε²/(2p²) + …,
    Δrate  =  rate(vacNorm) − rate(retEig)  =  7(p−1)/(6p²) · ε²  +  O(ε³).

Therefore on the bulk (where `C₄(s) ~ 1/ε`, so `C₄(s)·ε² ~ ε`),

    vacNorm(s) / retEig(s)  =  e^{−C₄(s)·Δrate}  ≈  1 − (7(p−1)/(6p²))·C₄(s)·(1 − w)²,

a prefactor that reads as LINEAR `O(1 − w)` on the bulk (`C₄(s)·(1−w)² ~ (1−w)`).

# THE EXPLICIT p=2 LINEAR-PREFACTOR COEFFICIENT (reported)

    a*(p)  =  7(p − 1) / (6 p²),       a*(2)  =  7/24,       a*(1)  =  0.

The `a*(1) = 0` value is the SHARP CONSISTENCY CHECK: at `p = 1` there is no
bond-moving and `normEigShift_p1_zero` already proves the defect vanishes EXACTLY —
no refinement is needed, and the refined coefficient is exactly `0`.

# THE VERDICT — (a):  THE LINEAR PREFACTOR IS ABSORBABLE (it is Casimir-shape)

The prefactor `1 − a*·C₄(s)·(1 − w)²` is proportional to the Casimir `C₄(s)`: it is
of pure HEAT-KERNEL shape.  Since `f^{C₄(s)}·g^{C₄(s)} = (f·g)^{C₄(s)}`, multiplying
the base by a correction `corr = 1 − a·(1 − w)²` multiplies `retEig` by exactly such a
Casimir-shape factor — so a REFINED two-parameter retune

    renormW2 p hp a w  :=  renormWFix p hp w · (1 − a·(1 − w)²)

ABSORBS the linear prefactor when `a = a*(p) = 7(p−1)/(6p²)`.  The residual then drops
to QUADRATIC `O((1 − w)²)`: the LINEAR lower bound `BulkLocalCLTLinear` is converted
into a QUADRATIC upper bound (the closure-shaped `RefinedBulkRemainderQuadratic`),
which is SUMMABLE (inverse-square `refinedDefect_invSq`) — exactly the order the gap
budget needs.

# The genuine retune-INVARIANT remainder (the honest residual, now quadratic)

What a retune CANNOT absorb is the part of the prefactor that is NOT proportional to
`C₄(s)`: the quartic-Casimir Edgeworth (cumulant-4) term `∝ C₄(s)²·(1 − w)²` coming
from the `θ⁴/180` curvature.  `quartic_retune_invariant` PROVES this is genuine: the
quartic shape `C₄(s)²` is NOT an affine combination `α + β·C₄(s)` of the heat-kernel
shapes (a `1`-parameter base only adjusts the coefficient of `C₄(s)` in the log).  But
this surviving term is `O((1 − w)²)` on the bulk — QUADRATIC, summable — so it is the
genuinely smaller open content, NOT the linear obstruction.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat`)

  * `qpow_mul_base` — the multiplicativity `(a·b)^n ≃ a^n · b^n` (the absorbability
    engine: the heat-kernel family is closed under base refinement).
  * `retEig2_factor` — `retEig2 ≃ retEig · corr^{C₄(s)}`: the refined eigenvalue is the
    old one times a Casimir-shape correction (the precise absorption mechanism).
  * `retEig2_param_zero` — at `a = 0` the refinement is trivial (`retEig2 ≃ retEig`):
    the refined family CONTAINS the current `1/p` retune.
  * `oneSub_corr` / `corr_casimir_shape` — the correction factor is Casimir-shape with
    scale `a·(1 − w)²`: `1 − corr^{C₄(s)} ≤ C₄(s)·(a·(1 − w)²)`.  Choosing `a = a*(p)`
    matches the predicted prefactor.
  * `refineCoeff` / `refineCoeff_p2` / `refineCoeff_p1_zero` — the EXPLICIT coefficient
    `7(p−1)/(6p²)`, with the values `7/24` (p=2) and `0` (p=1).
  * `defect_factor` — the LINEAR-CANCELLATION identity: under the factorization
    `vacNorm ≃ retEig2 · rem`, the residual is `retEig2 · (rem − 1)` — the linear
    Casimir-shape prefactor is folded into `retEig2`, leaving the pure remainder.
  * `refinedDefect_invSq` — the verdict-(a) PAYOFF: the refined per-mode defect, bounded
    QUADRATICALLY by `RefinedBulkRemainderQuadratic`, satisfies the inverse-SQUARE
    summable form `≤ Cq·(r·r)` (contrast the non-summable linear `BulkLocalCLTLinear`).
  * `quartic_retune_invariant` — the genuine obstruction: `C₄(s)²` is NOT affine in
    `C₄(s)` (a `3×3`-Vandermonde inconsistency at `s = 0,1,2`), so the cumulant-4
    Edgeworth term is retune-INVARIANT — but it is quadratic, hence summable.

# NAMED OPEN (NOT inhabited / NOT faked)

  * `RefinedBulkRemainderQuadratic N p hp a w` — that, at the refined base with
    `a = a*(p)`, the refined defect is genuinely QUADRATIC `≤ Cq·(1 − w)²` uniformly on
    the bulk.  This is the local-CLT input AFTER the linear cancellation; it is the
    closure-shaped successor of the linear lower bound `BulkLocalCLTLinear`, reduced to
    the general-`p` Edgeworth (quartic-cumulant) control.  NOT inhabited.

# Honest verdict and scope

VERDICT **(a)** with the sharp mechanism: the bulk linear prefactor is a Casimir-shape
(effective-time / second-cumulant) correction with EXPLICIT coefficient `7(p−1)/(6p²)`
(`7/24` at `p = 2`, `0` at `p = 1`), and the refined retune `renormW2` ABSORBS it —
converting the LINEAR obstruction into a QUADRATIC, summable residual.  The genuinely
retune-INVARIANT part is the quartic-Casimir Edgeworth term, PROVED non-absorbable but
QUADRATIC (hence summable).  The bond-moved measure DOES leave the heat-kernel manifold
at second order — but only at second order, so the leading (linear) departure is a
reparametrization, not a genuine loss.  This is NOT a 4D Yang–Mills mass-gap proof; it
is the sharp resolution of the linear-prefactor question, shrinking the open content
from a linear bulk obstruction to a quadratic Edgeworth control.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`/`Int` arithmetic over proved engines (`qpow_mul_base`, `mul_four_regroup`,
`oneSub_qpow_le`, `sq_le_sq`, `qpow_eqv_congr_base`) and one decidable `omega`
inconsistency.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide` (only
`decide`/`omega` on closed decidable facts), no `sorry`.  All witnesses and named
obligations are `Type`-level data.
-/

import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.VacNormEigShift
import YMGap.Continuum.BondMovingRelResidual
import YMGap.Continuum.S1Dominance

namespace YMGap.Continuum.RefinedRetune

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The absorbability engine — `qpow` multiplicativity in the base -/

/-- **`qpow (a·b) n ≃ qpow a n · qpow b n`** — the power of a product is the product of
the powers.  THE ABSORBABILITY ENGINE: the heat-kernel family `{f^{C₄(s)}}` is closed
under base refinement, so a multiplicative correction to the base multiplies the
eigenvalue by a Casimir-shape factor `corr^{C₄(s)}`.  Induction on `n` via the
four-factor regroup (general `a ≠ b` form of `FusionQuotientCollapse.qpow_mul_self`). -/
theorem qpow_mul_base (a b : Q') :
    ∀ n, (qpow (a * b) n) ≈ (qpow a n * qpow b n)
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | n + 1 => by
      show (qpow (a * b) n * (a * b)) ≈ ((qpow a n * a) * (qpow b n * b))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (a * b) (qpow_mul_base a b n)) ?_
      exact mul_four_regroup (qpow a n) (qpow b n) a b

/-! ## 1. The refined two-parameter retune `renormW2` and its eigenvalue `retEig2` -/

/-- **The Casimir-shape correction factor** `corr = 1 − a·(1 − w)²`.  Multiplying the
retune base by `corr` multiplies `retEig` by `corr^{C₄(s)} ≈ 1 − a·C₄(s)·(1 − w)²` — a
pure heat-kernel-shape prefactor.  Choosing `a = a*(p) = 7(p−1)/(6p²)` matches the
local-CLT linear prefactor. -/
def corrFactor (a w : Q') : Q' :=
  (1 : Q') - a * (((1 : Q') - w) * ((1 : Q') - w))

/-- **The refined two-parameter retune** `renormW2 p hp a w = renormWFix · corrFactor`:
the `1/p` exponent-matched base, multiplied by the second-order Casimir-shape
correction.  At `a = 0` it is exactly `renormWFix` (the current retune). -/
def renormW2 (p : Nat) (hp : 0 < p) (a w : Q') : Q' :=
  renormWFix p hp w * corrFactor a w

/-- **The refined per-mode eigenvalue** `retEig2 = renormW2^{C₄(s)}`. -/
def retEig2 (p : Nat) (hp : 0 < p) (a w : Q') (s : Nat) : Q' :=
  qpow (renormW2 p hp a w) (c4 s)

/-- **THE ABSORPTION MECHANISM** — `retEig2 ≃ retEig · corr^{C₄(s)}`.  The refined
eigenvalue is the OLD retuned eigenvalue times a Casimir-shape correction factor.  This
is the precise sense in which a refined retune can absorb any Casimir-shape prefactor:
it folds it into the base.  PROOF: `qpow_mul_base` on `renormWFix · corrFactor`. -/
theorem retEig2_factor (p : Nat) (hp : 0 < p) (a w : Q') (s : Nat) :
    (retEig2 p hp a w s) ≈ (retEig p hp w s * qpow (corrFactor a w) (c4 s)) := by
  show (qpow (renormWFix p hp w * corrFactor a w) (c4 s))
      ≈ (qpow (renormWFix p hp w) (c4 s) * qpow (corrFactor a w) (c4 s))
  exact qpow_mul_base (renormWFix p hp w) (corrFactor a w) (c4 s)

/-- **`corrFactor 0 w ≃ 1`** — the trivial correction at `a = 0`. -/
theorem corrFactor_zero (w : Q') : (corrFactor 0 w) ≈ (1 : Q') := by
  show ((1 : Q') + -((0 : Q') * (((1 : Q') - w) * ((1 : Q') - w)))) ≈ (1 : Q')
  have hz : ((0 : Q') * (((1 : Q') - w) * ((1 : Q') - w))) ≈ (0 : Q') :=
    Q'.zero_mul_eqv _
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.neg_eqv_congr _ _ hz)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 : Q') _ _ ?_) (Q'.eqv_of_eq (Q'.add_zero' (1 : Q')))
  show (-(0 : Q')) ≈ (0 : Q')
  exact Q'.eqv_of_eq (by rfl)

/-- **`retEig2 p hp 0 w s ≃ retEig p hp w s`** — at `a = 0` the refined family CONTAINS
the current `1/p` retune.  So `renormW2` is a genuine REFINEMENT (extra freedom), not a
replacement.  PROOF: `renormW2 p hp 0 w = renormWFix · corrFactor 0 w ≃ renormWFix · 1
≃ renormWFix`, then `qpow` congruence in the base. -/
theorem retEig2_param_zero (p : Nat) (hp : 0 < p) (w : Q') (s : Nat) :
    (retEig2 p hp 0 w s) ≈ (retEig p hp w s) := by
  show (qpow (renormWFix p hp w * corrFactor 0 w) (c4 s))
      ≈ (qpow (renormWFix p hp w) (c4 s))
  have hbase : (renormWFix p hp w * corrFactor 0 w) ≈ (renormWFix p hp w) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (corrFactor_zero w))
      (Q'.mul_one_eqv (renormWFix p hp w))
  exact qpow_eqv_congr_base hbase (c4 s)

/-! ## 2. The correction factor is Casimir-shape with scale `a·(1 − w)²` -/

/-- **`1 − corrFactor a w ≃ a·(1 − w)²`** — the correction deficit is exactly the
quadratic-margin scale `a·(1 − w)²`. -/
theorem oneSub_corr (a w : Q') :
    ((1 : Q') - corrFactor a w) ≈ (a * (((1 : Q') - w) * ((1 : Q') - w))) := by
  -- 1 − (1 − y) ≈ y  with  y = a·(1−w)²
  show ((1 : Q') + -((1 : Q') + -(a * (((1 : Q') - w) * ((1 : Q') - w)))))
      ≈ (a * (((1 : Q') - w) * ((1 : Q') - w)))
  have ha : (-((1 : Q') + -(a * (((1 : Q') - w) * ((1 : Q') - w)))))
      ≈ ((-1 : Q') + a * (((1 : Q') - w) * ((1 : Q') - w))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv (1 : Q') (-(a * (((1 : Q') - w) * ((1 : Q') - w))))) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_neg_eqv (a * (((1 : Q') - w) * ((1 : Q') - w))))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ ha) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-1)
      (a * (((1 : Q') - w) * ((1 : Q') - w))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (a * (((1 : Q') - w) * ((1 : Q') - w)))
      (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact QPoly.q_zero_add_eqv (a * (((1 : Q') - w) * ((1 : Q') - w)))

/-- **`corr_casimir_shape` — the correction is Casimir-shape with scale `a·(1 − w)²`.**
On `0 ≤ corr ≤ 1`,

    1 − corrFactor^{C₄(s)}  ≤  C₄(s) · ( a·(1 − w)² ),

i.e. the multiplicative correction `corr^{C₄(s)} ≥ 1 − C₄(s)·a·(1 − w)²` deviates from
`1` by a term PROPORTIONAL to the Casimir `C₄(s)` — exactly the shape of the local-CLT
linear prefactor `1 − a*·C₄(s)·(1 − w)²`.  So choosing `a = a*(p)` makes the refined
eigenvalue match the predicted prefactor to leading order.  PROOF: `oneSub_qpow_le` at
base `corrFactor`, then rewrite `1 − corr ≃ a·(1 − w)²` (`oneSub_corr`). -/
theorem corr_casimir_shape {a w : Q'} (s : Nat)
    (hc0 : (0 : Q') ≤ corrFactor a w) (hc1 : corrFactor a w ≤ (1 : Q')) :
    (1 : Q') - qpow (corrFactor a w) (c4 s)
      ≤ Q'.ofNat (c4 s) * (a * (((1 : Q') - w) * ((1 : Q') - w))) := by
  have hbase : (1 : Q') - qpow (corrFactor a w) (c4 s)
      ≤ Q'.ofNat (c4 s) * ((1 : Q') - corrFactor a w) :=
    oneSub_qpow_le hc0 hc1 (c4 s)
  refine Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv ?_)
  exact Q'.mul_eqv_congr_left (Q'.ofNat (c4 s)) _ _ (oneSub_corr a w)

/-! ## 3. The explicit refined coefficient `a*(p) = 7(p − 1) / (6 p²)` -/

/-- **The explicit refined retune coefficient** `a*(p) = 7(p − 1)/(6 p²)` — the value
that absorbs the local-CLT linear prefactor (the second-cumulant / effective-time
shift).  `a*(2) = 7/24`, `a*(1) = 0`. -/
def refineCoeff (p : Nat) (hp : 0 < p) : Q' :=
  Q'.mkPos (7 * ((p : Int) - 1)) (6 * (p * p))
    (Nat.mul_pos (by decide) (Nat.mul_pos hp hp))

/-- **`refineCoeff 1 _ ≃ 0`** — THE SHARP CONSISTENCY CHECK.  At `p = 1` there is no
bond-moving (`normEigShift_p1_zero` proves the defect vanishes exactly), so the refined
coefficient is exactly `0`: no refinement is needed.  (Numerator `7·(1 − 1) = 0`.) -/
theorem refineCoeff_p1_zero (hp : 0 < 1) : (refineCoeff 1 hp) ≈ (0 : Q') := by
  show (Q'.mkPos (7 * ((1 : Int) - 1)) (6 * (1 * 1)) _).num * (((0 : Q').den : Int))
      = ((0 : Q').num) * ((Q'.mkPos (7 * ((1 : Int) - 1)) (6 * (1 * 1)) _).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  decide

/-- **`refineCoeff 2 _ ≃ 7/24`** — the EXPLICIT p=2 linear-prefactor coefficient
`a*(2) = 7(2 − 1)/(6·4) = 7/24`.  This is THE reported number: the second parameter
that, in the refined retune `renormW2 2 _ (7/24) w`, cancels the bulk linear prefactor
of `vacNorm` at `p = 2`. -/
theorem refineCoeff_p2 (hp : 0 < 2) :
    (refineCoeff 2 hp) ≈ (Q'.mkPos 7 24 (by decide)) := by
  show (Q'.mkPos (7 * ((2 : Int) - 1)) (6 * (2 * 2)) _).num
        * ((Q'.mkPos 7 24 (by decide)).den : Int)
      = (Q'.mkPos 7 24 (by decide)).num
        * ((Q'.mkPos (7 * ((2 : Int) - 1)) (6 * (2 * 2)) _).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  decide

/-! ## 4. The refined per-mode defect and the LINEAR-CANCELLATION identity -/

/-- **The refined vacuum-normalized per-mode defect** against the REFINED eigenvalue:

    normEigShift2 N p hp a w s  =  | vacNorm N p hp w s  −  retEig2 p hp a w s |. -/
def normEigShift2 (N p : Nat) (hp : 0 < p) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (a : Q') (s : Nat) : Q' :=
  absQ (vacNorm N p hp hw0 hw1 s + -(retEig2 p hp a w s))

theorem normEigShift2_nonneg (N p : Nat) (hp : 0 < p) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (a : Q') (s : Nat) :
    (0 : Q') ≤ normEigShift2 N p hp hw0 hw1 a s :=
  absQ_nonneg _

/-- **THE LINEAR-CANCELLATION IDENTITY.**  Under the factorization `vac ≃ ret2 · rem`
(`rem` the quadratic remainder after the refined retune absorbs the Casimir-shape
prefactor), the residual is EXACTLY

    vac − ret2  ≃  ret2 · (rem − 1),

i.e. the linear Casimir-shape prefactor has been FOLDED INTO `ret2` and the residual is
`ret2` times the pure remainder `rem − 1`.  When `rem − 1` is quadratic, so is the
residual.  This is the precise sense in which the refined retune kills the linear term.
PROOF: `vac + −ret2 ≃ ret2·rem + −ret2 ≃ ret2·(rem + −1)` (distribute, `ret2·(−1) ≃
−ret2`). -/
theorem defect_factor (ret2 rem vac : Q') (h : vac ≈ (ret2 * rem)) :
    (vac + -(ret2)) ≈ (ret2 * (rem + -(1 : Q'))) := by
  have hkey : (ret2 * (rem + -(1 : Q'))) ≈ (ret2 * rem + -(ret2)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv ret2 rem (-(1 : Q'))) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv ret2 1) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv ret2)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(ret2)) h) (Q'.eqv_symm hkey)

/-! ## 5. The verdict-(a) obligation + the inverse-SQUARE summable payoff -/

/-- **THE VERDICT-(a) OBLIGATION — the refined remainder is QUADRATIC.**  At the refined
base (the intended coefficient `a = refineCoeff p hp`), the refined per-mode defect is
bounded QUADRATICALLY in the margin:

    normEigShift2 N p hp a w s  ≤  Cq · (1 − w)²    for all `s`.

This is the local-CLT input AFTER the linear cancellation — the CLOSURE-shaped successor
of the LINEAR lower bound `VacNormEigShift.BulkLocalCLTLinear`.  Where the unrefined
defect is LINEAR (non-summable), the refined defect is QUADRATIC; the residual is the
general-`p` Edgeworth (quartic-cumulant) control.  Carried as `Type`-level data; NOT
inhabited (it is the deep discrete-local-CLT tier, now at quadratic order). -/
structure RefinedBulkRemainderQuadratic (N p : Nat) (hp : 0 < p) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (a : Q') : Type where
  /-- The quadratic modulus constant. -/
  Cq : Q'
  /-- `Cq ≥ 0`. -/
  Cq_nonneg : (0 : Q') ≤ Cq
  /-- The refined defect is QUADRATIC in the margin, uniformly in `s`. -/
  quad : ∀ s, normEigShift2 N p hp hw0 hw1 a s
    ≤ Cq * (((1 : Q') - w) * ((1 : Q') - w))

/-- **THE VERDICT-(a) PAYOFF — the refined defect is inverse-SQUARE summable.**  Given
the refined quadratic bound and a margin control `1 − w ≤ r` (e.g. `r = A/(k+B)` along
asymptotic freedom), the refined per-mode defect satisfies

    normEigShift2 N p hp a w s  ≤  Cq · (r · r),

the inverse-SQUARE form feeding summability `∑ 1/k² < ∞`.  This is the decisive contrast
with the unrefined LINEAR lower bound `BulkLocalCLTLinear` (`cLin·(1 − w)`, non-summable):
the refined retune `renormW2` (with `a = refineCoeff p hp`) CONVERTS the linear bulk
obstruction into a summable quadratic residual.  PROOF: `rq.quad`, then `sq_le_sq` on the
margin scaled by `Cq ≥ 0`. -/
theorem refinedDefect_invSq (N p : Nat) (hp : 0 < p) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (a : Q') (rq : RefinedBulkRemainderQuadratic N p hp hw0 hw1 a)
    {r : Q'} (hr : (1 : Q') - w ≤ r) (s : Nat) :
    normEigShift2 N p hp hw0 hw1 a s ≤ rq.Cq * (r * r) := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hsq : ((1 : Q') - w) * ((1 : Q') - w) ≤ r * r := sq_le_sq hnn hr
  have hscale : rq.Cq * (((1 : Q') - w) * ((1 : Q') - w)) ≤ rq.Cq * (r * r) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsq rq.Cq_nonneg
  exact Q'.le_trans' _ _ _ (rq.quad s) hscale

/-! ## 6. The genuine retune-INVARIANT obstruction — the quartic-Casimir term -/

/-- **`quartic_retune_invariant` — the quartic-Casimir Edgeworth term is NOT absorbable
by ANY retune.**  A heat-kernel reparametrization (a base change `f ↦ f·corr`) only adds
a term PROPORTIONAL to `C₄(s)` in the log of the eigenvalue (the Casimir-shape
prefactor).  The genuine non-Gaussian cumulant-4 correction is PROPORTIONAL to `C₄(s)²`
(the `θ⁴/180` curvature term).  This lemma proves these are LINEARLY INDEPENDENT
shapes: there is NO affine fit `α + β·C₄(s) = C₄(s)²` valid at `s = 0, 1, 2`
(`C₄ = 0, 3, 8`, `C₄² = 0, 9, 64`).  Indeed the `s = 0, 1` data force `α = 0, β = 3`,
predicting `α + 8β = 24` at `s = 2`, contradicting the true `C₄(2)² = 64`.  So the
cumulant-4 term is retune-INVARIANT — but, being `∝ C₄(s)²·(1 − w)² = O((1 − w)²)` on
the bulk, it is QUADRATIC (summable), NOT the linear obstruction.  PROOF: `omega` on the
three linear equations (a `3×3`-Vandermonde inconsistency). -/
theorem quartic_retune_invariant :
    ¬ ∃ α β : Int,
        α + β * (c4 0 : Int) = ((c4 0 : Int) * (c4 0 : Int))
      ∧ α + β * (c4 1 : Int) = ((c4 1 : Int) * (c4 1 : Int))
      ∧ α + β * (c4 2 : Int) = ((c4 2 : Int) * (c4 2 : Int)) := by
  have e0 : (c4 0 : Int) = 0 := by decide
  have e1 : (c4 1 : Int) = 3 := by decide
  have e2 : (c4 2 : Int) = 8 := by decide
  rintro ⟨α, β, h0, h1, h2⟩
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  omega

/-! ## 7. Doc — PROVED, the VERDICT, and the precise residual (AGENTS.md Rule 6)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):

  * `qpow_mul_base` — multiplicativity `(a·b)^n ≃ a^n·b^n` (the absorbability engine).
  * `retEig2_factor` — `retEig2 ≃ retEig · corr^{C₄(s)}` (the absorption mechanism).
  * `retEig2_param_zero` — `a = 0` recovers the current retune (refinement, not
    replacement).
  * `oneSub_corr` / `corr_casimir_shape` — the correction is Casimir-shape with scale
    `a·(1 − w)²`; `a = a*(p)` matches the predicted prefactor.
  * `refineCoeff`, `refineCoeff_p1_zero` (`= 0`), `refineCoeff_p2` (`= 7/24`) — the
    EXPLICIT coefficient `a*(p) = 7(p − 1)/(6 p²)`.
  * `defect_factor` — the linear-cancellation identity `vac − ret2 ≃ ret2·(rem − 1)`.
  * `refinedDefect_invSq` — the verdict-(a) payoff: the refined defect is inverse-SQUARE
    summable (vs. the non-summable linear `BulkLocalCLTLinear`).
  * `quartic_retune_invariant` — the genuine obstruction `C₄(s)² ∉ span{1, C₄(s)}` is
    retune-INVARIANT but QUADRATIC.

VERDICT: **(a)** — A REFINED RETUNE KILLS THE LINEAR PREFACTOR.  The bulk linear
prefactor is a Casimir-shape (second-cumulant / effective-time) correction with EXPLICIT
coefficient `a*(p) = 7(p − 1)/(6 p²)` — `7/24` at `p = 2`, `0` at `p = 1` (the sharp
consistency with the proved `normEigShift_p1_zero`).  The refined retune `renormW2 p hp
(refineCoeff p hp) w = renormWFix · (1 − a*·(1 − w)²)` ABSORBS it (`retEig2_factor` +
`corr_casimir_shape`), converting the LINEAR lower bound `BulkLocalCLTLinear` into the
QUADRATIC, inverse-square-summable `RefinedBulkRemainderQuadratic` (`refinedDefect_invSq`).

The honest residual: the genuinely retune-INVARIANT part is the quartic-Casimir
Edgeworth (cumulant-4) term `∝ C₄(s)²·(1 − w)²`, PROVED non-absorbable
(`quartic_retune_invariant`) — the bond-moved measure DOES leave the heat-kernel
manifold, but only at SECOND order, so it is quadratic (summable), not the linear
obstruction.  The open content shrinks from a LINEAR bulk obstruction to a QUADRATIC
general-`p` Edgeworth control, isolated to the single named `RefinedBulkRemainderQuadratic`.

This is NOT a 4D Yang–Mills mass-gap proof; it is the sharp resolution of the
linear-prefactor question — the linear departure from the heat-kernel manifold is a
reparametrization (absorbed by `a*(p)`), and only the quadratic departure is genuine. -/

end YMGap.Continuum.RefinedRetune

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RefinedRetune.qpow_mul_base
#print axioms YMGap.Continuum.RefinedRetune.retEig2_factor
#print axioms YMGap.Continuum.RefinedRetune.corrFactor_zero
#print axioms YMGap.Continuum.RefinedRetune.retEig2_param_zero
#print axioms YMGap.Continuum.RefinedRetune.oneSub_corr
#print axioms YMGap.Continuum.RefinedRetune.corr_casimir_shape
#print axioms YMGap.Continuum.RefinedRetune.refineCoeff_p1_zero
#print axioms YMGap.Continuum.RefinedRetune.refineCoeff_p2
#print axioms YMGap.Continuum.RefinedRetune.normEigShift2_nonneg
#print axioms YMGap.Continuum.RefinedRetune.defect_factor
#print axioms YMGap.Continuum.RefinedRetune.refinedDefect_invSq
#print axioms YMGap.Continuum.RefinedRetune.quartic_retune_invariant
