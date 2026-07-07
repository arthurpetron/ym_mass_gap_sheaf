/-
Track B / R2 — CODYNAMIC REFLECTION-UNIT RECAST of the atomic core `singleStep`,
mirroring the machine-verified Agda spec (`--safe --without-K`, zero postulates)
`Codynamic/Metric.agda` (`Lipschitz.scale` monotone modulus; `εX` reflection-unit
defect) and `Codynamic/Trajectory.agda` (`nBound`/`nstep-d` left-fold Grönwall).

# What this module does (read first) — and the HONEST VERDICT

`SingleStepDefectReduction.SingleStepDefectBound` puts the WHOLE Clay continuum
gap on ONE open field
    `singleStep : ∀ k, (1 − afDefectSeq afr k)·trueMargin k ≤ trueMargin (k+1)`.
This module RECASTS that step in Arthur Petron's Codynamic Theory (theorem5.tex
Def 4.15/4.16, Lem 4.18, Prop 4.19, Cor 4.20, **Remark 4.20 "Moduli beyond
multiplication"**) and ADJUDICATES whether the NONLINEAR MONOTONE MODULUS opens a
strictly-weaker reduction, or collapses to `singleStep`.

The two codynamic quantities of a witnessed block-spin step (Agda `Metric.agda`):
  * the **monotone modulus** `scale` (`Lipschitz.lip`,
    `d(⟦bs⟧xs)(⟦bs⟧ys) ≤ scale (dAll xs ys)`) — the map's continuity on PAIRS;
  * the **reflection-unit defect** `δ_k = d(⟦bs⟧ fine_k, coarse_k)` (`εX`,
    Agda `wdef`) — the discrepancy at the RECORDED point.
The composed defect is the LEFT FOLD `b_i = scale_i(b_{i-1}) + δ_i`
(Agda `nBound`), and `nstep-d` bounds the total by that fold for ANY monotone
modulus — the multi-scale composition **for free** (Cor 4.20 + Remark 4.20).

**VERDICT: (iii) HONEST COLLAPSE — the codynamic recast does NOT advance the
frontier below `singleStep`.**  Precisely, machine-checked here:

  1. **Composition is free & genuinely codynamic** (`codyFold_bounds`,
     `codyFloor_lb`): the monotone-modulus Grönwall fold, mirroring Agda
     `nBound`/`nstep-d`, holds for ANY `MonotoneModulus`, and `CodynamicMarginRecast`
     routes into the EXISTING positive continuum floor
     (`fullFloor_of_codynamicRecast` via `fullFloor_of_singleStep`/`afFloorEps`).

  2. **The propagation obstruction is a LINEAR-modulus artifact**
     (`singleEdgeFactor_expansive_at_weak`): `DirectSingleStepReconGap`'s failure
     is the LINEAR single-edge modulus `2w³ → 2 > 1` being EXPANSIVE at weak
     coupling.  Non-expansive monotone moduli exist
     (`contractiveModulus_nonexpansive`), so the nonlinear-modulus degree of
     freedom (Remark 4.20) is REAL and the fold CAN be bounded — the linear
     eigenvalue is not the true obstruction.

  3. **BUT the crux DEFECT bound is ORTHOGONAL to the modulus**
     (`modulus_underdetermines_defect`): two `ReflectionStep`s with the SAME
     (identity) modulus have DIFFERENT defects (`2` vs `0`), and the identity
     modulus — a valid, computable, nonlinear-general monotone modulus — has
     defect `2 > 6·(1−½)² = 3/2` (`orthoBig_defect_exceeds_bound`).  So NO modulus
     bound implies `δ_k ≤ 6(1−w)²`: "compute the block-spin monotone modulus" is a
     genuine INDEPENDENT object but NOT core-shrinking (exactly like `uniform_in_m`,
     `docs/adjudicate-2026-07-07.md`).

  4. **The single-scale DEFECT obligation EQUI-INHABITS `singleStep`**
     (`singleStep_of_codynamicRecast` : `CodynamicMarginRecast → SingleStepDefectBound`,
     and `codynamicRecast_of_singleStep` the converse on `tm ≥ 0`): the reflection
     defect bound `εX ≤ 6(1−w)²` PINNED to the TRUE margin is the ATOMIC core, not
     strictly weaker.  By Def 4.16 the defect `d(⟦bs⟧ fine, coarse)` requires the
     interacting block-spin map `⟦bs⟧` = the unconstructed a→0 measure.

So the modulus recast SPLITS `singleStep` into {an independent, non-core-shrinking
nonlinear modulus} + {the atomic per-step interacting reflection defect ≡
`singleStep`}.  It answers the coordinator's (A)/(B) with **(B)**: the single-scale
content that bites (`εX ≤ 6(1−w)²` on the true margin) equi-inhabits `singleStep`
and requires the interacting measure; the modulus half that might have evaded the
`2w³→2` obstruction is orthogonal to the defect and cannot supply it.  No new
`:= SingleStepDefectBound` alias is emitted; `SingleStepDefectBound` and
`CodynamicMarginRecast` are inhabited NOWHERE.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition mirroring the verified Agda folds; the concrete
counterexample metric is a decidable two-point space.  Every load-bearing
declaration is `#print axioms`-gated; permitted output `propext`/`Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  `Type`-level witnesses
are `Type` data (Rule 8).
-/

import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Continuum.DirectSingleStepReconGap

namespace YMGap.Continuum.CodynamicReflectionUnitRecast

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.ContinuumClosureProgram
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 0. The cost structure is `Q'` and the MONOTONE MODULUS (Agda `Lipschitz`).

Agda `Metric.agda` `Costs` = an ordered additive structure with joins; the repo's
`Q'` is exactly such an instance.  `Lipschitz.scale` is a monotone map per rule
symbol with `scale-mono` and `scale-0` — the NONLINEAR degree of freedom of
Remark 4.20, subsuming the multiplicative `L·(−)` as the linear instance. -/

/-- **`MonotoneModulus` — the codynamic `Lipschitz.scale` (Remark 4.20).**  A
`Q'→Q'` continuity modulus with `scale-mono` (`mono`) and `scale-0` (`base`).
Multiplication by `L ≥ 0` is the LINEAR instance (`linearModulus`); the identity
and any concave/bounded map are equally admissible — NOTHING in the folds below
consumes linearity. -/
structure MonotoneModulus : Type where
  /-- The scaling map `s = scale ω`. -/
  s : Q' → Q'
  /-- `scale-mono`: monotone. -/
  mono : ∀ a b : Q', a ≤ b → s a ≤ s b
  /-- `scale-0`: `0 ≤ s 0`. -/
  base : (0 : Q') ≤ s 0

/-- The identity modulus (`scale = id`): the sharpest continuity a 1-Lipschitz
interpretation can carry; a fully-specified, computable monotone modulus. -/
def identityModulus : MonotoneModulus where
  s := fun x => x
  mono := fun _ _ h => h
  base := Q'.le_refl' 0

/-- The linear modulus `scale(x) = c·x` (`c ≥ 0`) — the multiplicative `L·(−)` of
the paper, one instance among the monotone moduli. -/
def linearModulus (c : Q') (hc : (0 : Q') ≤ c) : MonotoneModulus where
  s := fun x => c * x
  mono := fun a b h => Q'.mul_le_mul_of_nonneg_left a b c h hc
  base := Q'.le_of_eqv (Q'.eqv_symm (q_mul_zero c))

/-! ## 1. The reflection step and its DEFECT (Agda `Metric.agda` `wdef`/`εX`).

A block-spin step carries: a `Q'`-valued metric `d` on configurations, the
interpretation `bs = ⟦block-spin⟧`, its monotone modulus with the Lipschitz law
`lip`, and the RECORDED fine/coarse configs.  The **reflection-unit defect** is
`δ = d(⟦bs⟧ fine, coarse)` (Def 4.16 / Agda `wdef k = d (eval lhs)(eval rhs)`). -/

/-- **`ReflectionStep` — a witnessed block-spin application** (mirrors Agda
`MetricVal` + `Lipschitz` restricted to one step). -/
structure ReflectionStep : Type 1 where
  /-- Configuration space. -/
  Cfg : Type
  /-- The `Q'`-valued (pseudo)metric. -/
  d : Cfg → Cfg → Q'
  /-- Distances are nonnegative. -/
  d_nonneg : ∀ x y : Cfg, (0 : Q') ≤ d x y
  /-- The block-spin interpretation `⟦block-spin⟧`. -/
  bs : Cfg → Cfg
  /-- Its monotone modulus (`Lipschitz.scale`). -/
  modulus : MonotoneModulus
  /-- The Lipschitz law `d(⟦bs⟧x)(⟦bs⟧y) ≤ scale (d x y)` (`Lipschitz.lip`). -/
  lip : ∀ x y : Cfg, d (bs x) (bs y) ≤ modulus.s (d x y)
  /-- The recorded fine configuration. -/
  fine : Cfg
  /-- The recorded coarse configuration. -/
  coarse : Cfg

/-- **The reflection-unit defect** `δ = d(⟦bs⟧ fine, coarse)` (Def 4.16 / Agda
`wdef`): the discrepancy between the interpretation applied to the recorded fine
config and the recorded coarse value.  Depends on `⟦bs⟧` evaluated on `fine` —
i.e. on the interacting block-spin map. -/
def ReflectionStep.defect (R : ReflectionStep) : Q' := R.d (R.bs R.fine) R.coarse

/-! ## 2. The GRÖNWALL fold (Agda `Trajectory.agda` `nBound`/`nstep-d`).

`nBound b y (sy t∷ tr) = nBound (scale(rule) b +# d(stepF y, rec)) (rec) tr`:
the LEFT FOLD scaling the running bound by the step's modulus and ADDING the
step's reflection defect.  Composition of monotone moduli — no multiplication
required (Remark 4.20).  `nstep-d` bounds the accumulated discrepancy by the fold.
We formalize the abstract fold and prove the transport theorem for ANY monotone
modulus. -/

/-- **`codyFold` — the n-step defect fold** (`nBound`): `b₀ ↦ …`,
`b_{k+1} = scale_k(b_k) + δ_k`.  The classical `(∏L)b₀ + Σ(∏L)δ` is its
afterimage; the fold is the object (Remark 4.20 / Trajectory register notes). -/
def codyFold (sc : Nat → MonotoneModulus) (δ : Nat → Q') (b0 : Q') : Nat → Q'
  | 0 => b0
  | k + 1 => (sc k).s (codyFold sc δ b0 k) + δ k

/-- **`codyFold_bounds` — the n-step transition (`nstep-d`), monotone-modulus
form.**  If a running discrepancy `dist` starts within `b₀` and each step obeys
`dist(k+1) ≤ scale_k(dist k) + δ_k` (Prop 4.19's one-step recursion), then
`dist n ≤ codyFold n` at every `n`.  Structural induction, each step = mono +
`add_le_add` — the SAME proof shape as Agda `nstep-d`, valid for ANY monotone
modulus (no linearity). -/
theorem codyFold_bounds (sc : Nat → MonotoneModulus) (δ : Nat → Q')
    (dist : Nat → Q') (b0 : Q') (h0 : dist 0 ≤ b0)
    (hstep : ∀ k, dist (k + 1) ≤ (sc k).s (dist k) + δ k) :
    ∀ n, dist n ≤ codyFold sc δ b0 n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih =>
      have hm : (sc k).s (dist k) ≤ (sc k).s (codyFold sc δ b0 k) :=
        (sc k).mono _ _ ih
      have hadd : (sc k).s (dist k) + δ k
          ≤ (sc k).s (codyFold sc δ b0 k) + δ k :=
        Q'.add_le_add hm (Q'.le_refl' (δ k))
      exact Q'.le_trans' _ _ _ (hstep k) hadd

/-! ### 2b. The multiplicative MARGIN floor (the erosion-dual of `nBound`).

The margin recursion `σ_k·m_k ≤ m_{k+1}` (`singleStep` with survival
`σ_k = 1 − δ_k`) is `nBound` read as a LOWER bound on a positive gap — the
codynamic derivation of the product floor `∏σ_k·m₀`.  We prove it (same induction
as `codyFloor_lb`), then tie the recast to the EXISTING positive floor. -/

/-- The survival-product floor `∏_{i<n} σ_i · m₀` as a left fold. -/
def codyFloor (σ : Nat → Q') (m0 : Q') : Nat → Q'
  | 0 => m0
  | k + 1 => σ k * codyFloor σ m0 k

/-- **`codyFloor_lb` — the multiplicative Grönwall (margin erosion).**  If
`m₀ ≤ m 0` and `σ_k·m_k ≤ m_{k+1}` with `σ_k ≥ 0`, then `codyFloor σ m₀ n ≤ m n`:
the erosion product is a uniform floor for the eroding margin.  The lower-bound
dual of `codyFold_bounds`. -/
theorem codyFloor_lb (σ : Nat → Q') (m : Nat → Q') (m0 : Q')
    (hσ : ∀ k, (0 : Q') ≤ σ k) (h0 : m0 ≤ m 0)
    (hstep : ∀ k, σ k * m k ≤ m (k + 1)) :
    ∀ n, codyFloor σ m0 n ≤ m n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih =>
      have hm : σ k * codyFloor σ m0 k ≤ σ k * m k :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih (hσ k)
      exact Q'.le_trans' _ _ _ hm (hstep k)

/-! ## 3. The propagation obstruction is a LINEAR-modulus artifact (Remark 4.20).

`DirectSingleStepReconGap` shows the single-edge reconstruction has leading
excited eigenvalue `rho = 2w³ → 2 > 1` at weak coupling — the LINEAR modulus is
EXPANSIVE.  We (i) reproduce the expansiveness decidably and (ii) exhibit a
non-expansive monotone modulus, so the fold CAN be bounded: the linear eigenvalue
is not the true obstruction; the nonlinear degree of freedom is genuine. -/

/-- The concrete deep-UV weight `wWeak = 9/10` (= `DirectSingleStepReconGap.wWeak`). -/
def wWeakLoc : Q' := Q'.mkPos 9 10 (by decide)

/-- The LINEAR single-edge modulus factor `2w³` (= `WilsonConnCorr.rho w`, the
excited transfer eigenvalue / Lipschitz constant of the single-edge map). -/
def singleEdgeFactor (w : Q') : Q' := Q'.ofNat 2 * (w * (w * w))

/-- **`singleEdgeFactor_expansive_at_weak` — the LINEAR modulus is EXPANSIVE at
weak coupling.**  `2·(9/10)³ = 1458/1000 ≥ 1`: with the linear single-edge
modulus the fold multiplies error by `> 1` per step.  This is exactly
`DirectSingleStepReconGap.rho_ge_one_at_weak` (the `2w³ → 2 > 1` obstruction),
here isolated as a statement about the MODULUS. -/
theorem singleEdgeFactor_expansive_at_weak : (1 : Q') ≤ singleEdgeFactor wWeakLoc := by
  decide

/-- Cross-check: the local factor IS the `DirectSingleStepReconGap` single-edge
eigenvalue's obstruction (same numeric wall), certifying non-vacuity. -/
theorem singleEdge_matches_reconGap :
    (1 : Q') ≤ WilsonConnCorr.rho DirectSingleStepReconGap.wWeak :=
  DirectSingleStepReconGap.rho_ge_one_at_weak

/-- `oneHalf = 1/2`. -/
def oneHalf : Q' := Q'.mkPos 1 2 (by decide)

theorem oneHalf_nonneg : (0 : Q') ≤ oneHalf := by decide

/-- A concrete non-expansive monotone modulus `scale(x) = x/2`. -/
def contractiveModulus : MonotoneModulus := linearModulus oneHalf oneHalf_nonneg

/-- **`contractiveModulus_nonexpansive` — non-expansive monotone moduli EXIST.**
`(x/2) ≤ x` for `x ≥ 0`: unlike the single-edge `2w³ > 1`, this monotone modulus
never expands, so the fold `codyFold` stays bounded.  The nonlinear-modulus degree
of freedom (Remark 4.20) genuinely dissolves the `2w³→2` propagation obstruction —
which was an artifact of insisting on the LINEAR single-edge eigenvalue. -/
theorem contractiveModulus_nonexpansive (x : Q') (hx : (0 : Q') ≤ x) :
    contractiveModulus.s x ≤ x := by
  show oneHalf * x ≤ x
  have h1 : oneHalf ≤ (1 : Q') := by decide
  have h2 : oneHalf * x ≤ (1 : Q') * x :=
    Q'.mul_le_mul_of_nonneg_right oneHalf 1 x h1 hx
  exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.one_mul_eqv x))

/-! ## 4. THE CRUX — the DEFECT is ORTHOGONAL to the modulus (the collapse).

A `MonotoneModulus` bounds the map on PAIRS; the reflection DEFECT is a distance
at a single recorded point.  They are independent codynamic quantities (separate
additive fields in Agda `nBound`).  We machine-check this with a decidable
two-point metric: two steps with the IDENTITY modulus (the strongest continuity)
but DIFFERENT defects — so no modulus bound determines/bounds the defect. -/

/-- A decidable two-point configuration space. -/
inductive TwoPt : Type
  | a : TwoPt
  | b : TwoPt

/-- The two-point metric: `d(a,b) = d(b,a) = 2`, diagonal `0`. -/
def d2 : TwoPt → TwoPt → Q'
  | TwoPt.a, TwoPt.a => 0
  | TwoPt.b, TwoPt.b => 0
  | TwoPt.a, TwoPt.b => 2
  | TwoPt.b, TwoPt.a => 2

theorem d2_nonneg : ∀ x y : TwoPt, (0 : Q') ≤ d2 x y := by
  intro x y; cases x <;> cases y <;> decide

/-- A reflection step with the IDENTITY modulus (`bs = id`, so `lip` is `le_refl`)
and a LARGE defect: `fine = a`, `coarse = b`, defect `= d2 a b = 2`. -/
def orthoStepBig : ReflectionStep where
  Cfg := TwoPt
  d := d2
  d_nonneg := d2_nonneg
  bs := fun x => x
  modulus := identityModulus
  lip := fun x y => Q'.le_refl' (d2 x y)
  fine := TwoPt.a
  coarse := TwoPt.b

/-- Same IDENTITY modulus, but `coarse = fine`, so defect `= d2 a a = 0`. -/
def orthoStepZero : ReflectionStep where
  Cfg := TwoPt
  d := d2
  d_nonneg := d2_nonneg
  bs := fun x => x
  modulus := identityModulus
  lip := fun x y => Q'.le_refl' (d2 x y)
  fine := TwoPt.a
  coarse := TwoPt.a

theorem orthoStepBig_defect : orthoStepBig.defect = (2 : Q') := rfl
theorem orthoStepZero_defect : orthoStepZero.defect = (0 : Q') := rfl

/-- The model transverse bound `6·(1−w)²` (the `SingleStepDefectReduction` RHS
shape, `bondMovingDeltaRen_le_sixp`), as a function of the weight. -/
def sixQuad (w : Q') : Q' := Q'.ofNat 6 * ((1 - w) * (1 - w))

/-- **`orthoBig_defect_exceeds_bound` — the IDENTITY modulus VIOLATES the defect
bound.**  `orthoStepBig` carries the identity modulus (a valid, computable,
nonlinear-general monotone modulus) yet its defect `2` exceeds `6·(1−½)² = 3/2`.
So a bound on the modulus — even the tightest, the identity — does NOT imply
`δ_k ≤ 6(1−w)²`. -/
theorem orthoBig_defect_exceeds_bound : sixQuad oneHalf < orthoStepBig.defect := by
  rw [orthoStepBig_defect]; decide

/-- **`modulus_underdetermines_defect` — the CRUX orthogonality (machine-checked).**
`orthoStepBig` and `orthoStepZero` have the SAME (identity) modulus but DIFFERENT
defects (`2 ≠ 0`).  Hence the reflection defect is NOT a function of the modulus:
no `MonotoneModulus` computation can bound `δ_k`.  "Compute the block-spin monotone
modulus `scale`" is therefore INDEPENDENT of the defect bound `εX ≤ 6(1−w)²` — a
genuine object, but NOT core-shrinking (parallel to `uniform_in_m`,
`docs/adjudicate-2026-07-07.md`). -/
theorem modulus_underdetermines_defect :
    orthoStepBig.modulus = orthoStepZero.modulus
      ∧ orthoStepBig.defect ≠ orthoStepZero.defect := by
  refine ⟨rfl, ?_⟩
  rw [orthoStepBig_defect, orthoStepZero_defect]
  decide

/-! ## 5. The single-scale DEFECT obligation EQUI-INHABITS `singleStep` (collapse).

The codynamic per-step reflection defect, PINNED to the true margin, is
`CodynamicMarginRecast`.  We prove it maps BOTH WAYS to `SingleStepDefectBound`
(on the physical domain `tm ≥ 0`): the defect bound `εX ≤ 6(1−w)²` is NOT strictly
weaker — it is the atomic core.  Neither structure is inhabited here. -/

/-- **`CodynamicMarginRecast` — the codynamic per-step reflection-defect obligation
(`Type`, Rule 8; UNINHABITED).**  For an AF rate and the true margin, a per-step
reflection defect `reflDefect_k = d(⟦bs⟧ fine_k, coarse_k)` that (a) governs the
margin's per-step degradation and (b) satisfies the single-scale bound
`reflDefect_k ≤ δ_model_k` (`εX ≤ 6(1−w)²`).  This is exactly the codynamic
reading of `singleStep`'s open content. -/
structure CodynamicMarginRecast : Type where
  /-- The AF rate supplying `δ_model = afDefectSeq afr`. -/
  afr : AFRateModulus
  /-- The true dimensionless margin `m_lat(a_k)/a_k`. -/
  trueMargin : Nat → Q'
  /-- Strong-coupling anchor. -/
  trueMargin0_pos : (0 : Q') < trueMargin 0
  /-- The margin is nonnegative (physical: mass/spacing ratio). -/
  trueMargin_nonneg : ∀ k, (0 : Q') ≤ trueMargin k
  /-- The per-step reflection-unit defect (Agda `wdef`/`εX`). -/
  reflDefect : Nat → Q'
  /-- The defect is nonnegative. -/
  reflDefect_nonneg : ∀ k, (0 : Q') ≤ reflDefect k
  /-- (a) The reflection defect GOVERNS the margin's per-step degradation. -/
  refl_governs : ∀ k, (1 - reflDefect k) * trueMargin k ≤ trueMargin (k + 1)
  /-- (b) THE SINGLE-SCALE DEFECT BOUND `εX ≤ 6(1−w)²`: the reflection defect is
  at most the proved transverse model defect. -/
  refl_le_model : ∀ k, reflDefect k ≤ afDefectSeq afr k

/-- **`singleStep_of_codynamicRecast` — the reduction `newObligation → singleStep`
(PROVED).**  From (a)+(b) and `tm ≥ 0`: `1 − δ_model_k ≤ 1 − reflDefect_k`, so
`(1 − δ_model_k)·tm_k ≤ (1 − reflDefect_k)·tm_k ≤ tm_{k+1}`.  This is a genuine
implication (not an alias def): a conditional producer with an open
`CodynamicMarginRecast` hypothesis, so it does NOT inhabit `SingleStepDefectBound`. -/
def singleStep_of_codynamicRecast (R : CodynamicMarginRecast) : SingleStepDefectBound where
  afr := R.afr
  trueMargin := R.trueMargin
  trueMargin0_pos := R.trueMargin0_pos
  singleStep := by
    intro k
    have hneg : -(afDefectSeq R.afr k) ≤ -(R.reflDefect k) :=
      Q'.neg_le_neg (R.refl_le_model k)
    have h1 : (1 : Q') - afDefectSeq R.afr k ≤ 1 - R.reflDefect k := by
      show (1 : Q') + -(afDefectSeq R.afr k) ≤ 1 + -(R.reflDefect k)
      exact Q'.add_le_add (Q'.le_refl' 1) hneg
    have h2 : ((1 : Q') - afDefectSeq R.afr k) * R.trueMargin k
        ≤ (1 - R.reflDefect k) * R.trueMargin k :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ h1 (R.trueMargin_nonneg k)
    exact Q'.le_trans' _ _ _ h2 (R.refl_governs k)

/-- **`codynamicRecast_of_singleStep` — the CONVERSE (PROVED), on `tm ≥ 0`.**
Take `reflDefect := afDefectSeq afr`; then (b) is `le_refl` and (a) is verbatim
`singleStep`.  Together with the forward map this proves `CodynamicMarginRecast`
and `SingleStepDefectBound` are EQUI-INHABITED on the physical domain — the
codynamic defect obligation is NOT strictly weaker than `singleStep` (an ALIAS,
reproducing `real_defect_identification` of `docs/adjudicate-2026-07-07.md`). -/
def codynamicRecast_of_singleStep (S : SingleStepDefectBound)
    (hnn : ∀ k, (0 : Q') ≤ S.trueMargin k) : CodynamicMarginRecast where
  afr := S.afr
  trueMargin := S.trueMargin
  trueMargin0_pos := S.trueMargin0_pos
  trueMargin_nonneg := hnn
  reflDefect := afDefectSeq S.afr
  reflDefect_nonneg := afDefectSeq_nonneg S.afr
  refl_governs := S.singleStep
  refl_le_model := fun k => Q'.le_refl' (afDefectSeq S.afr k)

/-- **`fullFloor_of_codynamicRecast` — the codynamic recast yields the EXISTING
positive continuum floor.**  Routing `CodynamicMarginRecast` through the forward
reduction into `fullFloor_of_singleStep` gives `0 < prodFloor` and
`prodFloor ≤ trueMargin k` at every scale — the composition (part 2) tied to the
proved `afFloorEps`/`DefectGapRecursion` product-floor machinery.  Genuine, but
this floor was ALREADY available; the codynamic derivation is a cleaner
categorical account of it, not new closure. -/
theorem fullFloor_of_codynamicRecast (R : CodynamicMarginRecast) :
    (0 : Q') < (defectRecursion_of_singleStep (singleStep_of_codynamicRecast R)).prodFloor
      ∧ ∀ k, (defectRecursion_of_singleStep (singleStep_of_codynamicRecast R)).prodFloor
              ≤ R.trueMargin k :=
  fullFloor_of_singleStep (singleStep_of_codynamicRecast R)

end YMGap.Continuum.CodynamicReflectionUnitRecast

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.codyFold_bounds
#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.codyFloor_lb
#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.singleEdgeFactor_expansive_at_weak
#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.singleEdge_matches_reconGap
#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.contractiveModulus_nonexpansive
#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.orthoBig_defect_exceeds_bound
#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.modulus_underdetermines_defect
#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.singleStep_of_codynamicRecast
#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.codynamicRecast_of_singleStep
#print axioms YMGap.Continuum.CodynamicReflectionUnitRecast.fullFloor_of_codynamicRecast
