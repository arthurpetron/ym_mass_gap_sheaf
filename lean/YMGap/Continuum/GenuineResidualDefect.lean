/-
⚠️ DEPRECATED ROUTE (2026-06-27) — NOT a live path to the mass gap. ⚠️
The full-mode product-floor chain in this file (`genuine_fullMode_gap`, etc.) is
CONDITIONAL on the per-mode relative-residual bound `hbound` (concretely
`BondMovingRelResidual.FusionRelResidualBound`).  That bound was found FALSE: the
bond-moving (pointwise-product `K_w^p`) relative residual is LINEAR `O(1−w)`, not
quadratic `O((1−w)²)` — verified numerically, per-step defect `≈ 0.4374·(1−w)`,
power 1.00.  Hence along the AF rate `Σ_k d_k ~ Σ 1/k` DIVERGES and the product
floor → 0: NO positive gap.  The `d_quad` premise (`d_k ≤ M(1−w_k)²`) is false for
the genuine defect.  Reason: the pointwise product of heat kernels is not a heat
kernel (deviation `O(1−w)` per step); only the full Migdal–Kadanoff step (bond-move
+ DECIMATION) could be quadratic, and MK is uncontrolled in `d>1` anyway.  This
chain is retained for its reusable `Q'`/`Nat` lemmas (the summation half, the
moment machinery) ONLY; it does not establish a gap.  See
`project_os2_critical_path_map` memory for the full diagnosis.

Track B / R2 — the **genuine relative-residual** full-mode defect, replacing the
divergent `C₄²` envelope with the `K_τ`-normalized residual.

# The fix this module installs (and the precise honesty of it)

The full-mode chain previously measured the per-step quadratic defect with the
crude all-mode Casimir-square ENVELOPE

    casimirSqSum  =  ∑_s μ_τ(s)·qfac(w,s)^q·C₄(s)²,

i.e. the bond-moved coefficient bounded by `C₄(s)²` with NO division by the
heat-kernel coefficient `K_τ`.  Its renormalized form `(1−w)²·casimirSqSum =
∑_s μ_τ(s)·(1+(1−w)C₄(s))^q·((1−w)C₄(s))²` does NOT tend to `0` as `τ → 0`: the
`C₄(s)² = (y_s/τ)²` factor manufactures a spurious `τ^{−2}` that cancels the
`(1−w)² ≍ τ²` margin, leaving a positive CONSTANT (not summable).

The CORRECT object is the `K_τ`-NORMALIZED scaled norm of the GENUINE relative
residual `rrel_s` — the bond-moved coefficient measured *relative to the retuned
heat-kernel coefficient* `K_τ(s)`.  By the project's marginal→quadratic
mechanism, the relative residual is genuinely `O((1−w)²)` per mode, with the test
factor a BOUNDED Gaussian moment of `y_s = (1−w)·C₄(s)` (a polynomial in `y_s`,
hence `O(1)` on the active modes), NOT the unbounded `C₄(s)² = (y_s/τ)²`.

# What is built here (abstract over the per-mode residual bound)

This module works ABSTRACTLY.  The per-mode residual bound is taken as a NAMED
hypothesis carried by a `Type`-level structure `GenuineResidualBound`; the
summation half is PROVED here; the chain is fired here.  A parallel effort proves
the concrete per-mode bound and plugs it into the structure verbatim.

  * `GenuineResidualBound afr q m r S N₀` — carries the per-step
    relative-residual sequences `rrel k`, a FIXED w-independent nonneg-coefficient
    test polynomial `P`, the strict-positivity / `Zsum`-positivity / fixed-cutoff
    moment certificates (the `moment_bound` inputs, named per step), and the
    load-bearing per-mode bound
        `hbound : ∀ k s, |rrel k s| ≤ (1−w_k)²·Peval P (yArg w_k s)`.

  * `scaledNorm_le_momentSum` (THE SUMMATION HALF).  Termwise the `hbound`
    pulls the constant `(1−w_k)²` out of the finite scaled-norm sum:
        scaledNorm w N₀ hZ q (rrel k) n  ≤  (1−w_k)²·momentSum w N₀ hZ q P n.
    Same shape as the envelope's `momentSum_sq_factor`, but with a GENERAL test
    polynomial `P` and the residual bounded by `(1−w)²·P(y_s)` rather than EQUAL
    to the `C₄²` envelope.

  * `Muniform` / `momentSum_le_Muniform` — the polynomial moment is bounded
    UNIFORMLY in `w` by `momentM P q r S` (a function of `(P,q,r,S)` only) via the
    already-proved fixed-cutoff `moment_bound`.  THE KEY DIFFERENCE from the
    broken envelope: the test is the FIXED polynomial `Peval P (y_s)` — a BOUNDED
    Gaussian moment of `y_s = τ·C₄(s)` — not `C₄(s)² = (y_s/τ)²` (which is what
    manufactured the spurious `τ^{−2}`).

  * `fullModeDefect_genuine` — combines the two halves into a `FullModeDefect`
    with `M = Muniform`, `d k = scaledNorm w_k N₀ hZ q (rrel k) (S+Mwin)`, and the
    clean quadratic bound `d k ≤ Muniform·(1−w_k)²`.

  * `genuine_fullMode_gap` (THE DELIVERABLE) — fires the full-mode chain capstone
    on that defect to a STRICTLY POSITIVE product floor, conditional ONLY on the
    honest named per-mode residual bound `hbound` (plus the fixed-cutoff moment
    certificates).

# Honest scope (AGENTS.md Rule 6)

This REPLACES the divergent `C₄²` envelope with the `K_τ`-normalized genuine
relative residual.  The remaining hypotheses are:

  * the per-mode residual bound `hbound` — the conjectural fusion
    near-cancellation (the marginal→quadratic mechanism), targeted in PARALLEL
    by a concrete effort; NOT proved here.
  * the fixed-cutoff moment certificates `moment_bound` consumes (`hsummand`,
    `hcut`, `hhead`, `hwpos`, `hZ`, `hSN`) — discharged by `decide` at any
    concrete `w`; the moving-cutoff (uniform-over-all-`w`) upgrade is a NAMED
    follow-up (carry it via the partition certificate + pillars +
    `geom_beats_pow`), NOT done here.

Still s=1-retuning / FINITE fusion degree `N₀` / the named two-loop AF recurrence
(`AFRateModulus`) / tail `k ≥ k₀`.  This is the CORRECT-object conditional chain
(one honest per-mode hypothesis), NOT a 4D Yang–Mills mass-gap proof.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and composition over already-proved engines; every
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.  All constants
and moduli are `Type`-level data.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.BondMovingMoment
import YMGap.Continuum.FullModeAssembly
import YMGap.Continuum.AFRateCalibration

namespace YMGap.Continuum.GenuineResidualDefect

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.AFRateCalibration

/-! ## 0. The `fsum`/`finSum` bridge

`scaledNorm` (in `BondMovingScaledNorm`) sums with `BondMovingStep.fsum` while
`momentSum` (in `BondMovingMoment`) sums with `RationalTail.finSum`.  The two are
structurally identical recursions, equal at every length by induction. -/

/-- `BondMovingStep.fsum f n = RationalTail.finSum f n` (both are the same
`Σ_{i<n}` recursion). -/
theorem fsum_eq_finSum (f : Nat → Q') : ∀ n, fsum f n = RationalTail.finSum f n
  | 0 => rfl
  | n + 1 => by
      show fsum f n + f n = RationalTail.finSum f n + f n
      rw [fsum_eq_finSum f n]

/-! ## 1. THE SUMMATION HALF (proved here)

The summation half is stated and proved BEFORE the interface so it reads as a
standalone fact about the scaled norm of any sequence bounded per mode by
`(1−w)²·Peval P (yArg w s)`. -/

/-- **The per-summand `(1−w)²` domination.**  Under the per-mode bound `hb`, each
scaled-norm summand is `≤ (1−w)²` times the corresponding moment summand:

    μ(s)·qfac^q·|rrel s|  ≤  (1−w)²·(μ(s)·qfac^q·Peval P (yArg s)).

PROOF.  `|rrel s| ≤ (1−w)²·Peval P (yArg s)` (the named bound) multiplied by the
nonnegative weight `μ(s)·qfac^q`, then reassociated. -/
theorem scaledNorm_summand_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (P : QPoly.Poly)
    (rr : Nat → Q') (s : Nat)
    (hb : absQ (rr s) ≤ ((1 : Q') - w) * ((1 : Q') - w) * Peval P (yArg w s)) :
    μ w N hZ s * (qfac w s ^ q * absQ (rr s))
      ≤ ((1 : Q') - w) * ((1 : Q') - w)
          * (μ w N hZ s * (qfac w s ^ q * Peval P (yArg w s))) := by
  have hμnn : (0 : Q') ≤ μ w N hZ s := μ_nonneg hw0 N hZ s
  have hqfacnn : (0 : Q') ≤ qfac w s ^ q := Q'.pow_nonneg _ (qfac_nonneg hw1 s) q
  -- Step 1: bound |rr s| termwise inside qfac^q·(·)
  have h1 : qfac w s ^ q * absQ (rr s)
      ≤ qfac w s ^ q * (((1 : Q') - w) * ((1 : Q') - w) * Peval P (yArg w s)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hb hqfacnn
  -- Step 2: multiply by μ ≥ 0
  have h2 : μ w N hZ s * (qfac w s ^ q * absQ (rr s))
      ≤ μ w N hZ s
          * (qfac w s ^ q * (((1 : Q') - w) * ((1 : Q') - w) * Peval P (yArg w s))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h1 hμnn
  refine Q'.le_trans' _ _ _ h2 ?_
  -- Step 3: reassociate μ·(qfac^q·(F·E)) ≃ F·(μ·(qfac^q·E))  via moment_pull_factor
  refine Q'.le_of_eqv ?_
  exact moment_pull_factor (((1 : Q') - w) * ((1 : Q') - w))
    (μ w N hZ s) (qfac w s ^ q) (Peval P (yArg w s))

/-- **THE SUMMATION HALF.**  Under the per-mode bound `hb` (the residual bounded by
`(1−w)²·Peval P (yArg w s)`), the finite-cutoff scaled norm of the genuine
relative residual is `≤ (1−w)²` times the polynomial moment sum:

    scaledNorm w N hZ q rr  ≤  (1−w)²·momentSum w N hZ q P N.

(`scaledNorm` and `momentSum w … N` share the cutoff `N`: `scaledNorm` sums to its
own `N` internally; `momentSum` is evaluated at the same window `N`.)

PROOF.  Termwise domination (`scaledNorm_summand_le`), then pull the constant
`(1−w)²` out of the finite sum (`const_mul_finSum`).  This is the SAME shape as
the envelope's `momentSum_sq_factor`, but for a GENERAL test polynomial `P` and
with the residual bounded by `(1−w)²·Peval P (y_s)` rather than EQUAL to the
`C₄²` envelope. -/
theorem scaledNorm_le_momentSum {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (P : QPoly.Poly)
    (rr : Nat → Q')
    (hb : ∀ s, absQ (rr s)
      ≤ ((1 : Q') - w) * ((1 : Q') - w) * Peval P (yArg w s)) :
    scaledNorm w N hZ q rr
      ≤ ((1 : Q') - w) * ((1 : Q') - w) * momentSum w N hZ q P N := by
  show fsum (fun s => μ w N hZ s * (qfac w s ^ q * absQ (rr s))) N
      ≤ ((1 : Q') - w) * ((1 : Q') - w) * momentSum w N hZ q P N
  rw [fsum_eq_finSum]
  have hterm : ∀ s,
      μ w N hZ s * (qfac w s ^ q * absQ (rr s))
        ≤ ((1 : Q') - w) * ((1 : Q') - w) * momentTerm w N hZ q P s := by
    intro s
    exact scaledNorm_summand_le hw0 hw1 N hZ q P rr s (hb s)
  have hle : RationalTail.finSum
      (fun s => μ w N hZ s * (qfac w s ^ q * absQ (rr s))) N
      ≤ RationalTail.finSum
        (fun s => ((1 : Q') - w) * ((1 : Q') - w) * momentTerm w N hZ q P s) N :=
    CharacterTail.finSum_le_termwise _ _ hterm N
  refine Q'.le_trans' _ _ _ hle ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_symm ?_
  show (((1 : Q') - w) * ((1 : Q') - w) * momentSum w N hZ q P N).eqv
      (RationalTail.finSum
        (fun s => ((1 : Q') - w) * ((1 : Q') - w) * momentTerm w N hZ q P s) N)
  exact RationalTail.const_mul_finSum (fun s => momentTerm w N hZ q P s)
    (((1 : Q') - w) * ((1 : Q') - w)) N

/-! ## 2. The uniform polynomial-moment bound (fixed-cutoff route) -/

/-- **`Muniform`** — the `w`-INDEPENDENT polynomial-moment bound, the fixed-cutoff
`momentM`.  It depends only on `(P, q, r, S)`.  This is the cleanest route: the
test is the FIXED polynomial `Peval P (y_s)` (a BOUNDED Gaussian moment of
`y_s = (1−w)·C₄(s)`), NOT `C₄(s)² = (y_s/τ)²` — so there is no spurious `τ^{−2}`. -/
def Muniform (P : QPoly.Poly) (q r S : Nat) : Q' := momentM P q r S

theorem Muniform_nonneg (P : QPoly.Poly) (hP : nonnegCoeffs P) (q r S : Nat) :
    (0 : Q') ≤ Muniform P q r S := momentM_nonneg P hP q r S

/-- **The uniform moment bound.**  At a fixed cutoff `S ≤ N₀` and the two
fixed-cutoff moving-cutoff inequalities (`hcut`, `hhead`) plus the per-tail-term
Casimir domination (`hsummand`), the polynomial moment is `≤ Muniform`,
uniformly in the window `M`.  This is `moment_bound` directly. -/
theorem momentSum_le_Muniform {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (P : QPoly.Poly) (hP : nonnegCoeffs P) (q m r S N₀ : Nat) (hSN : S ≤ N₀)
    (hZ : (0 : Q') < Zsum w N₀)
    (hsummand : ∀ k,
      momentTerm w N₀ hZ q P (S + k) ≤ tailTerm w (m + 2) (S + k))
    (hcut : Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm w (m + 2) S ≤ dyad (r + 1)) :
    ∀ M, momentSum w N₀ hZ q P (S + M) ≤ Muniform P q r S :=
  moment_bound hw0 hw1 P hP q m r S N₀ hSN hZ hsummand hcut hhead

/-! ## 3. The abstract per-mode residual-bound interface -/

/-- **The genuine relative-residual per-mode bound interface.**  A `Type`-level
structure carrying the data the chain needs, abstractly:

  * `rrel k` — the relative-residual sequence `s ↦ rrel_s` at AF step `k`
    (the bond-moved coefficient *relative to the retuned* `K_τ` coefficient).
  * `P` (with `hP : nonnegCoeffs P`) — a FIXED, w-independent test polynomial
    (the bounded Gaussian-moment test in `y_s = (1−w)·C₄(s)`).
  * `hSN`, `hwpos`, `hZ`, `hsummand`, `hcut`, `hhead` — the fixed-cutoff moment
    certificates (the `moment_bound` inputs, named per step `k`; the AF interface
    only gives `0 ≤ w_k`, hence the explicit `hwpos`).
  * **`hbound`** — the load-bearing per-mode bound, VERBATIM the shape the
    parallel concrete effort targets:

        |rrel k s|  ≤  (1 − w_k)²·Peval P (yArg w_k s).

    The relative residual is `O((1−w_k)²)` per mode with a BOUNDED polynomial
    test `Peval P (y_s)` — NOT the unbounded `C₄(s)²` envelope. -/
structure GenuineResidualBound (afr : AFRateModulus) (q m r S N₀ : Nat) : Type where
  /-- The per-step relative-residual sequences. -/
  rrel : Nat → (Nat → Q')
  /-- The fixed w-independent test polynomial. -/
  P : QPoly.Poly
  /-- `P` has nonnegative coefficients. -/
  hP : nonnegCoeffs P
  /-- `S ≤ N₀` (cutoff inside the fusion degree). -/
  hSN : S ≤ N₀
  /-- Strict positivity of each weight (the AF interface only gives `0 ≤ w`; the
  moment bound needs `0 < w`). -/
  hwpos : ∀ k, (0 : Q') < afr.w k
  /-- The partition positivity guard at the fixed cutoff `N₀`. -/
  hZ : ∀ k, (0 : Q') < Zsum (afr.w k) N₀
  /-- The per-tail-term Casimir domination at each weight. -/
  hsummand : ∀ k k',
    momentTerm (afr.w k) N₀ (hZ k) q P (S + k')
      ≤ tailTerm (afr.w k) (m + 2) (S + k')
  /-- The ratio cutoff inequality at each weight. -/
  hcut : ∀ k,
    Q'.ofNat (2 ^ (m + 2)) * qpow (afr.w k) (2 * S + 3) ≤ HalfPow.half
  /-- The head cutoff inequality at each weight. -/
  hhead : ∀ k, tailTerm (afr.w k) (m + 2) S ≤ dyad (r + 1)
  /-- **The per-mode relative-residual bound** (the honest named hypothesis). -/
  hbound : ∀ k s,
    absQ (rrel k s)
      ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) * Peval P (yArg (afr.w k) s)

/-! ## 4. Building the `FullModeDefect` from the genuine residual

We assemble the two halves into the abstract per-step defect carried by
`FullModeDefect`.  The defect at AF step `k` is the genuine scaled-norm residual
at the fixed cutoff `N₀`, evaluated on the window `S + Mwin`:

    d k  =  scaledNorm w_k N₀ (hZ k) q (rrel k) (S + Mwin).

The clean quadratic bound `d k ≤ Muniform·(1−w_k)²` is the COMPOSITION of:
  (1) the summation half  scaledNorm ≤ (1−w_k)²·momentSum, and
  (2) the uniform moment   momentSum ≤ Muniform,
chained with `(1−w_k)² ≥ 0`. -/

/-- **The genuine per-step defect, packaged with its clean quadratic bound.**
Given the abstract per-mode residual bound (`grb`), a window length `Mwin`, and the
matching `hN : N₀ = S + Mwin` (the fixed cutoff is the head `S` plus the window),
build a `FullModeDefect afr` whose `M = Muniform P q r S` and whose per-step defect
is the genuine `K_τ`-normalized scaled-norm residual
`scaledNorm w_k N₀ (hZ k) q (rrel k)` (summed to its own cutoff `N₀`).

The clean quadratic bound `d k ≤ Muniform·(1−w_k)²` chains the summation half
(`scaledNorm_le_momentSum`) with the uniform moment (`momentSum_le_Muniform`); the
`hN` rewrite aligns the scaled-norm cutoff `N₀` with the moment window `S+Mwin`. -/
def fullModeDefect_genuine (afr : AFRateModulus) (q m r S N₀ : Nat)
    (grb : GenuineResidualBound afr q m r S N₀) (Mwin : Nat) (hN : N₀ = S + Mwin) :
    FullModeDefect afr where
  d := fun k => scaledNorm (afr.w k) N₀ (grb.hZ k) q (grb.rrel k)
  d_nonneg := by
    intro k
    show (0 : Q') ≤ fsum
      (fun s => μ (afr.w k) N₀ (grb.hZ k) s
        * (qfac (afr.w k) s ^ q * absQ (grb.rrel k s))) N₀
    refine fsum_nonneg (fun s => ?_) N₀
    refine Q'.mul_nonneg _ _ (μ_nonneg (afr.w_nonneg k) N₀ (grb.hZ k) s) ?_
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg _ (qfac_nonneg (Q'.le_of_lt (afr.w_lt_one k)) s) q)
      (absQ_nonneg (grb.rrel k s))
  M := Muniform grb.P q r S
  M_nonneg := Muniform_nonneg grb.P grb.hP q r S
  d_quad := by
    intro k
    have hw0 : (0 : Q') ≤ afr.w k := afr.w_nonneg k
    have hw1 : afr.w k ≤ (1 : Q') := Q'.le_of_lt (afr.w_lt_one k)
    have hmarnn : (0 : Q') ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) :=
      Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (Q'.sub_nonneg_of_le hw1)
    -- (1) summation half (at the scaled-norm cutoff N₀)
    have hsum : scaledNorm (afr.w k) N₀ (grb.hZ k) q (grb.rrel k)
        ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)
            * momentSum (afr.w k) N₀ (grb.hZ k) q grb.P N₀ :=
      scaledNorm_le_momentSum hw0 hw1 N₀ (grb.hZ k) q grb.P (grb.rrel k)
        (grb.hbound k)
    -- (2) uniform moment, at window Mwin (N₀ = S + Mwin).  The moment-bound
    -- conclusion is at the window `S + Mwin`; we need it at the cutoff `N₀`.
    -- Convert the window numeral `N₀ → S + Mwin` only inside the moment's *final*
    -- argument via the equation `hN` (a Nat equality between two cutoff windows),
    -- keeping the dependent `hZ`/`grb` arguments at the fixed `N₀`.
    have hmom : momentSum (afr.w k) N₀ (grb.hZ k) q grb.P N₀
        ≤ Muniform grb.P q r S := by
      have hmom0 : momentSum (afr.w k) N₀ (grb.hZ k) q grb.P (S + Mwin)
          ≤ Muniform grb.P q r S :=
        momentSum_le_Muniform (grb.hwpos k) (afr.w_lt_one k) grb.P grb.hP q m r S N₀
          grb.hSN (grb.hZ k) (grb.hsummand k) (grb.hcut k) (grb.hhead k) Mwin
      have hwin : momentSum (afr.w k) N₀ (grb.hZ k) q grb.P N₀
          = momentSum (afr.w k) N₀ (grb.hZ k) q grb.P (S + Mwin) :=
        congrArg (momentSum (afr.w k) N₀ (grb.hZ k) q grb.P) hN
      rw [hwin]; exact hmom0
    -- chain: scaledNorm ≤ (1−w)²·momentSum ≤ (1−w)²·Muniform ≃ Muniform·(1−w)²
    have hstep : ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)
          * momentSum (afr.w k) N₀ (grb.hZ k) q grb.P N₀
        ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) * Muniform grb.P q r S :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hmom hmarnn
    refine Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ hstep ?_)
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv (((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)) (Muniform grb.P q r S))

/-! ## 5. THE DELIVERABLE — the genuine full-mode gap -/

/-- **THE GENUINE FULL-MODE GAP.**  Along ANY AF rate `afr` carrying an abstract
genuine-relative-residual bound `grb` (and a window length `Mwin`), the running
product of the renormalized full-mode per-block rates `ρ_j = 1 − δ_ren(w_{k₀+j})`
over the tail `k ≥ k₀` has a STRICTLY POSITIVE floor: a constructive-real `floor`
with a positive rational lower bound `ε > 0`, and `floor ≤ ∏_{j<n} ρ_j` for every
prefix `n`.

Here the per-step defect `δ_ren(w_k) = scaledNorm w_k N₀ (hZ k) q (rrel k)`
(summed to the fixed cutoff `N₀ = S + Mwin`) is the `K_τ`-NORMALIZED scaled norm
of the GENUINE relative residual — NOT the divergent `C₄²` envelope.  This fires
`fullMode_gap_of_AFRate` on the genuine defect built by `fullModeDefect_genuine`.

REMAINING NAMED SCOPE (each load-bearing, none hidden):
  (i)   `grb.hbound` — the per-mode relative-residual bound
        `|rrel k s| ≤ (1−w_k)²·Peval P (yArg w_k s)` (the conjectural fusion
        near-cancellation / marginal→quadratic mechanism, targeted in PARALLEL).
  (ii)  `grb.hsummand`/`grb.hcut`/`grb.hhead`/`grb.hwpos`/`grb.hZ`/`grb.hSN` —
        the fixed-cutoff moment certificates (the `moment_bound` inputs).  The
        moving-cutoff (uniform-over-all-`w`) upgrade is a NAMED follow-up.
  (iii) s=1-MATCHED renormalization; FINITE fusion degree `N₀`; tail `k ≥ k₀`;
        AF rate the named two-loop input (`AFRateModulus`).

This is the CORRECT-object conditional chain (one honest per-mode hypothesis)
replacing the broken envelope — NOT a 4D Yang–Mills mass-gap proof. -/
def genuine_fullMode_gap (afr : AFRateModulus) (q m r S N₀ : Nat)
    (grb : GenuineResidualBound afr q m r S N₀) (Mwin : Nat) (hN : N₀ = S + Mwin) :
    Σ' (floor : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat floor ε
      ∧ ∀ n, CReal.leRat floor
          (RGGapPersistence.prodPrefix
            (fmTailRate afr (fullModeDefect_genuine afr q m r S N₀ grb Mwin hN)
              (fmCutoff afr (fullModeDefect_genuine afr q m r S N₀ grb Mwin hN))) n) :=
  fullMode_gap_of_AFRate afr (fullModeDefect_genuine afr q m r S N₀ grb Mwin hN)

end YMGap.Continuum.GenuineResidualDefect

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GenuineResidualDefect.fsum_eq_finSum
#print axioms YMGap.Continuum.GenuineResidualDefect.scaledNorm_summand_le
#print axioms YMGap.Continuum.GenuineResidualDefect.scaledNorm_le_momentSum
#print axioms YMGap.Continuum.GenuineResidualDefect.Muniform_nonneg
#print axioms YMGap.Continuum.GenuineResidualDefect.momentSum_le_Muniform
#print axioms YMGap.Continuum.GenuineResidualDefect.fullModeDefect_genuine
#print axioms YMGap.Continuum.GenuineResidualDefect.genuine_fullMode_gap
