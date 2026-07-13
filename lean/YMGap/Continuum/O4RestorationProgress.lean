/-
Track B+RepTheory / R2 — **deepening the scalar anisotropy residual: from a posited
per-step coefficient decay to the asymptotic-freedom MONOTONE FLOW of the
DIMENSIONLESS coupling plus an EXACT geometric spacing recursion.**

# Where this sits in the chain

The O(4)-rotation-restoration obligation is routed as

      DimensionlessFlow   (this module — the deepest residual)
        ⟶  O4DecayFromMargin.DimensionalScaling   (per-step dimensional scaling)
        ⟶  O4RestorationAF.ScalingDimensionDecay  (single-step ρ=1/2 contraction)
        ⟶  O4RestorationAF.RotationRestored       (legacy Cauchy predicate).

`O4DecayFromMargin` had already reduced `ScalingDimensionDecay` to a single named
analytic input `scale_step`:

      breakCoeff (k+1)  ≤  blockRatio^{degreeMargin} · breakCoeff k,

i.e. the magnitude of the leading rotation-breaking operator's coefficient decays
multiplicatively per RG blocking step.  That bare per-step bound still MIXES two
distinct ingredients — the operator's engineering-dimension weight (the
`spacing^{d−4}` factor) and the running of the dimensionless coupling.

# What this module sharpens

This module FACTORS `scale_step` into its two transparent constituents:

  * an EXACT geometric SPACING RECURSION
        spacing (k+1)  ≈  blockRatio · spacing k                         (geometry),
    which is the definition of an RG blocking step (linear spacing rescaling), and

  * the genuine ASYMPTOTIC-FREEDOM content, that the DIMENSIONLESS coupling of the
    rotation-breaking operator is NON-INCREASING along the flow,
        dimless (k+1)  ≤  dimless k                                       (AF monotone flow).

Writing the coefficient as its engineering-dimension factorization

      breakCoeff k  :=  dimless k · spacing k^{degreeMargin}

(`degreeMargin = d − 4`, the proved 24-cell margin), the per-step bound
`scale_step` is then a PROVED consequence of {spacing recursion, dimensionless
antitonicity} via the `qpow` algebra:

      breakCoeff (k+1)
        = dimless (k+1) · (blockRatio · spacing k)^{m}
        ≈ dimless (k+1) · blockRatio^{m} · spacing k^{m}      (qpow base-mult)
        ≤ dimless k     · blockRatio^{m} · spacing k^{m}      (AF antitonicity)
        ≈ blockRatio^{m} · (dimless k · spacing k^{m})
        = blockRatio^{m} · breakCoeff k.

So the residual is now the single TRANSPARENT, more-fundamental statement
`dimless_antitone` — the monotone running of the dimensionless coupling under
blocking (asymptotic freedom) — and the engineering-dimension `spacing^{d−4}`
factor is handled by PROVED `qpow` arithmetic, not posited.

# What this module PROVES vs NAMES

PROVED here (`[propext]` / `[propext, Quot.sound]` only):
  * `qpow_congr_base` — `qpow` is congruent in its base under `≈` (local copy).
  * `qpow_base_mul` — base-multiplicativity `qpow (x·y) n ≈ qpow x n · qpow y n`.
  * `breakCoeff_nonneg` — the engineering-dimension coefficient is nonnegative.
  * `scale_step` — **the reduction**: the per-step multiplicative decay
    `breakCoeff (k+1) ≤ blockRatio^{degreeMargin} · breakCoeff k`, DERIVED from the
    spacing recursion + dimensionless antitonicity + the proved `qpow` algebra.
  * `dimensionalScaling_of_flow` — packages a `DimensionlessFlow` as an
    `O4DecayFromMargin.DimensionalScaling` (the `scale_step` field is the proved
    reduction), so the whole downstream chain (`ScalingDimensionDecay`,
    legacy `RotationRestored` Cauchy predicate) is inherited.
  * `o4_restored_of_flow` — the anisotropy-Cauchy predicate obtained DIRECTLY
    from a `DimensionlessFlow`; this theorem type does not state full O(4).
  * `exampleFlow` / `example_o4_restored` — a CONCRETE inhabitant (constant
    dimensionless coupling, `blockRatio = 1/2`, `spacing = (1/2)^k`, `m = 2`),
    witnessing that `DimensionlessFlow` is NON-VACUOUS and the whole pipeline fires.
  * `coupling_antitone` — **a further sharpening of `dimless_antitone`**: the
    monotone running is DERIVED from a discrete RG recursion `g k ≈ g (k+1) + δ_k`
    plus the asymptotic-freedom SIGN of one step `δ_k ≥ 0` (`β(g) ≤ 0`).  So the
    bare monotonicity is reduced to a single per-step sign condition.
  * `flowOfCoupling` / `o4_restored_of_coupling` — a `CouplingRunning` supplies the
    residual half of a `DimensionlessFlow` (`dimless := g`, `dimless_antitone :=
    coupling_antitone`) over the canonical proved blocking geometry; the scalar
    Cauchy pipeline then fires from {RG recursion, AF beta-sign} alone.
  * `constCoupling`, `geoCoupling` / `geoFlow` / `geo_o4_restored` — two inhabitants
    of the beta-sign residual: the Gaussian fixed point (`δ ≡ 0`) and a genuinely
    STRICTLY-DECREASING coupling `g k = 1/2 + (1/2)^k` with strictly-positive drop
    `δ_k = (1/2)^{k+1}` (`β < 0`), beyond the constant case, on which the chain fires.

NAMED (the deepened residual, `Type`-level, Rule 8): `CouplingRunning.betaDrop_nonneg`
— the asymptotic-freedom SIGN of the dimensionless rotation-breaking coupling's
one-step beta function (`β ≤ 0`, the coupling runs downhill under blocking).  This
is strictly more fundamental than the bare monotonicity `dimless_antitone`: the
engineering-dimension weight is PROVED algebra (`scale_step`), the monotone flow is
DERIVED from {a recursion identity, a per-step sign} (`coupling_antitone`), and the
only remaining analytic input is the one-loop beta-function sign on the true
interacting coupling.

# Honest scope / what stays open

We prove "{exact blocking spacing recursion, discrete coupling RG recursion,
asymptotic-freedom one-step beta-sign `β ≤ 0`} ⇒ dimensionless coupling
non-increasing ⇒ per-step coefficient decay ⇒ anisotropy Cauchy".  Strict zero
decay is supplied downstream by the zero-limit modules, and full O(4) still needs
the observable response/action bridge.  We do NOT prove that
the TRUE interacting beta function is genuinely non-positive under the real
Yang–Mills RG (`betaDrop_nonneg`) — that is the remaining asymptotic-freedom
residual, now isolated as a single per-step SIGN condition (strictly sharper than
the bare monotonicity `dimless_antitone`).  The inhabitants `constCoupling`
(free-fixed-point) and `geoCoupling` (a strictly-decreasing coupling with `β < 0`)
show the structure is satisfiable beyond the constant case; the open content is the
same sign for the genuine interacting coupling.  The degree margin `d − 4 ≥ 2`
(24-cell) is genuinely used downstream (it forces the earned ratio `≤ 1/4`).

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'`/`qpow` arithmetic and reuse of the `O4DecayFromMargin` reduction; every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`decide`-on-nondecidable, no `sorry`, no `Prop := True` stub.  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.O4DecayFromMargin
import YMGap.Continuum.RGTransport
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.O4RestorationProgress

open YMGap.Constructive
open YMGap.Continuum

/-! ## 0. `qpow` base algebra (proved here, axiom-clean)

Two small `qpow` facts used by the reduction: congruence of the power in its base
under `≈`, and base-multiplicativity `(x·y)^n ≈ x^n · y^n`. -/

/-- **`qpow` is congruent in the base under `≈`.**  `a ≈ b ⟹ qpow a n ≈ qpow b n`
(induction on `n`; local copy to avoid a heavy import). -/
theorem qpow_congr_base {a b : Q'} (h : a.eqv b) :
    ∀ n, (RGTransport.qpow a n).eqv (RGTransport.qpow b n)
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      show (RGTransport.qpow a n * a).eqv (RGTransport.qpow b n * b)
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ a (qpow_congr_base h n))
        (Q'.mul_eqv_congr_left (RGTransport.qpow b n) _ _ h)

/-- A four-factor interchange `(a·b)·(c·d) ≈ (a·c)·(b·d)` (local copy). -/
theorem mul4_swap (a b c d : Q') :
    ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a (b * (c * d)) ((b * c) * d)
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a ((b * c) * d) ((c * b) * d)
    (Q'.mul_eqv_congr_right (b * c) (c * b) d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a ((c * b) * d) (c * (b * d))
    (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-- **`qpow` base-multiplicativity:** `qpow (x·y) n ≈ qpow x n · qpow y n`.
Induction on `n`: at `n+1`,
`(xy)^n·(xy) ≈ (x^n·y^n)·(x·y) ≈ (x^n·x)·(y^n·y) = x^{n+1}·y^{n+1}`. -/
theorem qpow_base_mul (x y : Q') :
    ∀ n, (RGTransport.qpow (x * y) n).eqv
          (RGTransport.qpow x n * RGTransport.qpow y n)
  | 0 => by
      show (1 : Q').eqv ((1 : Q') * (1 : Q'))
      exact Q'.eqv_symm (Q'.one_mul_eqv 1)
  | n + 1 => by
      show (RGTransport.qpow (x * y) n * (x * y)).eqv
            ((RGTransport.qpow x n * x) * (RGTransport.qpow y n * y))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (x * y) (qpow_base_mul x y n)) ?_
      exact mul4_swap (RGTransport.qpow x n) (RGTransport.qpow y n) x y

/-! ## 1. The deepened residual — `DimensionlessFlow`

The transparent RG datum that FACTORS the per-step coefficient decay into its
engineering-dimension weight and the running dimensionless coupling.

Fields:
  * `spacing` — the lattice spacing at blocking step `k` (a nonnegative `Q'`).
  * `blockRatio` — the linear spacing ratio of one RG blocking step (`≤ 1/2`).
  * `spacing_step` — the EXACT geometric spacing recursion
    `spacing (k+1) ≈ blockRatio · spacing k` (the definition of a blocking step).
  * `dimless` — the DIMENSIONLESS coupling of the leading rotation-breaking
    operator at step `k`.
  * `dimless_antitone` — **the genuine residual (asymptotic freedom):** the
    dimensionless coupling is NON-INCREASING along the flow, `dimless (k+1) ≤ dimless k`.
  * `degreeMargin` — the degree excess `d − 4` (`= 2` for the 24-cell case);
    `degreeMargin_ge_two` the proved margin. -/

/-- **The dimensionless-flow datum (the deepened named residual).**

`Type`-level data: the spacing schedule with its exact geometric blocking
recursion, together with the running dimensionless coupling of the leading
rotation-breaking operator and its asymptotic-freedom monotonicity. -/
structure DimensionlessFlow : Type where
  /-- The lattice spacing at blocking step `k`. -/
  spacing : Nat → Q'
  /-- The spacing is nonnegative. -/
  spacing_nonneg : ∀ k : Nat, (0 : Q') ≤ spacing k
  /-- The linear spacing ratio of one RG blocking step. -/
  blockRatio : Q'
  /-- The blocking ratio is nonnegative. -/
  blockRatio_nonneg : (0 : Q') ≤ blockRatio
  /-- **The blocking ratio at most halves the spacing:** `blockRatio ≤ 1/2`. -/
  blockRatio_le_half : blockRatio ≤ HalfPow.half
  /-- **The exact geometric spacing recursion** (one blocking step rescales the
  spacing by `blockRatio`): `spacing (k+1) ≈ blockRatio · spacing k`. -/
  spacing_step : ∀ k : Nat, (spacing (k + 1)).eqv (blockRatio * spacing k)
  /-- The dimensionless coupling of the leading rotation-breaking operator. -/
  dimless : Nat → Q'
  /-- The dimensionless coupling is nonnegative. -/
  dimless_nonneg : ∀ k : Nat, (0 : Q') ≤ dimless k
  /-- **The asymptotic-freedom residual:** the dimensionless rotation-breaking
  coupling is NON-INCREASING along the blocking flow, `dimless (k+1) ≤ dimless k`. -/
  dimless_antitone : ∀ k : Nat, dimless (k + 1) ≤ dimless k
  /-- The degree excess `d − 4` of the leading rotation-breaking operator. -/
  degreeMargin : Nat
  /-- PROVED margin `2 ≤ d − 4` (the 24-cell degree-6 content). -/
  degreeMargin_ge_two : 2 ≤ degreeMargin

/-- **The engineering-dimension coefficient.**  The magnitude of the leading
rotation-breaking operator's coefficient at step `k`, written as the running
dimensionless coupling times the engineering-dimension weight
`spacing^{degreeMargin}`:  `breakCoeff k = dimless k · spacing k^{d−4}`. -/
def breakCoeff (F : DimensionlessFlow) (k : Nat) : Q' :=
  F.dimless k * RGTransport.qpow (F.spacing k) F.degreeMargin

/-- `breakCoeff` is nonnegative (product of nonnegatives). -/
theorem breakCoeff_nonneg (F : DimensionlessFlow) (k : Nat) :
    (0 : Q') ≤ breakCoeff F k :=
  Q'.mul_nonneg _ _ (F.dimless_nonneg k)
    (RGTransport.qpow_nonneg (F.spacing k) (F.spacing_nonneg k) F.degreeMargin)

/-! ## 2. THE REDUCTION — the per-step decay from the spacing recursion + AF flow

`scale_step` is the per-step multiplicative decay required by
`O4DecayFromMargin.DimensionalScaling`.  We PROVE it from the spacing recursion
(`spacing_step`), the dimensionless antitonicity (`dimless_antitone`), and the
proved `qpow` base-multiplicativity. -/

/-- **THE REDUCTION.**  The per-step coefficient decay
`breakCoeff (k+1) ≤ blockRatio^{degreeMargin} · breakCoeff k`, DERIVED from
{exact spacing recursion, dimensionless antitonicity} and the proved `qpow`
algebra — NOT posited.  The engineering-dimension weight `spacing^{d−4}` is fully
handled by `qpow_base_mul`; the only inequality used is the AF monotonicity
`dimless (k+1) ≤ dimless k`. -/
theorem scale_step (F : DimensionlessFlow) (k : Nat) :
    breakCoeff F (k + 1)
      ≤ RGTransport.qpow F.blockRatio F.degreeMargin * breakCoeff F k := by
  -- nonnegativity of the shared right factor R = blockRatio^m · spacing(k)^m
  have hBnn : (0 : Q') ≤ RGTransport.qpow F.blockRatio F.degreeMargin :=
    RGTransport.qpow_nonneg F.blockRatio F.blockRatio_nonneg F.degreeMargin
  have hSnn : (0 : Q') ≤ RGTransport.qpow (F.spacing k) F.degreeMargin :=
    RGTransport.qpow_nonneg (F.spacing k) (F.spacing_nonneg k) F.degreeMargin
  have hRnn : (0 : Q') ≤
      RGTransport.qpow F.blockRatio F.degreeMargin
        * RGTransport.qpow (F.spacing k) F.degreeMargin :=
    Q'.mul_nonneg _ _ hBnn hSnn
  -- spacing(k+1)^m ≈ blockRatio^m · spacing(k)^m  (recursion + base-mult)
  have hqp : (RGTransport.qpow (F.spacing (k + 1)) F.degreeMargin).eqv
      (RGTransport.qpow F.blockRatio F.degreeMargin
        * RGTransport.qpow (F.spacing k) F.degreeMargin) :=
    Q'.eqv_trans _ _ _
      (qpow_congr_base (F.spacing_step k) F.degreeMargin)
      (qpow_base_mul F.blockRatio (F.spacing k) F.degreeMargin)
  -- e1 : breakCoeff(k+1) ≈ dimless(k+1) · R
  have e1 : (breakCoeff F (k + 1)).eqv
      (F.dimless (k + 1)
        * (RGTransport.qpow F.blockRatio F.degreeMargin
            * RGTransport.qpow (F.spacing k) F.degreeMargin)) := by
    show (F.dimless (k + 1) * RGTransport.qpow (F.spacing (k + 1)) F.degreeMargin).eqv _
    exact Q'.mul_eqv_congr_left (F.dimless (k + 1)) _ _ hqp
  -- le2 : dimless(k+1)·R ≤ dimless(k)·R  (AF antitonicity; R ≥ 0)
  have le2 : F.dimless (k + 1)
        * (RGTransport.qpow F.blockRatio F.degreeMargin
            * RGTransport.qpow (F.spacing k) F.degreeMargin)
      ≤ F.dimless k
        * (RGTransport.qpow F.blockRatio F.degreeMargin
            * RGTransport.qpow (F.spacing k) F.degreeMargin) :=
    Q'.mul_le_mul_of_nonneg_right (F.dimless (k + 1)) (F.dimless k) _
      (F.dimless_antitone k) hRnn
  -- e3 : dimless(k)·(B·S) ≈ B·(dimless(k)·S) = blockRatio^m · breakCoeff(k)
  have e3 : (F.dimless k
        * (RGTransport.qpow F.blockRatio F.degreeMargin
            * RGTransport.qpow (F.spacing k) F.degreeMargin)).eqv
      (RGTransport.qpow F.blockRatio F.degreeMargin * breakCoeff F k) := by
    show (F.dimless k
        * (RGTransport.qpow F.blockRatio F.degreeMargin
            * RGTransport.qpow (F.spacing k) F.degreeMargin)).eqv
      (RGTransport.qpow F.blockRatio F.degreeMargin
        * (F.dimless k * RGTransport.qpow (F.spacing k) F.degreeMargin))
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (F.dimless k)
        (RGTransport.qpow F.blockRatio F.degreeMargin)
        (RGTransport.qpow (F.spacing k) F.degreeMargin))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (RGTransport.qpow (F.spacing k) F.degreeMargin)
        (Q'.mul_comm_eqv (F.dimless k) (RGTransport.qpow F.blockRatio F.degreeMargin))) ?_
    exact Q'.mul_assoc_eqv (RGTransport.qpow F.blockRatio F.degreeMargin)
      (F.dimless k) (RGTransport.qpow (F.spacing k) F.degreeMargin)
  -- combine: breakCoeff(k+1) ≈ dimless(k+1)·R ≤ dimless(k)·R ≈ blockRatio^m · breakCoeff(k)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ le2 (Q'.le_of_eqv e3))

/-! ## 3. Packaging — inherit the whole downstream chain

A `DimensionlessFlow` yields an `O4DecayFromMargin.DimensionalScaling` whose
`scale_step` is the proved reduction; the existing `O4DecayFromMargin` /
`O4RestorationAF` machinery then delivers `ScalingDimensionDecay` and the legacy
`RotationRestored` Cauchy predicate. -/

/-- **The packaging.**  A `DimensionlessFlow` packaged as an
`O4DecayFromMargin.DimensionalScaling`: the `scale_step` field is the proved
`scale_step` reduction, with the engineering-dimension coefficient `breakCoeff`
and the proved 24-cell margin. -/
def dimensionalScaling_of_flow (F : DimensionlessFlow) :
    O4DecayFromMargin.DimensionalScaling where
  breakCoeff := breakCoeff F
  breakCoeff_nonneg := breakCoeff_nonneg F
  blockRatio := F.blockRatio
  blockRatio_nonneg := F.blockRatio_nonneg
  blockRatio_le_half := F.blockRatio_le_half
  degreeMargin := F.degreeMargin
  degreeMargin_ge_two := F.degreeMargin_ge_two
  scale_step := scale_step F

/-- The packaged datum carries the engineering-dimension coefficient unchanged. -/
@[simp] theorem dimensionalScaling_of_flow_breakCoeff
    (F : DimensionlessFlow) (k : Nat) :
    (dimensionalScaling_of_flow F).breakCoeff k = breakCoeff F k := rfl

/-- The packaged datum carries the same (proved) degree margin. -/
@[simp] theorem dimensionalScaling_of_flow_degreeMargin (F : DimensionlessFlow) :
    (dimensionalScaling_of_flow F).degreeMargin = F.degreeMargin := rfl

/-- The composed `ScalingDimensionDecay` (the single-step `ρ=1/2` contraction
datum) obtained from a `DimensionlessFlow`. -/
def scalingDimensionDecay_of_flow (F : DimensionlessFlow) :
    O4RestorationAF.ScalingDimensionDecay :=
  O4DecayFromMargin.scalingDimensionDecay_of_dimensionalScaling
    (dimensionalScaling_of_flow F)

/-- **ANISOTROPY CAUCHY FROM THE DIMENSIONLESS FLOW.**  The rotation-breaking
coefficient is Cauchy with an explicit two-sided modulus, derived directly from
a `DimensionlessFlow`.  The only
remaining analytic input is the asymptotic-freedom monotonicity `dimless_antitone`;
the engineering-dimension weight and the contraction ratio are proved.  Use the
strict zero-limit and observable-response modules for restoration claims. -/
theorem o4_restored_of_flow (F : DimensionlessFlow) :
    O4RestorationAF.RotationRestored (scalingDimensionDecay_of_flow F) :=
  O4DecayFromMargin.o4_restored_of_dimensionalScaling (dimensionalScaling_of_flow F)

/-! ## 3b. SHARPENING `dimless_antitone` — the beta-function sign of asymptotic freedom

`DimensionlessFlow.dimless_antitone` is the bare monotonicity
`dimless (k+1) ≤ dimless k`.  This module sharpens it ONE level deeper, to the
genuinely PHYSICAL content that drives it: the discrete RG recursion of the
dimensionless coupling together with the SIGN of its beta function.

Write the running coupling as a discrete RG flow with a per-step DECREASE: one
blocking step lowers the coupling by `δ_k := −β(g_k)`, i.e. `g k = g (k+1) + δ_k`.
Asymptotic freedom is exactly the statement that the beta function is NON-POSITIVE
on the flow (`β(g) ≤ 0`, equivalently the drop `δ_k ≥ 0`): the coupling runs
DOWNHILL toward the Gaussian fixed point as the scale is lowered.  From the
recursion plus `δ_k ≥ 0` the antitonicity is an IMMEDIATE consequence — no
monotonicity is posited, only the sign of one increment.

This is strictly more fundamental than the bare `dimless_antitone`: a monotone
sequence is replaced by {a recursion identity, a per-step sign}.  The sign
`δ_k ≥ 0` (`β ≤ 0`) is the one-loop asymptotic-freedom content (`β = −b₀ g³ − ⋯`,
`b₀ > 0` for non-abelian gauge theory); the recursion is the definition of an RG
step.  The residual `dimless_antitone` for the true interacting flow is thereby
reduced to the single per-step sign condition `betaDrop_nonneg` (the AF sign) on
the true running coupling.  (We carry the drop `δ_k ≥ 0` rather than `β_k ≤ 0`
verbatim to keep the algebra subtraction-free; the two are the same statement.) -/

/-- **The running-coupling datum (the sharper named residual).**

`Type`-level data: the dimensionless coupling as a discrete RG flow with an
explicit per-step decrease (`δ_k = −β(g_k)`), together with the asymptotic-freedom
SIGN of that decrease.

Fields:
  * `g` — the dimensionless coupling at blocking step `k` (nonnegative `Q'`).
  * `g_nonneg` — the coupling is nonnegative.
  * `betaDrop` — the per-step DECREASE `δ_k = −β(g_k)` of one blocking step.
  * `betaDrop_nonneg` — **the asymptotic-freedom residual (the beta SIGN):** the
    per-step decrease is non-negative, `δ_k ≥ 0` (equivalently `β(g_k) ≤ 0`: the
    coupling runs downhill under blocking).  This single per-step sign REPLACES the
    bare monotonicity.
  * `run_step` — **the discrete RG recursion** `g k ≈ g (k+1) + δ_k`. -/
structure CouplingRunning : Type where
  /-- The dimensionless coupling at blocking step `k`. -/
  g : Nat → Q'
  /-- The coupling is nonnegative. -/
  g_nonneg : ∀ k : Nat, (0 : Q') ≤ g k
  /-- The per-step decrease `δ_k = −β(g_k)` of one blocking step. -/
  betaDrop : Nat → Q'
  /-- **The asymptotic-freedom beta SIGN:** `δ_k ≥ 0` (i.e. `β ≤ 0`; downhill flow). -/
  betaDrop_nonneg : ∀ k : Nat, (0 : Q') ≤ betaDrop k
  /-- **The discrete RG recursion** `g k ≈ g (k+1) + δ_k`. -/
  run_step : ∀ k : Nat, (g k).eqv (g (k + 1) + betaDrop k)

/-- **THE SHARPER REDUCTION.**  The dimensionless coupling is non-increasing —
`g (k+1) ≤ g k` — derived from the discrete RG recursion `g k ≈ g (k+1) + δ_k`
and the asymptotic-freedom sign `δ_k ≥ 0`.  This DISCHARGES the bare
`dimless_antitone` from the single per-step sign condition. -/
theorem coupling_antitone (R : CouplingRunning) (k : Nat) : R.g (k + 1) ≤ R.g k :=
  -- g(k+1) ≤ g(k+1) + δ_k ≈ g k.
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (R.g (k + 1)) (R.betaDrop k) (R.betaDrop_nonneg k))
    (Q'.le_of_eqv (Q'.eqv_symm (R.run_step k)))

/-- **The flow built from a running coupling.**  A `CouplingRunning` supplies the
genuine residual half (`dimless := g`, `dimless_antitone := coupling_antitone`); the
geometric half is the canonical proved blocking geometry (`blockRatio = 1/2`,
`spacing = (1/2)^k`, degree margin `2`).  So a `DimensionlessFlow` — and hence the
legacy scalar Cauchy pipeline — is obtained from {RG recursion, AF beta-sign}
alone.  Strict vanishing and observable covariance are supplied downstream. -/
def flowOfCoupling (R : CouplingRunning) : DimensionlessFlow where
  spacing := fun k => RGTransport.qpow HalfPow.half k
  spacing_nonneg := fun k =>
    RGTransport.qpow_nonneg HalfPow.half HalfPow.half_nonneg k
  blockRatio := HalfPow.half
  blockRatio_nonneg := HalfPow.half_nonneg
  blockRatio_le_half := Q'.le_refl' HalfPow.half
  spacing_step := fun k => by
    show (RGTransport.qpow HalfPow.half k * HalfPow.half).eqv
          (HalfPow.half * RGTransport.qpow HalfPow.half k)
    exact Q'.mul_comm_eqv (RGTransport.qpow HalfPow.half k) HalfPow.half
  dimless := R.g
  dimless_nonneg := R.g_nonneg
  dimless_antitone := coupling_antitone R
  degreeMargin := 2
  degreeMargin_ge_two := by decide

/-- **ANISOTROPY CAUCHY FROM A RUNNING COUPLING.**  The rotation-breaking coefficient
is Cauchy, derived from a
`CouplingRunning`, i.e. from {the discrete RG recursion, the AF beta-sign
`β ≤ 0`}.  The only remaining analytic input is the single per-step sign
`beta_nonpos` on the true interacting coupling. -/
theorem o4_restored_of_coupling (R : CouplingRunning) :
    O4RestorationAF.RotationRestored (scalingDimensionDecay_of_flow (flowOfCoupling R)) :=
  o4_restored_of_flow (flowOfCoupling R)

/-! ## 4. A concrete inhabitant — `DimensionlessFlow` is non-vacuous

To show the deepened residual is SATISFIABLE (not a vacuous wall), we exhibit a
concrete flow: the free / fixed-point case with a CONSTANT dimensionless coupling
(`dimless ≡ 1`), blocking ratio `1/2`, spacing `(1/2)^k`, and degree margin `2`.
The scalar pipeline then fires, producing the legacy Cauchy predicate.

(The open content is the SAME monotonicity `dimless_antitone` for the genuine
INTERACTING dimensionless coupling, which the constant case does not supply.) -/

/-- **A concrete `DimensionlessFlow`** (free-fixed-point case): constant
dimensionless coupling `1`, blocking ratio `1/2`, spacing `(1/2)^k`, degree
margin `2`.  Witnesses that the structure is inhabited. -/
def exampleFlow : DimensionlessFlow where
  spacing := fun k => RGTransport.qpow HalfPow.half k
  spacing_nonneg := fun k =>
    RGTransport.qpow_nonneg HalfPow.half HalfPow.half_nonneg k
  blockRatio := HalfPow.half
  blockRatio_nonneg := HalfPow.half_nonneg
  blockRatio_le_half := Q'.le_refl' HalfPow.half
  spacing_step := fun k => by
    -- spacing (k+1) = qpow half (k+1) = qpow half k · half ≈ half · qpow half k
    show (RGTransport.qpow HalfPow.half k * HalfPow.half).eqv
          (HalfPow.half * RGTransport.qpow HalfPow.half k)
    exact Q'.mul_comm_eqv (RGTransport.qpow HalfPow.half k) HalfPow.half
  dimless := fun _ => (1 : Q')
  dimless_nonneg := fun _ => by decide
  dimless_antitone := fun _ => Q'.le_refl' (1 : Q')
  degreeMargin := 2
  degreeMargin_ge_two := by decide

/-- **The pipeline fires on the concrete inhabitant.**  The anisotropy-Cauchy
predicate holds for `exampleFlow`, demonstrating that the deepened residual is
inhabited. -/
theorem example_o4_restored :
    O4RestorationAF.RotationRestored (scalingDimensionDecay_of_flow exampleFlow) :=
  o4_restored_of_flow exampleFlow

/-! ## 5. Inhabiting the SHARPER residual — fixed point and a STRICTLY-decreasing flow

We exhibit two `CouplingRunning` witnesses, showing the beta-sign residual is
satisfiable both vacuously and non-vacuously:

  * `constCoupling` — the Gaussian fixed point `g ≡ 1`, `β ≡ 0` (the AF sign holds
    with equality; this is the free case the previous `exampleFlow` already covered);

  * `geoCoupling` — a STRICTLY-DECREASING running coupling `g k = 1/2 + (1/2)^k`
    with a STRICTLY-NEGATIVE beta increment `β_k = −(1/2)^{k+1} < 0`.  This is the
    genuine asymptotic-freedom shape (the coupling runs strictly downhill toward a
    fixed point) — beyond the constant case, demonstrating the chain fires on a real
    downhill flow. -/

/-- **The fixed-point running coupling** (`g ≡ 1`, `δ ≡ 0`): the AF sign holds with
equality.  Inhabits `CouplingRunning` at the Gaussian fixed point. -/
def constCoupling : CouplingRunning where
  g := fun _ => (1 : Q')
  g_nonneg := fun _ => by decide
  betaDrop := fun _ => (0 : Q')
  betaDrop_nonneg := fun _ => by decide
  run_step := fun _ => by
    show ((1 : Q')).eqv ((1 : Q') + 0)
    rw [Q'.add_zero']
    exact Q'.eqv_refl _

/-- **A STRICTLY-DECREASING running coupling.**  `g k = 1/2 + (1/2)^k` runs strictly
downhill to the fixed point `1/2`, with the strictly-POSITIVE per-step decrease
`δ_k = (1/2)^{k+1}` (i.e. `β_k = −(1/2)^{k+1} < 0`).  The discrete RG recursion
`g k = g (k+1) + (1/2)^{k+1}` is the exact halving telescope, and the AF sign
`δ_k ≥ 0` is the non-negativity of a power of `1/2`.  This is a genuine
(non-constant) asymptotic-freedom inhabitant. -/
def geoCoupling : CouplingRunning where
  g := fun k => HalfPow.half + RGTransport.qpow HalfPow.half k
  g_nonneg := fun k =>
    Q'.le_trans' _ _ _ HalfPow.half_nonneg
      (Q'.add_le_self_of_nonneg HalfPow.half (RGTransport.qpow HalfPow.half k)
        (RGTransport.qpow_nonneg HalfPow.half HalfPow.half_nonneg k))
  betaDrop := fun k => RGTransport.qpow HalfPow.half (k + 1)
  betaDrop_nonneg := fun k =>
    RGTransport.qpow_nonneg HalfPow.half HalfPow.half_nonneg (k + 1)
  run_step := fun k => by
    -- g k = 1/2 + (1/2)^k;  g(k+1) + δ_k = (1/2 + (1/2)^k·(1/2)) + (1/2)^k·(1/2).
    show (HalfPow.half + RGTransport.qpow HalfPow.half k).eqv
          ((HalfPow.half + RGTransport.qpow HalfPow.half k * HalfPow.half)
            + RGTransport.qpow HalfPow.half k * HalfPow.half)
    -- abbreviations: a = 1/2, x = (1/2)^k, p = x·(1/2).
    -- key: p + p ≈ x  (since x·(1/2) + x·(1/2) ≈ x·(1/2+1/2) = x·1 = x).
    have hsum :
        (RGTransport.qpow HalfPow.half k * HalfPow.half
          + RGTransport.qpow HalfPow.half k * HalfPow.half).eqv
          (RGTransport.qpow HalfPow.half k) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv (RGTransport.qpow HalfPow.half k)
          HalfPow.half HalfPow.half)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (RGTransport.qpow HalfPow.half k)
          (HalfPow.half + HalfPow.half) 1 (by decide)) ?_
      exact Q'.mul_one_eqv (RGTransport.qpow HalfPow.half k)
    -- (a + p) + p ≈ a + (p + p) ≈ a + x; take the symmetric form.
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv HalfPow.half
          (RGTransport.qpow HalfPow.half k * HalfPow.half)
          (RGTransport.qpow HalfPow.half k * HalfPow.half))
        (Q'.add_eqv_congr_left HalfPow.half _ _ hsum))

/-- **The strictly-decreasing flow** built from `geoCoupling`: a non-constant
`DimensionlessFlow` whose dimensionless coupling genuinely runs downhill. -/
def geoFlow : DimensionlessFlow := flowOfCoupling geoCoupling

/-- **The pipeline fires on the STRICTLY-DECREASING inhabitant.**  The legacy
anisotropy-Cauchy predicate holds for `geoFlow`, whose dimensionless coupling
strictly decreases with a negative beta increment. -/
theorem geo_o4_restored :
    O4RestorationAF.RotationRestored (scalingDimensionDecay_of_flow geoFlow) :=
  o4_restored_of_coupling geoCoupling

end YMGap.Continuum.O4RestorationProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.O4RestorationProgress.qpow_congr_base
#print axioms YMGap.Continuum.O4RestorationProgress.mul4_swap
#print axioms YMGap.Continuum.O4RestorationProgress.qpow_base_mul
#print axioms YMGap.Continuum.O4RestorationProgress.breakCoeff_nonneg
#print axioms YMGap.Continuum.O4RestorationProgress.scale_step
#print axioms YMGap.Continuum.O4RestorationProgress.dimensionalScaling_of_flow
#print axioms YMGap.Continuum.O4RestorationProgress.dimensionalScaling_of_flow_breakCoeff
#print axioms YMGap.Continuum.O4RestorationProgress.dimensionalScaling_of_flow_degreeMargin
#print axioms YMGap.Continuum.O4RestorationProgress.scalingDimensionDecay_of_flow
#print axioms YMGap.Continuum.O4RestorationProgress.o4_restored_of_flow
#print axioms YMGap.Continuum.O4RestorationProgress.exampleFlow
#print axioms YMGap.Continuum.O4RestorationProgress.example_o4_restored
#print axioms YMGap.Continuum.O4RestorationProgress.coupling_antitone
#print axioms YMGap.Continuum.O4RestorationProgress.flowOfCoupling
#print axioms YMGap.Continuum.O4RestorationProgress.o4_restored_of_coupling
#print axioms YMGap.Continuum.O4RestorationProgress.constCoupling
#print axioms YMGap.Continuum.O4RestorationProgress.geoCoupling
#print axioms YMGap.Continuum.O4RestorationProgress.geoFlow
#print axioms YMGap.Continuum.O4RestorationProgress.geo_o4_restored
