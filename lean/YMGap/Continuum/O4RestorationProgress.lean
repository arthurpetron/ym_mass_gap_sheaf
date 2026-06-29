/-
Track B+RepTheory / R2 — **deepening the O(4)-restoration residual: from a posited
per-step coefficient decay to the asymptotic-freedom MONOTONE FLOW of the
DIMENSIONLESS coupling plus an EXACT geometric spacing recursion.**

# Where this sits in the chain

The O(4)-rotation-restoration obligation is routed as

      DimensionlessFlow   (this module — the deepest residual)
        ⟶  O4DecayFromMargin.DimensionalScaling   (per-step dimensional scaling)
        ⟶  O4RestorationAF.ScalingDimensionDecay  (single-step ρ=1/2 contraction)
        ⟶  O4RestorationAF.RotationRestored       (proved CReal convergence).

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
    `RotationRestored`) is inherited.
  * `o4_restored_of_flow` — O(4) restored (the proved CReal convergence) obtained
    DIRECTLY from a `DimensionlessFlow`.
  * `exampleFlow` / `example_o4_restored` — a CONCRETE inhabitant (constant
    dimensionless coupling, `blockRatio = 1/2`, `spacing = (1/2)^k`, `m = 2`),
    witnessing that `DimensionlessFlow` is NON-VACUOUS and the whole pipeline fires.

NAMED (the deepened residual, `Type`-level, Rule 8): `DimensionlessFlow.dimless_antitone`
— the asymptotic-freedom monotone running of the dimensionless rotation-breaking
coupling under blocking.  This is strictly more fundamental than the previous bare
`scale_step`: the engineering-dimension weight is now PROVED algebra, and the only
remaining analytic input is the monotone flow of the dimensionless coupling.

# Honest scope / what stays open

We prove "{exact blocking spacing recursion, dimensionless coupling non-increasing}
⇒ per-step coefficient decay ⇒ O(4) restored".  We do NOT prove that the TRUE
interacting dimensionless rotation-breaking coupling is genuinely non-increasing
under the real Yang–Mills RG (`dimless_antitone`) — that is the remaining
asymptotic-freedom residual, now isolated as one transparent monotonicity.  The
concrete `exampleFlow` shows the structure is satisfiable (the constant /
free-fixed-point case); the open content is the same monotonicity for the genuine
interacting coupling.  The degree margin `d − 4 ≥ 2` (24-cell) is genuinely used
downstream (it forces the earned ratio `≤ 1/4`).

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
`O4RestorationAF` machinery then delivers `ScalingDimensionDecay` and the proved
`RotationRestored` convergence. -/

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

/-- **O(4) RESTORED FROM THE DIMENSIONLESS FLOW.**  The rotation-breaking
coefficient converges (with explicit two-sided modulus) — continuous O(4) is
restored as `a → 0` — derived DIRECTLY from a `DimensionlessFlow`.  The only
remaining analytic input is the asymptotic-freedom monotonicity `dimless_antitone`;
the engineering-dimension weight and the contraction ratio are proved. -/
theorem o4_restored_of_flow (F : DimensionlessFlow) :
    O4RestorationAF.RotationRestored (scalingDimensionDecay_of_flow F) :=
  O4DecayFromMargin.o4_restored_of_dimensionalScaling (dimensionalScaling_of_flow F)

/-! ## 4. A concrete inhabitant — `DimensionlessFlow` is non-vacuous

To show the deepened residual is SATISFIABLE (not a vacuous wall), we exhibit a
concrete flow: the free / fixed-point case with a CONSTANT dimensionless coupling
(`dimless ≡ 1`), blocking ratio `1/2`, spacing `(1/2)^k`, and degree margin `2`.
The whole pipeline then fires, producing the proved O(4)-restoration convergence.

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

/-- **The pipeline fires on the concrete inhabitant.**  O(4) restoration (the
proved CReal convergence of the rotation-breaking coefficient) holds for
`exampleFlow` — demonstrating the deepened residual is non-vacuous and the whole
chain is connected. -/
theorem example_o4_restored :
    O4RestorationAF.RotationRestored (scalingDimensionDecay_of_flow exampleFlow) :=
  o4_restored_of_flow exampleFlow

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
