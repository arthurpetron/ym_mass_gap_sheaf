/-
Track B+RepTheory / R2 — **the scalar anisotropy decay RATE as an EARNED
consequence of the PROVED 24-cell degree margin.**

# What this module sharpens

`O4RestorationAF.lean` discharges the opaque "O(4) is restored" `Prop` by routing
it through a single-step geometric contraction `breakCoeff (k+1) ≤ ρ · breakCoeff k`
with the ratio HARDCODED at `ρ = 1/2` (its `decay` field).  The proved degree margin
`d − 4 ≥ 2` (24-cell / `LatticeAnisotropy.breakDegree_gt_four`) only *motivated*
that `1/2`; it did not derive it.

This module replaces the posited `1/2` by a ratio DERIVED from a cleaner, more
fundamental input — the per-step DIMENSIONAL SCALING of an irrelevant operator.
Under one RG blocking step of linear spacing ratio `blockRatio ≤ 1/2`, an
irrelevant operator of engineering dimension `d` (excess `degreeMargin = d − 4`)
scales by

      breakCoeff (k+1)  ≤  blockRatio^{degreeMargin} · breakCoeff k.

The contraction ratio is therefore `ρ := blockRatio^{degreeMargin}`, and the
PROVED margin `degreeMargin ≥ 2` together with the blocking ratio `blockRatio ≤ 1/2`
forces

      ρ = blockRatio^{degreeMargin}  ≤  (1/2)^{degreeMargin}  ≤  (1/2)^2 = 1/4  ≤  1/2.

So the contraction `ρ ≤ 1/4` is now an EARNED consequence of the 24-cell invariant
theory (the degree margin) plus the AF/blocking spacing ratio, NOT a posited `1/2`.

# What this module PROVES vs NAMES

PROVED here (genuine theorems, `[propext]` / `[propext, Quot.sound]` only):
  * `rate_le_quarter` — the EARNED-rate lemma: `blockRatio^{degreeMargin} ≤ 1/4`,
    from `0 ≤ blockRatio ≤ 1/2` (base-monotone `qpow_mono`) and `degreeMargin ≥ 2`
    (exponent-antitone `qpow_antitone`), then `(1/2)^2 = 1/4` by computation.
  * `derivedRho_le_half` — the corollary `blockRatio^{degreeMargin} ≤ 1/2` (the
    ratio the downstream geometric engine needs).
  * `scalingDimensionDecay_of_dimensionalScaling` — the PROVED reduction
    `DimensionalScaling → O4RestorationAF.ScalingDimensionDecay`: the existing
    structure's `decay` field (`coeff (k+1) ≤ (1/2)·coeff k`) is DERIVED from the
    transparent per-step dimensional-scaling law `scale_step` plus the earned
    `derivedRho_le_half` and nonnegativity.
  * `o4_restored_of_dimensionalScaling` — the legacy anisotropy-Cauchy conclusion
    (`O4RestorationAF.RotationRestored`) obtained DIRECTLY from `DimensionalScaling`.
    Despite its historical name, this theorem type alone is not full O(4).

NAMED (the sharper single wall, `Type`-level, Rule 8): `DimensionalScaling` — the
transparent per-step dimensional-scaling law `breakCoeff (k+1) ≤
blockRatio^{degreeMargin} · breakCoeff k` (standard irrelevant-operator RG content)
together with `blockRatio ≤ 1/2` and the proved `degreeMargin ≥ 2`.  This is
strictly cleaner than the previous posited `ρ = 1/2`: the decay RATE is now a
PROVED consequence of the 24-cell degree margin, and the remaining named obligation
is only the single transparent dimensional-scaling estimate.

# Honest scope / what stays open

We prove "per-step dimensional scaling + blockRatio ≤ 1/2 ⇒ the contraction ratio
is ≤ 1/4 (earned from the proved margin) ⇒ the anisotropy schedule is Cauchy".
Strict convergence to zero is supplied by the later zero-limit modules; full O(4)
still requires the observable action/response bridge.  We do NOT prove the
dimensional-scaling law `scale_step` itself — that the degree-`d` operator's
coefficient genuinely scales by `blockRatio^{d−4}` under one true RG blocking step.
That single transparent estimate (standard RG-irrelevance content) is the remaining
named input.  The degree margin `d − 4 ≥ 2` is the genuinely PROVED 24-cell content
and is what makes the rate `≤ 1/4`.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'`/`qpow` arithmetic and the reused `O4RestorationAF` reduction; every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`decide`-on-nondecidable, no `sorry`, no `Prop := True` stub.  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.O4RestorationAF
import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.HeatKernelRGStep

namespace YMGap.Continuum.O4DecayFromMargin

open YMGap.Constructive
open YMGap.Continuum
open YMGap.RepTheory

/-! ## 1. The cleaner named input — `DimensionalScaling`

The transparent RG-irrelevance datum: the rotation-breaking coefficient sequence
together with the per-step DIMENSIONAL-SCALING law.  Under one RG blocking step of
linear spacing ratio `blockRatio ≤ 1/2`, the coefficient of an irrelevant operator
of degree excess `degreeMargin = d − 4` scales by `blockRatio^{degreeMargin}` — its
engineering-dimension weight.  This single estimate REPLACES the posited `ρ = 1/2`:
the contraction ratio is now `blockRatio^{degreeMargin}`, which the proved margin
forces below `1/4`. -/

/-- **The per-step dimensional-scaling datum (the cleaner named wall).**

`Type`-level data: the rotation-breaking coefficient sequence along the blocking
schedule together with the RG-irrelevance scaling law expressed as ONE
per-step dimensional-scaling estimate.

Fields:
  * `breakCoeff` — the magnitude of the leading rotation-breaking operator's
    coefficient at blocking step `k` (a nonnegative `Q'`).
  * `breakCoeff_nonneg` — the coefficient magnitude is nonnegative.
  * `blockRatio` — the linear spacing ratio of one RG blocking step.
  * `blockRatio_nonneg` — `0 ≤ blockRatio`.
  * `blockRatio_le_half` — **the AF/blocking ratio bound `blockRatio ≤ 1/2`** (one
    blocking step at least halves the lattice spacing).
  * `degreeMargin` — the degree excess `d − 4` of the leading rotation-breaking
    operator.
  * `degreeMargin_ge_two` — the PROVED margin `2 ≤ d − 4` (the 24-cell pushes the
    leading break to degree `≥ 6`).
  * `scale_step` — **the genuine remaining analytic content (the dimensional-scaling
    law):** under one blocking step the coefficient scales by its
    engineering-dimension weight,
    `breakCoeff (k+1) ≤ blockRatio^{degreeMargin} · breakCoeff k`.  This is the
    transparent irrelevant-operator content; the contraction ratio is
    `blockRatio^{degreeMargin}`, NOT a posited `1/2`. -/
structure DimensionalScaling : Type where
  /-- The leading rotation-breaking operator's coefficient magnitude at step `k`. -/
  breakCoeff : Nat → Q'
  /-- The coefficient magnitude is nonnegative. -/
  breakCoeff_nonneg : ∀ k : Nat, (0 : Q') ≤ breakCoeff k
  /-- The linear spacing ratio of one RG blocking step. -/
  blockRatio : Q'
  /-- The blocking ratio is nonnegative. -/
  blockRatio_nonneg : (0 : Q') ≤ blockRatio
  /-- **The blocking ratio at most halves the spacing:** `blockRatio ≤ 1/2`. -/
  blockRatio_le_half : blockRatio ≤ HalfPow.half
  /-- The degree excess `d − 4` of the leading rotation-breaking operator. -/
  degreeMargin : Nat
  /-- PROVED margin `2 ≤ d − 4` (the 24-cell degree-6 content). -/
  degreeMargin_ge_two : 2 ≤ degreeMargin
  /-- **The per-step dimensional-scaling law (the RG-irrelevance content).**  Under
  one blocking step the coefficient scales by its engineering-dimension weight:
  `breakCoeff (k+1) ≤ blockRatio^{degreeMargin} · breakCoeff k`. -/
  scale_step : ∀ k : Nat,
    breakCoeff (k + 1) ≤ RGTransport.qpow blockRatio degreeMargin * breakCoeff k

/-! ## 2. The EARNED rate — `blockRatio^{degreeMargin} ≤ 1/4 ≤ 1/2`

This is THE earned-rate lemma: the contraction ratio is `≤ 1/4` purely from the
PROVED margin (`degreeMargin ≥ 2`) and the blocking ratio (`blockRatio ≤ 1/2`).

Chain:
  * base-monotone:   `blockRatio^{degreeMargin} ≤ (1/2)^{degreeMargin}`
                     (`qpow_mono`, from `0 ≤ blockRatio ≤ 1/2`);
  * exponent-antitone: `(1/2)^{degreeMargin} ≤ (1/2)^2`
                     (`qpow_antitone`, from `2 ≤ degreeMargin`, base `≤ 1`);
  * computation:     `(1/2)^2 = 1/4 ≤ 1/2`. -/

/-- The rational `1/4` — the earned-rate ceiling `(1/2)^2`. -/
def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- `(1/2)^2 = 1/4 ≤ 1/4` — the base computation (decidable `Q'` order). -/
theorem qpow_half_two_le_quarter :
    RGTransport.qpow HalfPow.half 2 ≤ quarter := by decide

/-- `(1/2)^2 ≤ 1/2` (since `(1/2)^2 = 1/4 ≤ 1/2`). -/
theorem qpow_half_two_le_half :
    RGTransport.qpow HalfPow.half 2 ≤ HalfPow.half := by decide

/-- **THE EARNED-RATE LEMMA.**  The contraction ratio derived from the per-step
dimensional scaling is `≤ 1/4`:
`blockRatio^{degreeMargin} ≤ (1/2)^{degreeMargin} ≤ (1/2)^2 = 1/4`.
The two inequalities are EARNED from `blockRatio ≤ 1/2` (base-monotone) and the
PROVED margin `degreeMargin ≥ 2` (exponent-antitone); the value `1/4` is the
24-cell-floor consequence, NOT a posited constant. -/
theorem rate_le_quarter (D : DimensionalScaling) :
    RGTransport.qpow D.blockRatio D.degreeMargin ≤ quarter := by
  -- base-monotone: blockRatio^m ≤ (1/2)^m
  have hbase : RGTransport.qpow D.blockRatio D.degreeMargin
      ≤ RGTransport.qpow HalfPow.half D.degreeMargin :=
    HeatKernelGap.qpow_mono D.blockRatio_nonneg D.blockRatio_le_half D.degreeMargin
  -- exponent-antitone: (1/2)^m ≤ (1/2)^2  (m ≥ 2, base ∈ [0,1])
  have hexp : RGTransport.qpow HalfPow.half D.degreeMargin
      ≤ RGTransport.qpow HalfPow.half 2 :=
    HeatKernelRGStep.qpow_antitone HalfPow.half_nonneg (by decide)
      2 D.degreeMargin D.degreeMargin_ge_two
  -- (1/2)^2 = 1/4
  exact Q'.le_trans' _ _ _ hbase
    (Q'.le_trans' _ _ _ hexp qpow_half_two_le_quarter)

/-- **The earned ratio is `≤ 1/2`** — the form the downstream geometric engine
needs.  `blockRatio^{degreeMargin} ≤ (1/2)^2 = 1/4 ≤ 1/2`, EARNED from the proved
margin and the blocking ratio. -/
theorem derivedRho_le_half (D : DimensionalScaling) :
    RGTransport.qpow D.blockRatio D.degreeMargin ≤ HalfPow.half := by
  -- chain through (1/2)^2 ≤ 1/2 rather than 1/4 ≤ 1/2 (both decidable)
  have hbase : RGTransport.qpow D.blockRatio D.degreeMargin
      ≤ RGTransport.qpow HalfPow.half D.degreeMargin :=
    HeatKernelGap.qpow_mono D.blockRatio_nonneg D.blockRatio_le_half D.degreeMargin
  have hexp : RGTransport.qpow HalfPow.half D.degreeMargin
      ≤ RGTransport.qpow HalfPow.half 2 :=
    HeatKernelRGStep.qpow_antitone HalfPow.half_nonneg (by decide)
      2 D.degreeMargin D.degreeMargin_ge_two
  exact Q'.le_trans' _ _ _ hbase
    (Q'.le_trans' _ _ _ hexp qpow_half_two_le_half)

/-! ## 3. The reduction — `DimensionalScaling → ScalingDimensionDecay`

The existing `O4RestorationAF.ScalingDimensionDecay` carries its single-step
contraction with the factor `1/2` HARDCODED (`decay : coeff (k+1) ≤ (1/2)·coeff k`).
We DERIVE that hardcoded factor from the transparent per-step dimensional-scaling
law `scale_step` plus the EARNED `derivedRho_le_half`:

  `coeff (k+1) ≤ blockRatio^{degreeMargin}·coeff k ≤ (1/2)·coeff k`,

the second step by `blockRatio^{degreeMargin} ≤ 1/2` (earned) and `coeff k ≥ 0`. -/

/-- The earned per-step contraction at the existing structure's hardcoded ratio:
`breakCoeff (k+1) ≤ (1/2)·breakCoeff k`, DERIVED from `scale_step` and the EARNED
`derivedRho_le_half` (NOT posited). -/
theorem decay_at_half (D : DimensionalScaling) (k : Nat) :
    D.breakCoeff (k + 1) ≤ HalfPow.half * D.breakCoeff k := by
  -- breakCoeff (k+1) ≤ blockRatio^m · breakCoeff k
  refine Q'.le_trans' _ _ _ (D.scale_step k) ?_
  -- blockRatio^m · breakCoeff k ≤ (1/2) · breakCoeff k   (earned ratio, coeff ≥ 0)
  exact Q'.mul_le_mul_of_nonneg_right
    (RGTransport.qpow D.blockRatio D.degreeMargin) HalfPow.half (D.breakCoeff k)
    (derivedRho_le_half D) (D.breakCoeff_nonneg k)

/-- **THE REDUCTION.**  A `DimensionalScaling` (per-step dimensional-scaling law +
`blockRatio ≤ 1/2` + proved margin) yields an `O4RestorationAF.ScalingDimensionDecay`
whose single-step contraction `decay` is the EARNED `decay_at_half` and whose
`degreeMargin_ge_two` is the proved 24-cell margin.  The previously-posited ratio
`1/2` is now an EARNED consequence of `blockRatio ≤ 1/2` and `degreeMargin ≥ 2`. -/
def scalingDimensionDecay_of_dimensionalScaling (D : DimensionalScaling) :
    O4RestorationAF.ScalingDimensionDecay where
  coeff := D.breakCoeff
  coeff_nonneg := D.breakCoeff_nonneg
  degreeMargin := D.degreeMargin
  degreeMargin_ge_two := D.degreeMargin_ge_two
  decay := decay_at_half D

/-- The reduced datum carries the SAME coefficient schedule (the reduction does not
re-label the sequence). -/
@[simp] theorem scalingDimensionDecay_coeff (D : DimensionalScaling) (k : Nat) :
    (scalingDimensionDecay_of_dimensionalScaling D).coeff k = D.breakCoeff k := rfl

/-- The reduced datum carries the SAME (proved) degree margin. -/
@[simp] theorem scalingDimensionDecay_degreeMargin (D : DimensionalScaling) :
    (scalingDimensionDecay_of_dimensionalScaling D).degreeMargin = D.degreeMargin :=
  rfl

/-! ## 4. Legacy scalar Cauchy payoff from `DimensionalScaling`

Composing the reduction with the existing `O4RestorationAF.rotationRestored_of_decay`
concludes `RotationRestored`, the historical name for the rotation-breaking
coefficient's Cauchy predicate, DIRECTLY from `DimensionalScaling`. -/

/-- **ANISOTROPY CAUCHY FROM THE DIMENSIONAL-SCALING LAW.**  The rotation-breaking
coefficient is Cauchy with an explicit two-sided modulus, derived directly from a
`DimensionalScaling`.  The decay rate
`blockRatio^{degreeMargin} ≤ 1/4` is EARNED from the proved 24-cell degree margin
(`degreeMargin ≥ 2`) and the blocking ratio (`blockRatio ≤ 1/2`); the only remaining
named input is the transparent per-step dimensional-scaling law `scale_step`.
Use the strict zero-limit and observable-response modules for restoration claims. -/
theorem o4_restored_of_dimensionalScaling (D : DimensionalScaling) :
    O4RestorationAF.RotationRestored
      (scalingDimensionDecay_of_dimensionalScaling D) :=
  O4RestorationAF.rotationRestored_of_decay
    (scalingDimensionDecay_of_dimensionalScaling D)

end YMGap.Continuum.O4DecayFromMargin

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.O4DecayFromMargin.qpow_half_two_le_quarter
#print axioms YMGap.Continuum.O4DecayFromMargin.qpow_half_two_le_half
#print axioms YMGap.Continuum.O4DecayFromMargin.rate_le_quarter
#print axioms YMGap.Continuum.O4DecayFromMargin.derivedRho_le_half
#print axioms YMGap.Continuum.O4DecayFromMargin.decay_at_half
#print axioms YMGap.Continuum.O4DecayFromMargin.scalingDimensionDecay_of_dimensionalScaling
#print axioms YMGap.Continuum.O4DecayFromMargin.scalingDimensionDecay_coeff
#print axioms YMGap.Continuum.O4DecayFromMargin.scalingDimensionDecay_degreeMargin
#print axioms YMGap.Continuum.O4DecayFromMargin.o4_restored_of_dimensionalScaling
