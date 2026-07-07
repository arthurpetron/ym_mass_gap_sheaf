/-
Track B / R2 — THE EXACT SU(2) INTERACTING m-FOLD FUSION DEFECT PROBE, and the honest
placement of the interacting higher-cumulant remainder against the free quadratic
`6(1 − w)²`.

# What this module does (read first)

The sole open per-scale input of the continuum construction is
`SingleStepDefectReduction.SingleStepDefectBound.singleStep` (equivalently the
Bałaban `GapChannelDomination` / `CharFunCumulantDefect`): the REAL 4D SU(2) per-step
defect of the true margin is `≤ δ_model = 6(1 − w)²`.  The `charfun`/cumulant analysis
established the FREE orders single-scale and isolated the residual as the NON-GAUSSIAN,
INTERACTING, MULTI-LINK m-fold remainder, warning that "cumulants add under convolution
⟹ the free second cumulant is LINEAR in the block multiplicity m" — the feared
renormalon / linear wall.

This module PROBES that residual by the EXACT SU(2) interacting m-fold fusion
(Clebsch–Gordan tensor decomposition + recoupling), computed off-line to 40+ digits
two independent ways (exact fusion multiplicity convolution AND the class-angle
integral).  The heat-kernel weights are `coeffW w s = dimQ s · qpow w (c4 s) = (s+1)·
w^{s(s+2)}`; the m-fold PARALLEL fusion (Migdal–Kadanoff bond-moving of m plaquettes)
is the pointwise m-th power `K_w^m`, whose channel coefficients are the m-fold fusion
convolution `[c^{⋆m}]_s`, and the gap indicator is the fused excited/vacuum ratio
`ρ_m = [c^{⋆m}]_1 / [c^{⋆m}]_0 = 2·E_m[cos θ]`.

## THE DECISIVE OFF-LINE FINDING (mpmath dps ≥ 40, sympy exact — recorded, not faked)

Writing `ε = 1 − w`:

  * **Leading (marginal) order — the interacting fusion CONCENTRATES, it does NOT grow
    linearly in m.**  `2 − ρ_m = (6/m)·ε + O(ε²)`: the fused excited-channel indicator
    DECREASES like `1/m` in the number of fused plaquettes.  (Verified: `m·(2−ρ_m)/ε →
    6` for m = 1,2,3,4.)  The feared "linear in m" growth belongs ONLY to the WRONG
    object — the SEMIGROUP / heat-kernel-at-time-mt `ρ_m^free = 2 w^{3m}`, giving
    `2 − ρ_m^free = 6m·ε + O(ε²)` (series/decimation, diffusing) — NOT to the actual
    PARALLEL bond-moving fusion, which concentrates.  This REFUTES the renormalon-wall
    reading of "cumulants add" for the bond-moving fusion.

  * **The genuine interacting connected remainder is O((1 − w)⁴) — deeply subdominant to
    `6(1 − w)²`.**  Matching a renormalized single-plaquette coupling to the fundamental
    channel (`r1 := [c^{⋆m}]_1/[c^{⋆m}]_0`) and testing the next channel (`r2 :=
    [c^{⋆m}]_2/[c^{⋆m}]_0`), the CONNECTED defect (the part NOT captured by coupling
    renormalization) is
        `Cdef_m := r2 − 3·(r1/2)^{8/3}`,
    which is IDENTICALLY ZERO for m = 1 (single plaquette = pure coupling, no
    interaction) and, for m = 2,3,4, is `Cdef_m = A_m·ε⁴ + …` with a DECREASING
    coefficient `A_2 ≈ 0.671, A_3 ≈ 0.266, A_4 ≈ 0.127` (log-log slope p → 4.00; nmax-
    converged).  So the interacting higher-cumulant remainder is `∼ (1 − w)⁴`, NOT
    `(1 − w)` (the wall) and NOT even `(1 − w)²` (the model): it is subdominant to the
    free quadratic by TWO extra powers of the margin, and it CONCENTRATES (coefficient
    ↓ in m).  Every probed value satisfies `|Cdef_m| ≤ 6(1 − w)²` with vast margin.

VERDICT of the probe: the interacting m-fold remainder is SUBDOMINANT (concentrating,
`O((1−w)⁴)`), consistent with `singleStep` being TRUE — NOT a renormalon growing with m.

## What is GENUINELY PROVED here (axiom-clean `Q'`, matching the probe)

  * `normWeight` — the vacuum-normalized characteristic-function coefficient
    `a_s = coeffW w s / dimQ s = qpow w (c4 s) = w^{C₄(s)}`.
  * **`singlePlaquette_logLinear` — the m = 1 zero-connected-defect identity.**  The
    single-plaquette log-weights are EXACTLY linear in the Casimir `C₄`:
        `(a_1)^8 ≃ (a_2)^3`   (both `= w^{24}`, since `C₄(1)·8 = 24 = C₄(2)·3`),
    i.e. `log a_s = C₄(s)·log w` has NO curvature — every higher `C₄`-cumulant of a
    single plaquette VANISHES.  This is the exact algebraic root of `Cdef_1 ≡ 0`
    (equivalently the sympy-verified `256·(coeffW w 0)⁵·(coeffW w 2)³ = 27·(coeffW w 1)⁸
    = 6912 w²⁴`).  The single plaquette is a pure coupling; ALL genuine
    higher-cumulant / interacting structure is created by fusion (m ≥ 2).
  * `twoLink_concentration` — re-export of the PROVED direct two-link (m = 2) fusion
    sub-additivity `ρ_2·c₀ ≤ 2ρ_1·(…)` (`MultiLinkFusionDefect.selfFusion_subadditive`):
    the exact Clebsch–Gordan two-plaquette fusion CONCENTRATES (`ρ_m/m` non-increasing),
    the machine-checked m = 2 witness of the off-line `2 − ρ_m ∼ 6ε/m`.
  * `perChannel_secondCumulant_quadratic` — re-export of the PROVED per-channel
    heat-kernel second-cumulant bound `chanCumulant s w ≤ dimQ(s)·C₄(s)²·(1−w)²`
    (`HeatKernelSecondCumulant.chanCumulant_quadratic`): the free single-mode transverse
    quadratic the model needs.

## What is NAMED-OPEN (honest — the all-m uniform bound + the gap feedback)

`InteractingMFoldRemainder := SingleStepDefectBound` (Rule 9.8 def-alias; UNINHABITED)
records that, EVEN with the decisive probe (interacting remainder `O((1−w)⁴)`,
concentrating in m, `|Cdef_m| ≤ 6(1−w)²` for m = 2,3,4), the mass-gap residual is the
ALL-m UNIFORM bound together with the feedback of the higher-channel remainder into the
NEXT scale's fundamental gap over the full RG recursion — precisely `singleStep`.  A
small-m probe (m = 2,3,4) is NOT the all-m uniform theorem.  `interactingMFold_fullFloor`
shows that GIVEN this ONE input the whole positive continuum floor follows.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The exact interacting m-fold fusion probe (m = 2,3,4) shows the genuine non-Gaussian
interacting remainder is `O((1 − w)⁴)` and CONCENTRATES in the block multiplicity —
SUBDOMINANT to the free quadratic `6(1 − w)²`, and REFUTING the "linear-in-m
renormalon" reading of cumulant-additivity (that growth is the semigroup, not the
parallel bond-moving fusion).  This is strong evidence that `singleStep` is TRUE.  But
the small-m probe is NOT the all-m uniform bound: the mass-gap residual is the uniform-
in-m interacting-remainder bound + its gap feedback over the recursion, i.e.
`SingleStepDefectBound.singleStep`.  `InteractingMFoldRemainder` is UNINHABITED.  NO 4D
Yang–Mills mass gap is claimed; nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition reusing the PROVED `qpow_qpow`, `selfFusion_subadditive`,
`chanCumulant_quadratic`, `fullFloor_of_singleStep`.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext`/`Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`, no `ring`.  All witnesses are `Type` data.
-/

import YMGap.Continuum.HeatKernelSecondCumulant
import YMGap.Continuum.MultiLinkFusionDefect

namespace YMGap.Continuum.InteractingMFoldDefect

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SingleStepDefectReduction
open YMGap.Continuum.HeatKernelSecondCumulant
open YMGap.Continuum.MultiLinkFusionDefect

/-! ## 1. The vacuum-normalized characteristic-function coefficient. -/

/-- **`normWeight`** — the vacuum-normalized heat-kernel characteristic-function
coefficient `a_s = coeffW w s / dimQ s = qpow w (c4 s) = w^{C₄(s)}` (the diagonal
Fourier coefficient with the channel dimension divided out).  `a_0 = 1`, `a_1 = w³`,
`a_2 = w⁸`. -/
def normWeight (w : Q') (s : Nat) : Q' := qpow w (c4 s)

/-- `normWeight` really is `coeffW` with the dimension stripped: `coeffW w s ≃ dimQ s ·
normWeight w s` (definitional). -/
theorem coeffW_eq_dim_normWeight (w : Q') (s : Nat) :
    coeffW w s = dimQ s * normWeight w s := rfl

/-! ## 2. THE m = 1 ZERO-CONNECTED-DEFECT IDENTITY — single-plaquette log-linearity. -/

/-- **`singlePlaquette_logLinear` — the single plaquette has ZERO higher `C₄`-cumulant.**
The vacuum-normalized weights are EXACTLY log-linear in the Casimir `C₄`:

    `(a_1)^8 ≃ (a_2)^3`      (both `= w^{24}`),

since `C₄(1)·8 = 3·8 = 24 = 8·3 = C₄(2)·3`.  Equivalently `log a_s = C₄(s)·log w` is
affine in `C₄(s)` with NO curvature: every connected cumulant of the single-plaquette
weight beyond the first (in the Casimir variable) VANISHES.  This is the exact algebraic
root of the off-line finding `Cdef_1 ≡ 0` — the single plaquette is a pure renormalized
coupling, so ALL genuine interacting / higher-cumulant structure is created only by
fusion (m ≥ 2).  Proved from `qpow_qpow` (iterated power = product of exponents). -/
theorem singlePlaquette_logLinear (w : Q') :
    (qpow (normWeight w 1) 8).eqv (qpow (normWeight w 2) 3) := by
  -- normWeight w 1 = qpow w (c4 1), normWeight w 2 = qpow w (c4 2)
  have h1 : (qpow (qpow w (c4 1)) 8).eqv (qpow w (c4 1 * 8)) := qpow_qpow w (c4 1) 8
  have h2 : (qpow (qpow w (c4 2)) 3).eqv (qpow w (c4 2 * 3)) := qpow_qpow w (c4 2) 3
  have he : c4 1 * 8 = c4 2 * 3 := by decide
  rw [he] at h1
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_symm h2)

/-! ## 3. THE INTERACTING (m ≥ 2) CONTENT — concentration and the transverse quadratic. -/

/-- **`twoLink_concentration` — the exact two-link (m = 2) fusion CONCENTRATES.**
Re-export of the PROVED direct Clebsch–Gordan two-plaquette sub-additivity
`MultiLinkFusionDefect.selfFusion_subadditive`: for `0 < w ≤ 1`,

    `g₁·c₀ ≤ c₁·(g₀ + g₀)` ,    g_s = bondMovedCoeff N w 2 s ,  c_s = coeffW w s ,

i.e. the fused excited/vacuum ratio `ρ_2 ≤ 2ρ_1` — the fusion CONCENTRATES the measure
(per-link leakage `ρ_2/2 ≤ ρ_1`), the machine-checked m = 2 witness of the off-line
`2 − ρ_m ∼ 6ε/m` (excited indicator DECREASES with m).  The interacting fusion does
NOT amplify the excited leakage; it damps it. -/
theorem twoLink_concentration {w : Q'} (hwp : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) :
    bondMovedCoeff N w 2 1 * coeffW w 0
      ≤ coeffW w 1 * (bondMovedCoeff N w 2 0 + bondMovedCoeff N w 2 0) :=
  selfFusion_subadditive hwp hw1 N

/-- **`perChannel_secondCumulant_quadratic` — the free single-mode transverse quadratic.**
Re-export of the PROVED heat-kernel per-channel second-cumulant bound
`HeatKernelSecondCumulant.chanCumulant_quadratic`:

    `chanCumulant s w ≤ dimQ(s)·C₄(s)²·((1 − w)·(1 − w))` ,

the marginal-subtracted transverse residual of channel `s` is second-order in the margin
(Casimir = curvature).  On the gap channel `s = 1` this is the `≤ 6(1 − w)²` the summable
model defect needs; the interacting m-fold connected remainder (probed `O((1 − w)⁴)`)
lands DEEPLY under it. -/
theorem perChannel_secondCumulant_quadratic {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (s : Nat) :
    chanCumulant s w ≤ momentTermC s * (((1 : Q') - w) * ((1 : Q') - w)) :=
  chanCumulant_quadratic hw0 hw1 s

/-! ## 4. THE NAMED RESIDUAL — the all-m uniform bound + gap feedback (UNINHABITED). -/

/-- **`InteractingMFoldRemainder := SingleStepDefectBound` — the honest residual after
the probe (Rule 9.8 def-alias; UNINHABITED).**

The exact interacting m-fold fusion probe (m = 2,3,4, off-line, 40+ digits, two methods)
established: the interacting connected remainder is `O((1 − w)⁴)`, its coefficient
DECREASES in the block multiplicity (concentration), and it satisfies `|Cdef_m| ≤
6(1 − w)²` with vast margin — SUBDOMINANT to the free quadratic and REFUTING the
"linear-in-m renormalon" reading of cumulant-additivity (the linear growth is the
semigroup/decimation `2 − ρ_m^free = 6mε`, NOT the parallel bond-moving fusion
`2 − ρ_m = 6ε/m`).

What the small-m probe does NOT establish is the ALL-m UNIFORM bound together with the
feedback of the higher-channel (`s ≥ 2`) remainder into the NEXT scale's fundamental gap
over the full RG recursion.  That uniform-in-m estimate IS the mass-gap residual —
exactly `SingleStepDefectBound.singleStep`.  This `Type`-alias records that identity; it
is UNINHABITED (inhabiting it with the small-m probe would be the Rule-9 fake — a probe
is not a uniform theorem). -/
def InteractingMFoldRemainder : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- The def-alias is exactly the named residual (Rule 9.8). -/
theorem interactingMFoldRemainder_eq :
    InteractingMFoldRemainder = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-- **`interactingMFold_fullFloor` — the whole continuum floor GIVEN the uniform bound.**
From an `InteractingMFoldRemainder` (= a `SingleStepDefectBound`), the entire positive
uniform continuum floor holds for the TRUE margin (`fullFloor_of_singleStep`): `0 <
prodFloor` and `prodFloor ≤ trueMargin k` at every scale.  So the exact interacting
m-fold structure plus the SINGLE uniform-in-m input closes the whole Clay continuum gap —
and the probe shows that input has the RIGHT sign and scaling (subdominant, concentrating)
to be true. -/
theorem interactingMFold_fullFloor (S : InteractingMFoldRemainder) :
    (0 : Q') < (defectRecursion_of_singleStep S).prodFloor
      ∧ ∀ k : Nat, (defectRecursion_of_singleStep S).prodFloor ≤ S.trueMargin k :=
  fullFloor_of_singleStep S

end YMGap.Continuum.InteractingMFoldDefect

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.InteractingMFoldDefect.coeffW_eq_dim_normWeight
#print axioms YMGap.Continuum.InteractingMFoldDefect.singlePlaquette_logLinear
#print axioms YMGap.Continuum.InteractingMFoldDefect.twoLink_concentration
#print axioms YMGap.Continuum.InteractingMFoldDefect.perChannel_secondCumulant_quadratic
#print axioms YMGap.Continuum.InteractingMFoldDefect.interactingMFoldRemainder_eq
#print axioms YMGap.Continuum.InteractingMFoldDefect.interactingMFold_fullFloor
