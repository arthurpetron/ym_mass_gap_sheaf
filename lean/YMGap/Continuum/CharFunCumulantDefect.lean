/-
Track B / R1 — THE CHARACTERISTIC-FUNCTION / CUMULANT ATTACK on the single-scale
per-scale block-spin defect bound `realδ_k ≤ δ_model_k = 6(1 − w_k)²`.

# What this module does (read first)

The SU(2) single-plaquette heat-kernel weight is the diagonal character coefficient
`coeffW w s = dim(s)·w^{C₄(s)}` (`= dimQ s · qpow w (c4 s)`, exactly the Fourier /
characteristic-function coefficient of the class function `K_t(θ) = Σ_s dim(s) χ_s(θ)
e^{−t C₄(s)}` with `w = e^{−t}`).  The `m`-fold fusion (block-spin convolution) is the
PRODUCT of these characteristic functions — the normalized coefficient `a_s = w^{C₄(s)}`
goes to `a_s^m = w^{m C₄(s)}` (the semigroup / heat kernel at `w^m`), so cumulants ADD
under convolution.  This module records what the characteristic-function / cumulant
expansion PROVES single-scale, and isolates EXACTLY what it does NOT.

## What the characteristic-function / cumulant expansion GIVES single-scale (PROVED)

The per-step degradation of the transfer gap splits, on the dominant `s = 1` mode, into
the three cumulant orders (`SingleStepDefectReduction` §Task 2):

  * **(A) FREE / zeroth: scale-EXACT.**  At the Gaussian fixed point `w = 1` the
    renormalized defect is `0` — `charFun_freeEnd_zero` (from `≤ 0` and `≥ 0`).  The free
    heat-kernel semigroup contributes ZERO defect: convolution of Gaussians is exact.

  * **(B) MARGINAL / first cumulant: LINEAR, absorbed by the counterterm.**  The marginal
    part is the running-coupling drift `1 − renormW p w ≃ C₄(1)·(1 − w)` — LINEAR in the
    margin `(1 − w)` (`charFun_marginal_linear`, re-exporting `renormW_margin`).  This is
    the FIRST-cumulant / drift term; it is SUBTRACTED exactly by the retuning counterterm
    `renormW`, not an error.  Under `m`-fold convolution the first cumulant scales like
    `m·(1 − w)` — LINEAR in the block multiplicity `m`; the counterterm removes it.

  * **(C) TRANSVERSE / second-and-higher cumulant: QUADRATIC.**  After the linear marginal
    is cancelled, the residual model defect is the QUADRATIC overshoot
    `δ_ren(2,p,w) = 2p·(1 − w)²·(w + 2) ≤ 6p·(1 − w)²` (`charFun_transverse_quadratic`,
    re-exporting `bondMovingDeltaRen_le_sixp`).  This is the free single-mode transverse
    part — the sharp `(1 − w)²` scaling the summable model defect needs.

The exact decomposition `trueDev = counterterm − transverse`
(`charFun_defect_decomposition`, re-exporting `trueDev_eq_counterterm_sub_transverse`)
exhibits all three orders in one identity.

## What it does NOT give single-scale (the honest isolation) — THE MASS GAP INPUT

The characteristic-function / cumulant expansion controls the FREE heat kernel: the
first cumulant (marginal, linear, counterterm-cancelled) and the free single-mode second
cumulant (transverse, quadratic).  But the REAL per-scale defect `realδ_k` is the FULL
non-abelian, MULTI-LINK, INTERACTING remainder of the true dimensionless margin — NOT the
free single-mode quantity.  Two facts make this decisive:

  1. **Cumulants add under convolution ⟹ the FREE second cumulant is LINEAR in the block
     multiplicity `m`, not quadratic.**  `a_s^m = w^{m C₄(s)}`: the `m`-fold fusion second
     cumulant is `m·κ₂(single) ~ m·(1 − w)`.  A pure-second-cumulant defect is therefore
     LINEAR (`~ m(1 − w)`) — this is the "prefactor LINEAR" wall.  The QUADRATIC `(1 − w)²`
     bound is reached ONLY because the counterterm cancels the linear marginal AND the
     interacting remainder stays under the free quadratic.

  2. **The quadratic bound `realδ_k ≤ δ_model_k` requires the NON-GAUSSIAN interacting
     m-fold remainder to not exceed the free transverse quadratic.**  That remainder is a
     higher-cumulant / genuinely-interacting object, NOT determined by the free heat
     kernel's second cumulant.  It is exactly `SingleStepDefectBound.singleStep`.

`CharFunCumulantDefect := SingleStepDefectReduction.SingleStepDefectBound` records this
identity (Rule 9.8, proof not prose): the char-function/cumulant structure supplies the
free (A)/(B)/(C) orders SINGLE-SCALE, and the residual real-defect bound is precisely the
non-Gaussian interacting input `singleStep` — UNINHABITED.  `charFunCumulant_fullFloor`
shows that GIVEN this ONE non-Gaussian input the whole positive continuum floor follows.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The per-scale defect bound `realδ_k ≤ 6(1 − w_k)²` is **NOT provable single-scale from the
characteristic-function / cumulant expansion alone.**  The cumulants give the FREE
structure — the free part is scale-exact (A), the marginal first cumulant is linear and
counterterm-cancelled (B), and the free single-mode second cumulant is the quadratic model
defect (C) — all PROVED single-scale here.  But the free second cumulant is LINEAR in the
block multiplicity; the QUADRATIC defect bound on the TRUE margin needs the NON-GAUSSIAN
interacting m-fold remainder to stay under the free quadratic — which is exactly the
interacting-measure input `singleStep`, NOT a free-cumulant quantity.  So the defect bound
is IRREDUCIBLY the `singleStep` input.  `CharFunCumulantDefect` is UNINHABITED; NO 4D
Yang–Mills mass gap is claimed; nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` re-export and composition of PROVED lemmas (`renormW_margin`,
`bondMovingDeltaRen_le_sixp`, `trueDev_eq_counterterm_sub_transverse`,
`freeEnd_defect_scaleExact`, `fullFloor_of_singleStep`).  The one new fact
`charFun_freeEnd_zero` is `Int.le_antisymm` on the `≤`-both-ways of the free-end defect
(the same rational-antisymmetry core as `cubeRoot_unique_rat`).  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext`/`Quot.sound` only.
No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.CharFunCumulantDefect

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 1. The characteristic function (heat-kernel weight) and its cumulant orders. -/

/-- **The characteristic-function coefficient** — the SU(2) single-plaquette heat-kernel
weight is the diagonal character coefficient `coeffW w s = dim(s)·w^{C₄(s)}`, exactly the
Fourier coefficient of the class function `K_t(θ) = Σ_s dim(s) χ_s(θ) e^{−t C₄(s)}` at
`w = e^{−t}`.  Vacuum-normalized (`coeffW w 0 = 1`); the first-excited coefficient is the
separator `coeffW w 1 = 2·w³`.  (Re-export of `BondMovingStep.coeffW`, the anchor object
of this attack.) -/
theorem charFun_normalization (w : Q') :
    coeffW w 0 = 1 ∧ coeffW w 1 = dimQ 1 * HeatKernelGap.heatKernelSep w :=
  ⟨coeffW_zero w, coeffW_one w⟩

/-! ### (A) FREE / zeroth cumulant — scale-EXACT (zero defect at the Gaussian end). -/

/-- **(A) `charFun_freeEnd_zero` — the free heat-kernel semigroup contributes ZERO
defect.**  At the Gaussian fixed point `w = 1` the renormalized per-step defect is exactly
`0`: from `freeEnd_defect_scaleExact` (`≤ 0`) and `freeEnd_defect_nonneg` (`≥ 0`) by
rational antisymmetry (`Int.le_antisymm` on the cross-multiplied numerators, the same core
as `cubeRoot_unique_rat`).  Convolution of Gaussians is exact — the free UV step erodes
nothing; this is the zeroth-order (scale-exactness) statement of the cumulant expansion. -/
theorem charFun_freeEnd_zero (N p : Nat) :
    (bondMovingDeltaRen N p 1).eqv 0 := by
  show (bondMovingDeltaRen N p 1).num * ((0 : Q').den : Int)
      = (0 : Q').num * ((bondMovingDeltaRen N p 1).den : Int)
  exact Int.le_antisymm
    (SingleStepDefectReduction.freeEnd_defect_scaleExact N p)
    (SingleStepDefectReduction.freeEnd_defect_nonneg N p)

/-! ### (B) MARGINAL / first cumulant — LINEAR, absorbed by the counterterm. -/

/-- **(B) `charFun_marginal_linear` — the first-cumulant marginal drift is LINEAR.**  The
marginal part of the step is the running-coupling drift `1 − renormW p w ≃ C₄(1)·(1 − w)`,
LINEAR in the margin `(1 − w)`.  This is the FIRST cumulant (the drift of the heat-kernel
time under bond-moving); it is SUBTRACTED exactly by the retuning counterterm `renormW`.
Under `m`-fold convolution it scales like `m·(1 − w)` — LINEAR in the block multiplicity;
the counterterm removes it, leaving only (C).  (Re-export of `renormW_margin`.) -/
theorem charFun_marginal_linear (p : Nat) (w : Q') :
    ((1 : Q') - renormW p w).eqv (Q'.ofNat (c4 1) * ((1 : Q') - w)) :=
  renormW_margin p w

/-! ### (C) TRANSVERSE / second cumulant — QUADRATIC (the summable model defect). -/

/-- **(C) `charFun_transverse_quadratic` — the residual model defect is QUADRATIC.**  After
the linear marginal is cancelled by the counterterm, the residual defect on the dominant
mode is the quadratic overshoot `δ_ren(N,p,w) ≤ 6p·(1 − w)²` — the sharp `(1 − w)²` scaling
the summable model defect needs (`Σ 1/k² < ∞`).  This is the FREE single-mode transverse
(second-cumulant) part.  (Re-export of `bondMovingDeltaRen_le_sixp`.) -/
theorem charFun_transverse_quadratic {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N p : Nat) :
    bondMovingDeltaRen N p w
      ≤ Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)))) :=
  bondMovingDeltaRen_le_sixp hw0 hw1 N p

/-- **The one-identity cumulant decomposition** `trueDev = counterterm − transverse`:

    dimQ 1·(1 − w³)  ≃  dimQ 1·(1 − renormW p w)  −  δ_ren(N,1,w) ,

exhibiting all three cumulant orders at once — the true first-excited deviation is the
[marginal counterterm (B), linear] minus the [transverse residual (C), quadratic], with
the free part (A) scale-exact.  (Re-export of `trueDev_eq_counterterm_sub_transverse`.) -/
theorem charFun_defect_decomposition (N p : Nat) (w : Q') :
    (dimQ 1 * ((1 : Q') - qpow w (c4 1))).eqv
      ((dimQ 1 * ((1 : Q') - renormW p w)) - bondMovingDeltaRen N 1 w) :=
  trueDev_eq_counterterm_sub_transverse N p w

/-! ## 2. THE HONEST ISOLATION — the residual is the NON-GAUSSIAN interacting input.

The characteristic-function / cumulant expansion supplies (A)/(B)/(C) SINGLE-SCALE — all
proved above.  What it does NOT supply is the bound of the REAL non-abelian multi-link
INTERACTING remainder by the free transverse quadratic: `realδ_k ≤ δ_model_k`.  Because
cumulants add under convolution, the free second cumulant is LINEAR in the block
multiplicity `m`; the quadratic bound on the TRUE margin needs the non-Gaussian m-fold
remainder to stay under the free quadratic — the interacting-measure input `singleStep`. -/

/-- **`CharFunCumulantDefect := SingleStepDefectBound` — the residual is exactly the
non-Gaussian interacting input (Rule 9.8, proof not prose; UNINHABITED).**  The
char-function/cumulant structure gives the free orders (A)/(B)/(C) single-scale (the four
theorems above); the remaining content — the real interacting per-step defect bounded by
the free transverse quadratic — is precisely `SingleStepDefectBound.singleStep`, NOT a
free-cumulant quantity.  This `Type`-alias records that identity; it is UNINHABITED (it IS
the real RG estimate).  Inhabiting it with an ASSUMED bound would be the Rule-9 fake —
deliberately not written. -/
def CharFunCumulantDefect : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- The def-alias is exactly the named residual (Rule 9.8). -/
theorem charFunCumulantDefect_eq :
    CharFunCumulantDefect = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-- **`charFunCumulant_fullFloor` — the whole continuum floor GIVEN the one non-Gaussian
input.**  From a `CharFunCumulantDefect` (= a `SingleStepDefectBound`), the entire positive
uniform continuum floor holds for the TRUE margin (`fullFloor_of_singleStep`): `0 <
prodFloor` and `prodFloor ≤ trueMargin k` at every scale.  So the char-function/cumulant
free structure plus the SINGLE non-Gaussian interacting input `singleStep` closes the whole
Clay continuum gap — and that input is exactly what the cumulants do NOT provide. -/
theorem charFunCumulant_fullFloor (S : CharFunCumulantDefect) :
    (0 : Q') < (defectRecursion_of_singleStep S).prodFloor
      ∧ ∀ k : Nat, (defectRecursion_of_singleStep S).prodFloor ≤ S.trueMargin k :=
  fullFloor_of_singleStep S

end YMGap.Continuum.CharFunCumulantDefect

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CharFunCumulantDefect.charFun_normalization
#print axioms YMGap.Continuum.CharFunCumulantDefect.charFun_freeEnd_zero
#print axioms YMGap.Continuum.CharFunCumulantDefect.charFun_marginal_linear
#print axioms YMGap.Continuum.CharFunCumulantDefect.charFun_transverse_quadratic
#print axioms YMGap.Continuum.CharFunCumulantDefect.charFun_defect_decomposition
#print axioms YMGap.Continuum.CharFunCumulantDefect.charFunCumulantDefect_eq
#print axioms YMGap.Continuum.CharFunCumulantDefect.charFunCumulant_fullFloor
