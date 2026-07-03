/-
The Wilson functional-calculus HEAD — wiring the now-UNCONDITIONAL weight-1
Parseval datum into `continuousFC_retired`, so that the entire
`WilsonTowerParseval` datum, the three `RCscale` scalar-order laws, and the
vacuum are ALL discharged internally, leaving only the two genuinely analytic
per-point residuals (`img` R3, `termwise` R1) plus the located spectral
`model`/`gap` at the capstone.

# The one structural correction over the stale research-lead head

The stale head wired `charLinearSmulGNS := qLinearSmulGNS w hw` (the
single-coordinate `V = Q'` module) and forced the user to hand-supply
`S`, `P`, `Rnonneg`, `Rscalar`, `Rone`, `vac`.  But
`FinEuclCompletionCoordsClose.symbolTypedParseval` (PROVED, unconditional)
discharges the WHOLE `WilsonTowerParseval` datum only over the N-coordinate
module `charSmulGNS N` (`V = Nat → Q'`) with symbol `charDiagonalSymbol` — a
DIFFERENT carrier.  To consume that now-free Parseval, `charLinearSmulGNS`
must be `charSmulGNS N` upgraded to a `LinearSmulGNSData` (its sole extra field
`smul_add_scalar` is per-coordinate `Q'` right-distributivity, `QPoly.q_add_mul`),
after which the glue collapses: `S`/`P`/order-laws/`vac` all become internal.

# What is proved here vs. carried

  * `charLinearSmulGNS N` — the `LinearSmulGNSData` over `charSmulGNS N`
    (GENUINE, discharged: `smul_add_scalar` = `q_add_mul`).
  * `char_Rnonneg` — the nonnegative-scale order law from `RCscale_mono`
    + `RCscale_RCzero` (GENUINE, discharged).
  * `wilsonTowerLinearTransfer` — the completed `LinearTransferOperator`, with
    the Parseval datum (`symbolTypedParseval …`), the three `RCscale` order
    laws (`char_Rnonneg`, `RCscale_scalar_mono`, `RCscale_one`), and the
    canonical embedded-zero vacuum all supplied internally (GENUINE assembly).
  * `wilson_continuous_functional_calculus` — the capstone specialization of
    `continuousFC_retired` on `wilsonTowerLinearTransfer`.  The only carried
    hypotheses are `img` (R3) and `termwise` (R1) plus `model`/`gap`.

# Honest scope of the remaining residuals

After this head, the ONLY carried hypotheses at the capstone are `img`
(R3, `PolyImageCauchy`, the choice-free per-point representative supplier) and
`termwise` (R1, the per-polynomial spectral norm bound), plus the located
`model`/`gap`.  The whole `WilsonTowerParseval` datum and the three `RCscale`
order laws and `vac` are now fully discharged internally.  Honesty caveat
(inherited verbatim from the `SymbolTypedParsevalClose` /
`FinEuclCompletionCoordsClose` headers): this is the WEIGHT-1 tower over its own
`charSmulGNS N` / `charDiagonalSymbol`, an existence witness with the physical
spectrum `λ_s = qpow w (c4 (s+1))` (gap from `λ_1 < 1`) but NOT a `√μ`-fidelity
match to the interacting `E_Λ` moment functional.  That fidelity match remains
a separate input.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.BoundedFCRetired
import YMGap.Continuum.WilsonLinearFC
import YMGap.Continuum.SymbolTypedParsevalClose
import YMGap.Continuum.FinEuclCompletionCoordsClose
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.ContinuousTransferCalculus

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSQuotient.GNSData
open YMGap.Continuum.ContinuousFCCarrierLimit
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ContinuousFunctionalCalculusForm
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.FCNormBoundLimit
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.WilsonLinearFC
open YMGap.Continuum.SymbolTypedParsevalClose
open YMGap.Continuum.FinEuclCompletionCoordsClose
open YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.WilsonFCHead

open YMGap.Continuum
open YMGap.Continuum.BoundedFCRetired

/-! ## 1. The `LinearSmulGNSData` witness over the N-coordinate carrier -/

/-- **`charLinearSmulGNS N` — the N-coordinate module upgraded to a
`LinearSmulGNSData`.**  Its base is `charSmulGNS N` (`V = Nat → Q'`), and the sole
extra field `smul_add_scalar` (`(s+t)·a ≈ s·a + t·a`) is per-coordinate `Q'`
right-distributivity `QPoly.q_add_mul`.  Crucially `(charLinearSmulGNS N).toSmulGNSData`
reduces to `charSmulGNS N`, so no coercion feeds either `wilsonLinearTransfer` or
`continuousFC_retired`. -/
def charLinearSmulGNS (N : Nat) : LinearSmulGNSData where
  toSmulGNSData := charSmulGNS N
  smul_add_scalar := fun s t a k => QPoly.q_add_mul s t (a k)

/-! ## 2. The nonnegative-scale order law (the only non-packaged one) -/

/-- **`char_Rnonneg` — nonnegativity of `RCscale s c` for `0 ≤ s`, `0 ≤ c`.**
From `RCscale_mono` (`RCle (RCscale s 0) (RCscale s c)`) and `RCscale_RCzero`
(`RCscale s 0 = 0`), so `RCle 0 (RCscale s c)`, i.e. `RCnonneg (RCscale s c)`.
The other two order laws are `CReal.RCscale_scalar_mono` and `CReal.RCscale_one`
directly. -/
theorem char_Rnonneg {s : Q'} (hs : (0 : Q') ≤ s) {c : CReal.RC}
    (hc : CReal.RCnonneg c) : CReal.RCnonneg (CReal.RCscale s c) := by
  have h := CReal.RCscale_mono hs hc
  rwa [CReal.RCscale_RCzero s] at h

/-! ## 3. The completed `LinearTransferOperator` — glue fully discharged -/

/-- **`wilsonTowerLinearTransfer` — the Wilson weight-1 tower as a completed
`LinearTransferOperator`.**  Feeds `wilsonLinearTransfer` the now-UNCONDITIONAL
Parseval datum `(symbolTypedParseval w hw0 hw1 N).parseval`, the three `RCscale`
scalar-order laws (`char_Rnonneg`, `CReal.RCscale_scalar_mono`,
`CReal.RCscale_one`), and the canonical embedded-zero vacuum.  Nothing is left as
a user obligation. -/
def wilsonTowerLinearTransfer (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    LinearTransferOperator (charLinearSmulGNS N).toSmulGNSData :=
  wilsonLinearTransfer (charDiagonalSymbol w hw0 hw1 N) rcScaleResidualPlus w hw0 hw1 N
    (symbolTypedParseval w hw0 hw1 N).parseval
    (fun {s} hs {c} hc => char_Rnonneg hs hc)
    (fun {s t} hst {c} hc => CReal.RCscale_scalar_mono hst hc)
    CReal.RCscale_one
    (embedV (charSmulGNS N).toGNSData (charSmulGNS N).toGNSData.zero)

/-! ## 4. The capstone specialization into `continuousFC_retired` -/

/-- **`wilson_continuous_functional_calculus` — the ④-chain capstone over the
Wilson weight-1 tower.**  Specializes `continuousFC_retired` on
`wilsonTowerLinearTransfer`.  The entire `WilsonTowerParseval` datum, the three
`RCscale` order laws, and the vacuum are discharged internally; the ONLY carried
hypotheses are:

  * `img` (R3) — the choice-free per-point `PolyImageCauchy` representative
    supplier, and
  * `termwise` (R1) — the per-polynomial spectral norm bound,

together with the located spectral `model`/`gap`.  It yields a
`BoundedTransferCalculusResidual` — a bounded self-adjoint `f(T)` with the
operator-norm bound `‖f(T)x‖² ≤ M·‖x‖²`. -/
def wilson_continuous_functional_calculus
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat)
    (model : SpectralModel) (gap : LocatedSpectralGap model)
    (F : CtsMod) (M : Q')
    (img : ∀ x : GNSCompletionSpace (charLinearSmulGNS N).toGNSData,
             PolyImageCauchy (charLinearSmulGNS N)
               (wilsonTowerLinearTransfer w hw0 hw1 N).toAdditiveTransferOperator
               (bernsteinPoly F) x)
    (termwise : ∀ (p : Nat)
        (x : GNSCompletionSpace (charLinearSmulGNS N).toGNSData),
        RCle ((charLinearSmulGNS N).toGNSData.cinnerCompl
                (polyApply (charLinearSmulGNS N).toSmulGNSData
                  (wilsonTowerLinearTransfer w hw0 hw1 N).toAdditiveTransferOperator
                  (bernsteinPoly F p) x)
                (polyApply (charLinearSmulGNS N).toSmulGNSData
                  (wilsonTowerLinearTransfer w hw0 hw1 N).toAdditiveTransferOperator
                  (bernsteinPoly F p) x))
             (RCscale M ((charLinearSmulGNS N).toGNSData.cinnerCompl x x))) :
    BoundedTransferCalculus.BoundedTransferCalculusResidual
      (spectralGapDataOfL (charLinearSmulGNS N).toSmulGNSData
        (wilsonTowerLinearTransfer w hw0 hw1 N).toAdditiveTransferOperator model gap) :=
  continuousFC_retired (charLinearSmulGNS N) (wilsonTowerLinearTransfer w hw0 hw1 N)
    model gap F M img termwise

/-! ## 5. Non-vacuity of the elementary symbol data

The capstone's `F : CtsMod` datum is non-vacuous: `monotoneOmegaVanishing_constCtsMod 0`
exhibits a concrete `CtsMod` with its `MonotoneOmegaVanishing`. -/

/-- **Pipeline non-vacuity.**  A concrete inhabited `CtsMod` (with its monotone
vanishing modulus) exists, so the elementary symbol data feeding
`wilson_continuous_functional_calculus` are non-vacuous. -/
example : MonotoneOmegaVanishing (constCtsMod 0) :=
  monotoneOmegaVanishing_constCtsMod 0

end YMGap.Continuum.WilsonFCHead

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonFCHead.charLinearSmulGNS
#print axioms YMGap.Continuum.WilsonFCHead.char_Rnonneg
#print axioms YMGap.Continuum.WilsonFCHead.wilsonTowerLinearTransfer
#print axioms YMGap.Continuum.WilsonFCHead.wilson_continuous_functional_calculus
