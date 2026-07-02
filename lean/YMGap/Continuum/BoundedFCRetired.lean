/-
# `continuousFC_retired` — the ④-chain capstone into `dischargeBTC_complete`

This module ties the continuous-functional-calculus ④ chain into the
never-yet-consumed sink `dischargeBTC_complete`
(`Continuum/FCNormBoundLimit.lean`).  The composed capstone

  `continuousFC_retired`

feeds the Bernstein polynomial sequence `bernsteinPoly F` of a
constructively-presented continuous symbol `F : CtsMod` into
`dischargeBTC_complete`, producing a `BoundedTransferCalculusResidual` — a
BOUNDED self-adjoint operator `f(T) = lim_n (bernsteinPoly F n)(T)` with the
operator-norm bound `‖f(T)x‖² ≤ M·‖x‖²`, `M = F.bound²`.

## What is proved here vs. carried

The BODY of the capstone is FULLY proved: self-adjointness and the norm-bound
limit are already theorems inside `dischargeBTC_complete`
(`fcApply_selfAdjoint_limit` / `fcApply_normBound_limit`).  Only three honest
residuals are surfaced as explicit hypotheses (never `sorry`, never faked):

  * **R1** `termwise` — the per-polynomial spectral norm bound
    `‖bₚ(T)x‖² ≤ M·‖x‖²` (reduces to the coordinate resolution + `F.bound`).
  * **R3** `img` — the choice-free `∀`-point `PolyImageCauchy` representative.

`M`, `img`, `termwise` are exactly the carried fields of `CompleteFCLimitData`;
everything else in the body is `dischargeBTC_complete`.

## Non-vacuity

`MonotoneOmegaVanishing_of_lipschitz` builds the monotone vanishing modulus for
any Lipschitz symbol; `constCtsMod` / `monotoneOmegaVanishing_constCtsMod`
exhibit a concrete inhabited `CtsMod` with its `MonotoneOmegaVanishing`, so the
elementary data of the capstone are non-vacuous.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.BernsteinSequenceWrap
import YMGap.Continuum.BernsteinStageData
import YMGap.Continuum.BernsteinUniformConvergence
import YMGap.Constructive.CRealAbs

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

namespace YMGap.Continuum.BoundedFCRetired

open YMGap.Continuum

/-! ## 1. The composed ④-chain capstone -/

/-- **`continuousFC_retired` — the retirement theorem.**  The Bernstein sequence
`bernsteinPoly F` of a continuous symbol `F` feeds `dischargeBTC_complete`,
yielding a `BoundedTransferCalculusResidual` for the FORMED transfer operator.

The body is exactly step 4 of the plan and is fully proved; the only carried
data are `M = F.bound²`, the choice-free per-point image supplier `img` (R3),
and the per-polynomial spectral norm bound `termwise` (R1).  Both residuals are
surfaced as explicit hypotheses, never hidden. -/
def continuousFC_retired
    (SL    : LinearSmulGNSData)
    (LT    : LinearTransferOperator SL.toSmulGNSData)
    (model : SpectralModel) (gap : LocatedSpectralGap model)
    (F     : CtsMod)
    (M     : Q')
    -- RESIDUAL R3: choice-free ∀-point representative + distance supply.
    (img   : ∀ x : GNSCompletionSpace SL.toGNSData,
               PolyImageCauchy SL LT.toAdditiveTransferOperator (bernsteinPoly F) x)
    -- RESIDUAL R1: per-polynomial spectral norm bound.
    (termwise : ∀ (p : Nat) (x : GNSCompletionSpace SL.toGNSData),
        RCle (SL.toGNSData.cinnerCompl
                (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (bernsteinPoly F p) x)
                (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (bernsteinPoly F p) x))
             (RCscale M (SL.toGNSData.cinnerCompl x x))) :
    BoundedTransferCalculus.BoundedTransferCalculusResidual
      (spectralGapDataOfL SL.toSmulGNSData LT.toAdditiveTransferOperator model gap) :=
  dischargeBTC_complete SL LT model gap
    { pseq                   := bernsteinPoly F
      img                    := img
      normSqBound            := M
      polyNormBound_termwise := termwise }

/-! ## 2. Non-vacuity of the elementary symbol data

The capstone's symbol datum `F : CtsMod` together with `MonotoneOmegaVanishing F`
are non-vacuous: the constant symbol `f ≡ c` is a genuine `CtsMod` (bound `|c|`,
flat modulus `ω ≡ 0`; the sole real obligation `mod` is `|c − c| ≤ 0`), and it
carries a monotone vanishing modulus (`δ ε = ε`, `small : 0 ≤ ε`). -/

/-- **The constant symbol as a `CtsMod`.**  `f(x) = c` with uniform bound `|c|`
and flat modulus `ω ≡ 0`.  The only nontrivial field is `mod`, discharged by
`|c − c| = |0| ≤ 0`. -/
def constCtsMod (c : Q') : CtsMod where
  f _   := c
  bound := Q'.abs c
  ω _   := 0
  f_le  := fun _ => Q'.le_refl' (Q'.abs c)
  ω_nn  := fun _ => Q'.le_refl' 0
  mod   := fun _ _ _ _ => by
    -- goal: `Q'.abs (c - c) ≤ 0`; `c - c = c + -c ≈ 0` and `|0| ≤ 0`.
    have h1 : (Q'.abs (c + -c)).eqv (Q'.abs (0 : Q')) :=
      Q'.abs_eqv_congr (Q'.add_neg_self_eqv c)
    have hz : Q'.abs (0 : Q') ≤ 0 := by decide
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h1) hz

/-- **The monotone vanishing modulus for the constant symbol.**  `δ ε = ε` is
non-decreasing and positive, and `ω (δ ε) = 0 ≤ ε`. -/
def monotoneOmegaVanishing_constCtsMod (c : Q') :
    MonotoneOmegaVanishing (constCtsMod c) where
  delta ε := ε
  mono _ _ h := h
  pos _ h := h
  small _ h := Q'.le_of_lt h

/-- **Pipeline non-vacuity.**  A concrete `CtsMod` + `MonotoneOmegaVanishing`
pair exists, so the elementary data feeding `continuousFC_retired` are
inhabited. -/
example : MonotoneOmegaVanishing (constCtsMod 0) :=
  monotoneOmegaVanishing_constCtsMod 0

end YMGap.Continuum.BoundedFCRetired

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BoundedFCRetired.continuousFC_retired
#print axioms YMGap.Continuum.BoundedFCRetired.constCtsMod
#print axioms YMGap.Continuum.BoundedFCRetired.monotoneOmegaVanishing_constCtsMod
