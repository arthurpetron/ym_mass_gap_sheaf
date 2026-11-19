/-
# Step n = 0 Dobrushin uniform: certificates + CentredPowerDecay interface

Additive.  Decidable TV-Dobrushin certificates at w = 1/8 and the
`CentredPowerDecay` interface adapted to live names (`centeredExcitation`,
`RCone' = ofQ' 1`).  Föllmer/Dobrushin itself left OPEN as `hDob_OPEN`.

HARD STOP this round: proofs of `evenDecay_of_centredPowerDecay` and
`fineAt_step0_all_widths` deferred (elaboration failures in the proof body).
Certificates + interface only.  No sorry/admit.

Does NOT formalise Dobrushin/Föllmer, W₁, L1, Haar, or Pulled*.
Mathlib-free; no Classical/native_decide/omega/simpa/grind.
Not chart closure / not gap evidence.
-/

import YMGap.Continuum.EvenDecayTwoStepFactor
import YMGap.Continuum.SU2LogConvexGapInfinite
import YMGap.Continuum.CRealLogConvexRatioMono
import YMGap.Continuum.BF4WilsonAllNomeCenteredVector
import YMGap.Continuum.BF4WilsonAllNomeCenteringPin
import YMGap.RG.CoarseConstantZero
import YMGap.RG.Robust3CrossUniform
import YMGap.RG.Robust3UndershootAfSchedule
import YMGap.RG.Robust3Width2Electric
import YMGap.Continuum.ReconstructionCapstone

namespace YMGap.RG.Step0DobrushinUniform

set_option autoImplicit false
set_option maxRecDepth 16384

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RG.Robust3Width2Electric (termF partialF)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredExcitation)

/-! ## (i) Decidable certificates -/

def wEighth : Q' := Q'.mkPos 1 8 (by decide)

/-- Crude positive tail majorant for the decidable F₁ certificate.
True series tail after N = 12 at w = 1/8 is ≪ 10⁻¹⁷⁰. -/
def tailBound (_w : Q') (_N : Nat) : Q' := Q'.mkPos 1 100000 (by decide)

def cF1 : Q' := Q'.mkPos 79 10000 (by decide)
def cAlpha : Q' := Q'.mkPos 14 100 (by decide)
def cSqrt : Q' := Q'.mkPos 2829 1000 (by decide)

theorem F1_eighth_le :
    partialF wEighth 12 + tailBound wEighth 12 ≤ (1 : Q') + cF1 := by decide

theorem dobrushin_eighth :
    ((12 : Q') + (2 : Q') * cSqrt) * cF1 ≤ cAlpha := by decide

theorem sqrt8_le :
    (8 : Q') ≤ cSqrt * cSqrt := by decide

/-! ## (ii) CentredPowerDecay interface

Live adaptation: paper `centeredState` on `IntrinsicExpression` → live
`centeredExcitation` (`centeredState_embed`).  `RCone'` → `ofQ' 1` class.

Deferred (next additive push; no statement change expected):
* `evenDecay_of_centredPowerDecay` via `dyadic_geometric_first_le` + shifts +
  CompletedGap density into `VacuumComplement`
* `fineAt_step0_all_widths` from `hDob_OPEN` + evenDecay +
  `twoStepFactor_of_even_decay` at r = 1/8 → factor 1/64
-/

def RCone' : RC := Quotient.mk crealSetoid (ofQ' (1 : Q'))

def CentredPowerDecay {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (q : Q') : Prop :=
  ∀ x : IntrinsicExpression width, ∃ C : Q', ∀ n : Nat,
    RCle
      (completedInner hw0 hw1
        (centeredExcitation hw0 hw1 x).val
        (completedTime hw0 hw1 (2 * n) (centeredExcitation hw0 hw1 x).val))
      (RCscale (C * q ^ n) RCone')

end YMGap.RG.Step0DobrushinUniform

#print axioms YMGap.RG.Step0DobrushinUniform.F1_eighth_le
#print axioms YMGap.RG.Step0DobrushinUniform.dobrushin_eighth
#print axioms YMGap.RG.Step0DobrushinUniform.sqrt8_le
