/-
# Step n = 1 Dobrushin/W₁ certificates + fineAt (open hDobW1)

Additive.  Decidable certificates at w = 7/20 for the one-sided-weight
Dobrushin product ((12 + √8 + 1/√8)·κ ≤ 0.94), plus fineAt assembly at
nome index 2 reusing Step0's CentredPowerDecayVC → EvenDecay → twoStepFactor
chain verbatim.  W₁/Haar/L1/Pulled* left OPEN as `hDobW1_OPEN`.

Mathlib-free; no sorry/admit/Classical/native_decide/omega/simpa/grind.
Not chart closure / not gap evidence.  Paper: steps01_uniform.md §9 / §9.7.
-/

import YMGap.RG.Step0DobrushinUniform
import YMGap.RG.Robust3UndershootAfSchedule
import YMGap.RG.Robust3CrossUniform
import YMGap.Continuum.EvenDecayTwoStepFactor
import YMGap.Continuum.BF4WilsonAllNomeCompletedInner
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.ReconstructionCapstone

namespace YMGap.RG.Step1DobrushinUniform

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule)
open YMGap.RG.Robust3CrossUniform (fineAt)
open YMGap.Continuum.EvenDecayTwoStepFactor (twoStepFactor_of_even_decay)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner_nonnegative)
open YMGap.RG.Step0DobrushinUniform
  (wEighth CentredPowerDecayVC evenDecay_of_centredPowerDecayVC)

/-! ## (i) Decidable certificates (steps01_uniform.md §9.6) -/

/-- Lower bound witness for √8 (= e^{m*}).  Same value as Step0 `cSqrt`. -/
def cE : Q' := Q'.mkPos 2829 1000 (by decide)

/-- Lower bound witness for 1/√8 (= e^{−m*}). -/
def cEi : Q' := Q'.mkPos 354 1000 (by decide)

/-- Uniform geodesic-W₁ single-site influence ceiling at w = 7/20 (κ ≤ 0.0618). -/
def cKappa1 : Q' := Q'.mkPos 618 10000 (by decide)

/-- `cEi ≥ 1/√8`, via `1 ≤ 8 · cEi²` (decidable; 8·0.354² = 1.002528 ≥ 1). -/
theorem invSqrt8_le : (1 : Q') ≤ (8 : Q') * (cEi * cEi) := by decide

/-- One-sided Dobrushin product at w = 7/20:
`(12 + √8 + 1/√8) · κ ≤ 0.94` (decidable; ≈ 0.9383 ≤ 0.94).
Does not formalise W₁/Haar; those stay in `hDobW1_OPEN`. -/
theorem dobrushin_W1_7_20 :
    ((12 : Q') + cE + cEi) * cKappa1 ≤ Q'.mkPos 94 100 (by decide) := by decide

/-! ## (ii) fineAt assembly (mirror of Step0, nome index 2) -/

private theorem wEighth_mul_self :
    (wEighth * wEighth).eqv (Q'.mkPos 1 64 (by decide)) := by decide

/-- Step n = 1 fineAt for all widths, conditional on the open W₁-side
CentredPowerDecayVC envelope at nome index 2 and rate `wEighth`. -/
theorem fineAt_step1_all_widths
    (hDobW1_OPEN : ∀ width,
      CentredPowerDecayVC
        (robust3UndershootSchedule.nome_pos (0 + 1 + 1))
        (robust3UndershootSchedule.nome_lt_one (0 + 1 + 1)) width wEighth) :
    ∀ W : Nat → Nat, fineAt W 1 (Q'.mkPos 1 64 (by decide)) := by
  intro W
  -- fineAt W 1 unfolds to WilsonVacuumSqTwoStepFactor at nome_pos (0+1+1), width W (0+1+1)
  let hw0 := robust3UndershootSchedule.nome_pos (0 + 1 + 1)
  let hw1 := robust3UndershootSchedule.nome_lt_one (0 + 1 + 1)
  let width := W (0 + 1 + 1)
  have hq : (0 : Q') < wEighth := by decide
  have hEven := evenDecay_of_centredPowerDecayVC hw0 hw1 wEighth hq (hDobW1_OPEN width)
  have hTS := twoStepFactor_of_even_decay hw0 hw1 width wEighth hEven
  intro y
  have h := hTS y
  have hnn := completedInner_nonnegative hw0 hw1 y.val
  exact RCle_trans h
    (RCscale_mono_scalar (Q'.le_of_eqv wEighth_mul_self) hnn)

end YMGap.RG.Step1DobrushinUniform

#print axioms YMGap.RG.Step1DobrushinUniform.invSqrt8_le
#print axioms YMGap.RG.Step1DobrushinUniform.dobrushin_W1_7_20
#print axioms YMGap.RG.Step1DobrushinUniform.fineAt_step1_all_widths
