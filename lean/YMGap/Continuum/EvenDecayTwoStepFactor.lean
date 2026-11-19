/-
# Even-decay ⇒ one-step / two-step vacuum-complement factors

Additive.  Via `completedInner_even_diagonal`:

* one-step: `B(Tx,Tx) = B(x, T₂x)`, so even-lag decay at lag 1 is a one-step
  norm bound;
* two-step: `B(T₂x,T₂x) = B(x, T₄x)`, so even-lag decay at lag 2 is a
  two-step vacuum-complement factor.

Specializes at `centeredExcitation` (already a `VacuumComplement`).
Uses live `Q'.pow` for the rate power (no `RCpow`/`RCone`).
Mathlib-free; not chart closure / not gap evidence by itself.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedGap
import YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
import YMGap.Continuum.BF4WilsonAllNomeCenteredVector
import YMGap.Continuum.ReconstructionCapstone

namespace YMGap.Continuum.EvenDecayTwoStepFactor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap (completedInner_even_diagonal)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
  (WilsonVacuumSqFactor WilsonVacuumSqTwoStepFactor)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredExcitation)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)

section

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Even-lag correlator decay hypothesis at a fixed vector. -/
def EvenDecay (x : V) (r : Q') : Prop :=
  ∀ n : Nat, RCle (B x (T (2 * n) x)) (RCscale (r ^ n) (B x x))

private theorem pow_one_eqv (r : Q') : (r ^ 1).eqv r :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left r (r ^ 0) (1 : Q')
      (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')))
    (Q'.mul_one_eqv r)

private theorem pow_two_eqv (r : Q') : (r ^ 2).eqv (r * r) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_refl (r * r ^ 1))
    (Q'.mul_eqv_congr_left r _ _ (pow_one_eqv r))

/-- One-step norm bound from even decay at lag 1, via the even diagonal. -/
theorem oneStep_of_even_decay (x : V) (r : Q') (h : EvenDecay hw0 hw1 width x r) :
    RCle (B (T 1 x) (T 1 x)) (RCscale r (B x x)) := by
  have h1 : RCle (B x (T (2 * 1) x)) (RCscale (r ^ 1) (B x x)) := h 1
  have hdiag : B x (T (2 * 1) x) = B (T 1 x) (T 1 x) :=
    completedInner_even_diagonal hw0 hw1 width 1 x
  have h2 : RCle (B (T 1 x) (T 1 x)) (RCscale (r ^ 1) (B x x)) := by
    rw [← hdiag]; exact h1
  have hnn : RCnonneg (B x x) := completedInner_nonnegative hw0 hw1 x
  exact RCle_trans h2 (CReal.RCscale_mono_scalar (Q'.le_of_eqv (pow_one_eqv r)) hnn)

/-- `WilsonVacuumSqFactor` from a uniform even-decay hypothesis on the whole
vacuum complement. -/
theorem wilsonVacuumSqFactor_of_even_decay (r : Q')
    (h : ∀ y : VacuumComplement hw0 hw1 (width := width),
      EvenDecay hw0 hw1 width y.val r) :
    WilsonVacuumSqFactor hw0 hw1 width r := fun y =>
  oneStep_of_even_decay hw0 hw1 width y.val r (h y)

/-- Pointwise two-step bound at a single vacuum-complement vector. -/
theorem twoStep_of_even_decay_at (y : VacuumComplement hw0 hw1 (width := width))
    (r : Q') (h : EvenDecay hw0 hw1 width y.val r) :
    RCle (B (T 2 y.val) (T 2 y.val)) (RCscale (r * r) (B y.val y.val)) := by
  have h2 : RCle (B y.val (T (2 * 2) y.val)) (RCscale (r ^ 2) (B y.val y.val)) := h 2
  have hdiag : B y.val (T (2 * 2) y.val) = B (T 2 y.val) (T 2 y.val) :=
    completedInner_even_diagonal hw0 hw1 width 2 y.val
  have hbound : RCle (B (T 2 y.val) (T 2 y.val)) (RCscale (r ^ 2) (B y.val y.val)) := by
    rw [← hdiag]; exact h2
  have hnn : RCnonneg (B y.val y.val) := completedInner_nonnegative hw0 hw1 y.val
  exact RCle_trans hbound (CReal.RCscale_mono_scalar (Q'.le_of_eqv (pow_two_eqv r)) hnn)

/-- Uniform two-step factor on the vacuum complement. -/
theorem twoStepFactor_of_even_decay (r : Q')
    (h : ∀ y : VacuumComplement hw0 hw1 (width := width),
      EvenDecay hw0 hw1 width y.val r) :
    WilsonVacuumSqTwoStepFactor hw0 hw1 width (r * r) := fun y =>
  twoStep_of_even_decay_at hw0 hw1 width y r (h y)

/-- Centered excitation instance. -/
theorem twoStepFactor_of_even_decay_centeredExcitation
    (ψ : IntrinsicExpression width) (r : Q')
    (h : EvenDecay hw0 hw1 width (centeredExcitation hw0 hw1 ψ).val r) :
    RCle
      (B (T 2 (centeredExcitation hw0 hw1 ψ).val)
          (T 2 (centeredExcitation hw0 hw1 ψ).val))
      (RCscale (r * r) (B (centeredExcitation hw0 hw1 ψ).val
          (centeredExcitation hw0 hw1 ψ).val)) :=
  twoStep_of_even_decay_at hw0 hw1 width (centeredExcitation hw0 hw1 ψ) r h

end

end YMGap.Continuum.EvenDecayTwoStepFactor

/-! ## Axiom audit -/

#print axioms YMGap.Continuum.EvenDecayTwoStepFactor.oneStep_of_even_decay
#print axioms YMGap.Continuum.EvenDecayTwoStepFactor.wilsonVacuumSqFactor_of_even_decay
#print axioms YMGap.Continuum.EvenDecayTwoStepFactor.twoStep_of_even_decay_at
#print axioms YMGap.Continuum.EvenDecayTwoStepFactor.twoStepFactor_of_even_decay
#print axioms
  YMGap.Continuum.EvenDecayTwoStepFactor.twoStepFactor_of_even_decay_centeredExcitation
