/-
# Zero-shift uniqueness on the SAME vacuum-complement domain

The original positive form margin kills the difference of two domain inputs
with the same output, provided both inputs are orthogonal to the original
vacuum. This does not assert full-carrier injectivity or remove its kernel.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorDerivative
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear

namespace YMGap.Continuum.BF4WilsonAllNomeSectorZeroInjective

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint graph)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphGap (graph_form_gap)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap (coreMargin coreMargin_positive)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "B" => completedInner hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "Point" => DomainPoint hw0 hw1 (width := width)

/-- Equality of original derivative outputs determines the original
vacuum-orthogonal sector inputs, without a positive shift. -/
theorem input_injective (p q : Point)
    (hp : B U p.input.val = RCzero) (hq : B U q.input.val = RCzero)
    (h : p.output.val = q.output.val) : p.input.val = q.input.val := by
  let du := Sub p.input.val q.input.val
  have G := BF4WilsonAllNomeDerivativeGraph.subtract hw0 hw1
    (graph hw0 hw1 p) (graph hw0 hw1 q)
  have hu : B U du = RCzero := by
    change B U (Sub p.input.val q.input.val) = RCzero
    rw [completedInner_sub_right, hp, hq]
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => (by decide : Q'.eqv ((0 : Q') + -0) 0)))
  have hg := graph_form_gap hw0 hw1 G hu
  rw [h, completedSub_self, completedInner_zero_right] at hg
  let delta := coreMargin hw0 hw1 width
  have hd : (0 : Q') < delta := coreMargin_positive hw0 hw1
  have hc : Q'.eqv (Q'.recipPos delta hd * delta) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv delta hd)
  have hn := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos delta hd)) hg
  rw [RCscale_RCscale, RCscale_RCzero, scale_congr hc, RCscale_one] at hn
  have hdist : completedDist hw0 hw1 p.input.val q.input.val = RCzero :=
    RCle_antisymm hn (completedDist_nonnegative hw0 hw1 p.input.val q.input.val)
  exact (completedDist_zero_iff hw0 hw1 p.input.val q.input.val).mp hdist

#print axioms input_injective

end YMGap.Continuum.BF4WilsonAllNomeSectorZeroInjective
