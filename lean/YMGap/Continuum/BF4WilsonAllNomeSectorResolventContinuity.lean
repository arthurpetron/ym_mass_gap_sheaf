/-
# Uniform positive-shift continuity on the SAME vacuum complement

The exact resolvent identity and the original derivative form margin give
||R_lambda x-R_mu x||^2 <= (mu-lambda)^2 delta^(-4)||x||^2.
The constant is independent of the positive shifts, but retains the original
nome/width dependence of delta. This is the quantitative input for taking
the shift to zero, not a physical mass or continuum-uniform estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorResolventIdentity
import YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap

namespace YMGap.Continuum.BF4WilsonAllNomeSectorResolventContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolvent (state)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap
  (state_orthogonal uniform_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolventIdentity (resolvent_identity)
open YMGap.Continuum.BF4WilsonAllNomeResolventLimit (resolvent)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap (coreMargin coreMargin_positive)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "B" => completedInner hw0 hw1
local notation "R" => resolvent hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "Sector" => State hw0 hw1 (width := width)

/-- The bound is uniform in BOTH positive shift parameters, including
coincident parameters. Only the actual fixed-nome/width form margin enters. -/
theorem parameter_bound (lambda mu : Q')
    (hl : (0 : Q') < lambda) (hm : (0 : Q') < mu) (x : Sector)
    (hx : B U x.val = RCzero) :
    let r := Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1)
    RCle (completedDist hw0 hw1 (R lambda hl x.val) (R mu hm x.val))
      (RCscale (((mu-lambda)*(mu-lambda) * (r*r)) * (r*r)) (B x.val x.val)) := by
  let r := Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1)
  have hr2 : (0 : Q') ≤ r*r := SumOfSquares.q_mul_self_nonneg r
  have hd2 : (0 : Q') ≤ (mu-lambda)*(mu-lambda) :=
    SumOfSquares.q_mul_self_nonneg (mu-lambda)
  have hu := state_orthogonal hw0 hw1 mu hm x hx
  have hfirst := uniform_norm_bound hw0 hw1 lambda hl (state hw0 hw1 mu hm x) hu
  have hsecond := uniform_norm_bound hw0 hw1 mu hm x hx
  have h := RCscale_mono hd2 (RCle_trans hfirst (RCscale_mono hr2 hsecond))
  unfold completedDist
  rw [resolvent_identity hw0 hw1 lambda mu hl hm x,
    completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  simp only [RCscale_RCscale] at h
  rw [scale_congr
    (Q'.eqv_symm (Q'.mul_assoc_eqv ((mu-lambda)*(mu-lambda)) (r*r) (r*r)))
    (B x.val x.val)] at h
  exact h

#print axioms parameter_bound

end YMGap.Continuum.BF4WilsonAllNomeSectorResolventContinuity
