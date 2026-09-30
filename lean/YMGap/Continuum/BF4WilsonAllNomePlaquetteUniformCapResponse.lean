/-
# Plaquette response with the universal fundamental-loop norm cap

The actual centered plaquette excitation on the literal-width all-nome
completion has squared norm at most 4. Combining this uniform cap with the
existing same-carrier response-square certificate gives explicit lag-two and
Rayleigh floors `uniformFloor^2/4` and `uniformFloor^2/16`. These are still
fixed-parameter response estimates: no nome/width-uniform positive rate or
continuum conclusion follows.
-/

import YMGap.Continuum.BF4WilsonAllNomeLoopNormBound
import YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponseCore

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteUniformCapResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
  (uniformFloor uniformFloor_positive)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector)
open YMGap.Continuum.BF4WilsonAllNomeLoopNormBound (centered_loop_norm_le_four)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponseCore

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "u" => uniformFloor hw0 width
local notation "hfour" => Q'.ofNat_succ_pos 3

/-- The existing plaquette vector is exactly the centered fundamental loop. -/
theorem plaquette_norm_le_four :
    RCle (B v v) (Rq 4) := by
  change RCle
    (B (centeredVector hw0 hw1 (loopState (plaquetteLoop face hf)))
      (centeredVector hw0 hw1 (loopState (plaquetteLoop face hf)))) (Rq 4)
  exact centered_loop_norm_le_four hw0 hw1 (plaquetteLoop face hf)

/-- Absolute lag-two floor: `u^2 / 4`, written as `u^2 * recipPos 4`. -/
def absoluteFloor : Q' := u * u * Q'.recipPos 4 hfour

include hw1 in
theorem absoluteFloor_positive : (0 : Q') < absoluteFloor hw0 width :=
  Q'.mul_pos (Q'.mul_pos (uniformFloor_positive hw0 hw1 width)
    (uniformFloor_positive hw0 hw1 width)) (Q'.recipPos_pos 4 hfour)

private theorem rational_scale (a b : Q') :
    RCscale a (Rq b) = Rq (a * b) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul a b).symm

private theorem inverse_scale_four (x : RC) :
    RCscale (Q'.recipPos 4 hfour) (RCmul (Rq 4) x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv 4 hfour)))
      (Q'.one_mul_eqv _))

/-- The actual centered plaquette has lag-two pairing at least `u^2 / 4`.
The response is still for the original completed transfer on this carrier. -/
theorem plaquette_twoStep_floor_four
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Rq (absoluteFloor hw0 width)) (B v (T 2 v)) := by
  have hnonneg : RCnonneg (B v (T 2 v)) := by
    rw [← completed_oneStep_diagonal (hw0 := hw0) (hw1 := hw1)
      (width := width)]
    exact completedInner_nonnegative hw0 hw1 (T 1 v)
  have hscaled := RCmul_mono_nonneg_left hnonneg
    (plaquette_norm_le_four hw0 hw1 width face hf)
  rw [RCmul_comm (B v (T 2 v)) (B v v),
    RCmul_comm (B v (T 2 v)) (Rq 4)] at hscaled
  have h := RCscale_mono
    (Q'.le_of_lt (Q'.recipPos_pos 4 hfour))
    (RCle_trans
      (plaquetteExcitation_response_square hw0 hw1 width face hf hactive)
      hscaled)
  rw [inverse_scale_four] at h
  have hp : RCscale (Q'.recipPos 4 hfour) (Rq (u * u)) =
      Rq (absoluteFloor hw0 width) := by
    rw [rational_scale]
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.mul_comm_eqv _ _))
  rw [hp] at h
  exact h

/-- The relative floor is the absolute floor divided by 4, hence `u^2/16`. -/
def relativeFloor : Q' := absoluteFloor hw0 width * Q'.recipPos 4 hfour

include hw1 in
theorem relativeFloor_positive :
    (0 : Q') < relativeFloor hw0 width :=
  Q'.mul_pos (absoluteFloor_positive hw0 hw1 width) (Q'.recipPos_pos 4 hfour)

private theorem relativeFloor_cap :
    RCscale (relativeFloor hw0 width) (Rq 4) =
      Rq (absoluteFloor hw0 width) := by
  rw [rational_scale]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv 4 hfour)))
      (Q'.mul_one_eqv _))

/-- Same-object Rayleigh lower bound with explicit scalar `u^2/16`. -/
theorem plaquette_relative_floor_four
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (RCscale (relativeFloor hw0 width) (B v v))
      (B v (T 2 v)) := by
  have hscaled := RCscale_mono
    (Q'.le_of_lt (relativeFloor_positive hw0 hw1 width))
    (plaquette_norm_le_four hw0 hw1 width face hf)
  rw [relativeFloor_cap] at hscaled
  exact RCle_trans hscaled
    (plaquette_twoStep_floor_four hw0 hw1 width face hf hactive)

private theorem rational_scale_cancel_of_floor {a b f : Q'} {X : RC}
    (hf : (0 : Q') < f) (hfloor : RCle (Rq f) X)
    (hscaled : RCle (RCscale a X) (RCscale b X)) : a ≤ b := by
  revert hfloor hscaled
  refine Quotient.inductionOn X ?_
  intro A hfloor hscaled
  have hc : leEv (ofQ' a) (ofQ' b) :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap.leEv_cancel_mul_right_posEv
      ⟨f, hf, hfloor⟩ hscaled
  exact GNSQuotient.GNSData.RCofQ'_le_reflect hc

include hf in
/-- Calibration against the existing transfer estimate cancels the actual
positive plaquette norm and does not invoke its older expression-dependent cap. -/
theorem relativeFloor_le_twoStepRate
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    relativeFloor hw0 width ≤ twoStepRate hw0 hw1 width := by
  have hlow := plaquette_relative_floor_four hw0 hw1 width face hf hactive
  have hupper : RCle (B v (T 2 v))
      (RCscale (twoStepRate hw0 hw1 width) (B v v)) := by
    rw [show RCscale (twoStepRate hw0 hw1 width) (B v v) =
      RCmul (Rq (twoStepRate hw0 hw1 width)) (B v v) by
        refine Quotient.inductionOn (B v v) ?_
        intro X
        rfl]
    exact plaquetteExcitation_twoStep_bound hw0 hw1 width face hf
  exact rational_scale_cancel_of_floor
    (starRatio_positive hw0 hw1)
    (plaquetteExcitation_norm_floor hw0 hw1 width face hf)
    (RCle_trans hlow hupper)

#print axioms plaquette_norm_le_four
#print axioms absoluteFloor
#print axioms absoluteFloor_positive
#print axioms plaquette_twoStep_floor_four
#print axioms relativeFloor
#print axioms relativeFloor_positive
#print axioms plaquette_relative_floor_four
#print axioms relativeFloor_le_twoStepRate

end YMGap.Continuum.BF4WilsonAllNomePlaquetteUniformCapResponse
