/-
# Same-carrier normalized plaquette response

The explicit lag-two response floor is divided by the actual completed
diagonal ceiling.  The result is a positive Rayleigh-style lower witness for
the true lag-two matrix coefficient of the same all-nome Wilson excitation.
The witness remains nome/width-dependent and is not a uniform spectral or
physical mass bound.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteRelativeFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "C" => plaquetteNormCeiling hw0 hw1 width face hf

private theorem rcscale_as_mul (a : Q') (b : RC) :
    RCscale a b = RCmul (Rq a) b := by
  refine Quotient.inductionOn b ?_
  intro A
  rfl

def relativeFloor : Q' :=
  twoStepFloor hw0 hw1 width face hf *
    Q'.recipPos C (plaquetteNormCeiling_positive hw0 hw1 width face hf)

theorem relativeFloor_positive : (0 : Q') < relativeFloor hw0 hw1 width face hf :=
  Q'.mul_pos (twoStepFloor_positive hw0 hw1 width face hf)
    (Q'.recipPos_pos _ _)

private theorem relativeFloor_cap :
    RCscale (relativeFloor hw0 hw1 width face hf) (Rq C) =
      Rq (twoStepFloor hw0 hw1 width face hf) := by
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.mul_recipPos_eqv C
            (plaquetteNormCeiling_positive hw0 hw1 width face hf))))
      (Q'.mul_one_eqv _))

theorem plaquetteExcitation_relative_floor
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (RCscale (relativeFloor hw0 hw1 width face hf) (B v v))
      (B v (T 2 v)) := by
  have hcap : RCle (B v v) (Rq C) :=
    plaquetteExcitation_norm_ceiling hw0 hw1 width face hf
  have hscaled := RCscale_mono
    (Q'.le_of_lt (relativeFloor_positive hw0 hw1 width face hf)) hcap
  rw [relativeFloor_cap] at hscaled
  exact RCle_trans hscaled
    (plaquetteExcitation_twoStep_floor hw0 hw1 width face hf hactive)

private theorem rational_scale_cancel_of_floor {a b f : Q'} {X : RC}
    (hf : (0 : Q') < f)
    (hfloor : RCle (Rq f) X)
    (hscaled : RCle (RCscale a X) (RCscale b X)) : a ≤ b := by
  revert hfloor hscaled
  refine Quotient.inductionOn X ?_
  intro A hfloor hscaled
  have hc : leEv (ofQ' a) (ofQ' b) :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap.leEv_cancel_mul_right_posEv
      ⟨f, hf, hfloor⟩ hscaled
  exact GNSQuotient.GNSData.RCofQ'_le_reflect hc

theorem plaquette_relativeFloor_le_rate
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    relativeFloor hw0 hw1 width face hf ≤ twoStepRate hw0 hw1 width := by
  have hlow := plaquetteExcitation_relative_floor hw0 hw1 width face hf hactive
  have hupper : RCle (B v (T 2 v))
      (RCscale (twoStepRate hw0 hw1 width) (B v v)) := by
    rw [show RCscale (twoStepRate hw0 hw1 width) (B v v) =
      RCmul (Rq (twoStepRate hw0 hw1 width)) (B v v) by
        exact rcscale_as_mul (twoStepRate hw0 hw1 width) (B v v)]
    exact plaquetteExcitation_twoStep_bound hw0 hw1 width face hf
  exact rational_scale_cancel_of_floor
    (starRatio_positive hw0 hw1)
    (plaquetteExcitation_norm_floor hw0 hw1 width face hf)
    (RCle_trans hlow hupper)

theorem twoStepRate_positive_of_plaquette
    (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    (0 : Q') < twoStepRate hw0 hw1 width :=
  Q'.pos_of_lt_of_le
    (relativeFloor_positive hw0 hw1 width face hf)
    (plaquette_relativeFloor_le_rate hw0 hw1 width face hf hactive)

#print axioms relativeFloor
#print axioms relativeFloor_positive
#print axioms relativeFloor_cap
#print axioms plaquetteExcitation_relative_floor
#print axioms plaquette_relativeFloor_le_rate
#print axioms twoStepRate_positive_of_plaquette

end YMGap.Continuum.BF4WilsonAllNomePlaquetteRelativeFloor
