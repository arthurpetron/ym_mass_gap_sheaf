/-
# Same-carrier plaquette rate calibration

The explicit positive lag-two response floor and the existing completed
strict transfer bound constrain one another on the SAME all-nome Wilson
completion.  This produces a rational inequality between the response floor,
the fixed-parameter transfer rate, and the completed diagonal ceiling.  It is
not a scaling-uniform estimate or a physical mass calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteRateCalibration

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
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_nonnegative)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "q" => twoStepRate hw0 hw1 width
local notation "C" => plaquetteNormCeiling hw0 hw1 width face hf

private theorem rcscale_as_mul (a : Q') (b : RC) :
    RCscale a b = RCmul (Rq a) b := by
  refine Quotient.inductionOn b ?_
  intro A
  rfl

private theorem rational_scale (a b : Q') :
    RCscale a (Rq b) = Rq (a * b) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul a b).symm

theorem plaquette_twoStep_floor_le_rate_mul_normCeiling
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    twoStepFloor hw0 hw1 width face hf ≤ q * C := by
  have hfloor : RCle (Rq (twoStepFloor hw0 hw1 width face hf))
      (B v (T 2 v)) :=
    plaquetteExcitation_twoStep_floor hw0 hw1 width face hf hactive
  have hupper : RCle (B v (T 2 v)) (RCscale q (B v v)) := by
    rw [rcscale_as_mul]
    exact plaquetteExcitation_twoStep_bound hw0 hw1 width face hf
  have hcap : RCle (B v v) (Rq C) :=
    plaquetteExcitation_norm_ceiling hw0 hw1 width face hf
  have hscaled : RCle (RCscale q (B v v)) (RCscale q (Rq C)) :=
    RCscale_mono (twoStepRate_nonnegative hw0 hw1 width) hcap
  have h := RCle_trans hfloor (RCle_trans hupper hscaled)
  rw [rational_scale] at h
  exact GNSQuotient.GNSData.RCofQ'_le_reflect h

#print axioms rcscale_as_mul
#print axioms rational_scale
#print axioms plaquette_twoStep_floor_le_rate_mul_normCeiling

end YMGap.Continuum.BF4WilsonAllNomePlaquetteRateCalibration
