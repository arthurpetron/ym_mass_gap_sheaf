/-
# Positive two-step response on the SAME all-nome Wilson carrier

The core response-square certificate is combined with the explicit completed
diagonal ceiling.  The resulting positive lag-two floor remains on the
literal-width all-nome completion; nome and width remain visible parameters.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponseCore

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
  (uniformFloor uniformFloor_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponseCore

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "C" => plaquetteNormCeiling hw0 hw1 width face hf

private theorem inverse_scale (P : Q') (hP : (0 : Q') < P) (a : RC) :
    RCscale (Q'.recipPos P hP) (RCmul (Rq P) a) = a := by
  refine Quotient.inductionOn a ?_
  intro A
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv P hP)))
      (Q'.one_mul_eqv _))

def twoStepFloor : Q' :=
  (uniformFloor hw0 width * uniformFloor hw0 width) *
    Q'.recipPos C (plaquetteNormCeiling_positive hw0 hw1 width face hf)

theorem twoStepFloor_positive :
    (0 : Q') < twoStepFloor hw0 hw1 width face hf :=
  Q'.mul_pos
    (Q'.mul_pos (uniformFloor_positive hw0 hw1 width)
      (uniformFloor_positive hw0 hw1 width))
    (Q'.recipPos_pos _ _)

theorem plaquetteExcitation_twoStep_floor
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Rq (twoStepFloor hw0 hw1 width face hf)) (B v (T 2 v)) := by
  have hnonneg : RCnonneg (B v (T 2 v)) := by
    rw [← completed_oneStep_diagonal (hw0 := hw0) (hw1 := hw1)
      (width := width)]
    exact completedInner_nonnegative hw0 hw1 (T 1 v)
  have hcap := RCmul_mono_nonneg_left hnonneg
    (plaquetteExcitation_norm_ceiling hw0 hw1 width face hf)
  rw [RCmul_comm (B v (T 2 v)) (B v v),
    RCmul_comm (B v (T 2 v)) (Rq C)] at hcap
  have h := RCscale_mono
    (Q'.le_of_lt (Q'.recipPos_pos C
      (plaquetteNormCeiling_positive hw0 hw1 width face hf)))
    (RCle_trans
      (plaquetteExcitation_response_square hw0 hw1 width face hf hactive)
      hcap)
  rw [inverse_scale C (plaquetteNormCeiling_positive hw0 hw1 width face hf)] at h
  have hp : RCscale (Q'.recipPos C
      (plaquetteNormCeiling_positive hw0 hw1 width face hf))
      (Rq (uniformFloor hw0 width * uniformFloor hw0 width)) =
      Rq (twoStepFloor hw0 hw1 width face hf) := by
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.mul_comm_eqv _ _))
  rw [hp] at h
  exact h

#print axioms twoStepFloor
#print axioms twoStepFloor_positive
#print axioms plaquetteExcitation_twoStep_floor

end YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse
