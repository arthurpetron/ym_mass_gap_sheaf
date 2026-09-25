/-
# Squared one-step response on the SAME all-nome Wilson carrier

This core certificate combines the existing positive connected plaquette
response with completed Cauchy--Schwarz and exact time balance.  It stops at
the product lower bound; the positive denominator and lag-two floor are kept
in the downstream compiler module.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
import YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponseCore

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
  (uniformFloor uniformFloor_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

private theorem square_mono {a b : RC} (ha : RCnonneg a) (hab : RCle a b) :
    RCle (RCmul a a) (RCmul b b) := by
  have h1 := RCmul_mono_nonneg_left ha hab
  have h2 := RCmul_mono_nonneg_left (RCle_trans ha hab) hab
  rw [RCmul_comm b a] at h2
  exact RCle_trans h1 h2

theorem completed_oneStep_diagonal (z : Completion hw0 hw1 width) :
    B (T 1 z) (T 1 z) = B z (T 2 z) :=
  (completedInner_time_balance hw0 hw1 1 z (T 1 z)).trans
    (congrArg (fun y => B z y)
      (completedTime_add hw0 hw1 1 1 z).symm)

theorem plaquetteExcitation_response_square
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Rq (uniformFloor hw0 width * uniformFloor hw0 width))
      (RCmul (B v v) (B v (T 2 v))) := by
  have hd : RCnonneg (Rq (uniformFloor hw0 width)) := by
    apply leEv_of_le
    intro n
    change (0 : Q') ≤ uniformFloor hw0 width + Q'.invSucc n
    exact Q'.zero_le_add _ _
      (Q'.le_of_lt (uniformFloor_positive hw0 hw1 width))
      (Q'.invSucc_nonneg n)
  have h := RCle_trans
    (square_mono hd
      (plaquetteExcitation_response_floor hw0 hw1 width face hf hactive))
    (completedInner_cauchySchwarz hw0 hw1 v (T 1 v))
  rw [completed_oneStep_diagonal (hw0 := hw0) (hw1 := hw1)
    (width := width)] at h
  exact h

#print axioms completed_oneStep_diagonal
#print axioms plaquetteExcitation_response_square

end YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponseCore
