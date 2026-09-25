/-
# The explicit plaquette excitation on the complex Wilson carrier

The plaquette state is first constructed in the actual real Wilson completion.
This file embeds that same state into the existing two-component complex
carrier and transports its orthogonality, norm, and lag-two response.  The
result is a fixed-nome/width same-object witness for the complex gap; it does
not assert a scaling or continuum identification.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexGap
import YMGap.Continuum.BF4WilsonAllNomeComplexRelativeLoss
import YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse

namespace YMGap.Continuum.BF4WilsonAllNomeComplexPlaquetteExcitation

set_option autoImplicit false
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeComplexification
open YMGap.Continuum.BF4WilsonAllNomeComplexGap
open YMGap.Continuum.BF4WilsonAllNomeComplexRelativeLoss
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "z" => embedReal hw0 hw1 width v
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "I" => inner hw0 hw1 width
local notation "CT" => complexTime hw0 hw1 width
local notation "CU" => complexUnit hw0 hw1 width

/-- The literal real plaquette excitation, embedded in the complex carrier. -/
def complexPlaquetteExcitation : ComplexCarrier hw0 hw1 width := z

theorem complexPlaquetteExcitation_eq :
    complexPlaquetteExcitation hw0 hw1 width face hf =
      embedReal hw0 hw1 width v := rfl

theorem complexPlaquetteExcitation_orthogonal :
    I CU (complexPlaquetteExcitation hw0 hw1 width face hf) =
      (RCzero, RCzero) := by
  change inner hw0 hw1 width
      (embedReal hw0 hw1 width (unitState hw0 hw1 width))
      (embedReal hw0 hw1 width v) = (RCzero, RCzero)
  rw [inner_embedReal]
  exact Prod.ext (plaquetteExcitation hw0 hw1 width face hf).property
    (by rfl)

theorem complexPlaquetteExcitation_diagonal :
    I (complexPlaquetteExcitation hw0 hw1 width face hf)
        (complexPlaquetteExcitation hw0 hw1 width face hf) =
      (B v v, RCzero) := by
  rw [complexPlaquetteExcitation_eq]
  exact inner_embedReal hw0 hw1 width v v

theorem complexPlaquetteExcitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio w)))
      (I (complexPlaquetteExcitation hw0 hw1 width face hf)
        (complexPlaquetteExcitation hw0 hw1 width face hf)).1 := by
  rw [complexPlaquetteExcitation_eq, inner_embedReal]
  exact plaquetteExcitation_norm_floor hw0 hw1 width face hf

theorem complexPlaquetteExcitation_twoStep_floor
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Rq (twoStepFloor hw0 hw1 width face hf))
      (I (complexPlaquetteExcitation hw0 hw1 width face hf)
        (CT 2 (complexPlaquetteExcitation hw0 hw1 width face hf))).1 := by
  rw [complexPlaquetteExcitation_eq, complexTime_embedReal, inner_embedReal]
  exact plaquetteExcitation_twoStep_floor hw0 hw1 width face hf hactive

theorem complexPlaquetteExcitation_relative_loss :
    RCle
      (RCscale (1 - twoStepRate hw0 hw1 width)
        (I (complexPlaquetteExcitation hw0 hw1 width face hf)
          (complexPlaquetteExcitation hw0 hw1 width face hf)).1)
      (RCsub
        (I (complexPlaquetteExcitation hw0 hw1 width face hf)
          (complexPlaquetteExcitation hw0 hw1 width face hf)).1
        (I (complexPlaquetteExcitation hw0 hw1 width face hf)
          (CT 2 (complexPlaquetteExcitation hw0 hw1 width face hf))).1) := by
  exact complex_twoStep_relative_loss hw0 hw1 width
    (complexPlaquetteExcitation hw0 hw1 width face hf)
    (complexPlaquetteExcitation_orthogonal hw0 hw1 width face hf)

theorem complexPlaquetteExcitation_even_lag_corr_decay (n : Nat) :
    RCle
      (I (complexPlaquetteExcitation hw0 hw1 width face hf)
        (CT (2*n) (complexPlaquetteExcitation hw0 hw1 width face hf))).1
      (RCscale ((twoStepRate hw0 hw1 width)^n)
        (I (complexPlaquetteExcitation hw0 hw1 width face hf)
          (complexPlaquetteExcitation hw0 hw1 width face hf)).1) := by
  exact complex_even_lag_corr_decay hw0 hw1 width n
    (complexPlaquetteExcitation hw0 hw1 width face hf)
    (complexPlaquetteExcitation_orthogonal hw0 hw1 width face hf)

/- The origin face supplies an unconditional witness after the two padding
   layers used by the response certificate. -/
def originComplexPlaquetteExcitation :
    ComplexCarrier hw0 hw1 (width + 2) :=
  complexPlaquetteExcitation hw0 hw1 (width + 2) originFace
    (originFace_mem (width + 1))

theorem originComplexPlaquetteExcitation_orthogonal :
    inner hw0 hw1 (width + 2) (complexUnit hw0 hw1 (width + 2))
        (originComplexPlaquetteExcitation hw0 hw1 width) =
      (RCzero, RCzero) := by
  exact complexPlaquetteExcitation_orthogonal hw0 hw1 (width + 2) originFace
    (originFace_mem (width + 1))

theorem originComplexPlaquetteExcitation_twoStep_floor
    (hactive : ∀ l, l ∈ edgesOf originFace →
      (baseLinks (width + 2)).idxOf l ∈ activeBlocks (width + 2)) :
    RCle (Rq (twoStepFloor hw0 hw1 (width + 2) originFace
        (originFace_mem (width + 1))))
      (inner hw0 hw1 (width + 2) (originComplexPlaquetteExcitation hw0 hw1 width)
        (complexTime hw0 hw1 (width + 2) 2
          (originComplexPlaquetteExcitation hw0 hw1 width))).1 := by
  exact complexPlaquetteExcitation_twoStep_floor hw0 hw1 (width + 2) originFace
    (originFace_mem (width + 1)) hactive

#print axioms complexPlaquetteExcitation
#print axioms complexPlaquetteExcitation_eq
#print axioms complexPlaquetteExcitation_orthogonal
#print axioms complexPlaquetteExcitation_diagonal
#print axioms complexPlaquetteExcitation_norm_floor
#print axioms complexPlaquetteExcitation_twoStep_floor
#print axioms complexPlaquetteExcitation_relative_loss
#print axioms complexPlaquetteExcitation_even_lag_corr_decay
#print axioms originComplexPlaquetteExcitation
#print axioms originComplexPlaquetteExcitation_orthogonal
#print axioms originComplexPlaquetteExcitation_twoStep_floor

end YMGap.Continuum.BF4WilsonAllNomeComplexPlaquetteExcitation
