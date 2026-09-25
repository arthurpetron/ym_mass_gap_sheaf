/-
# Width degeneration of the explicit original-response witness

The displayed `uniformFloor` is positive at each fixed nome and width, but
its detector carries a head factor on every temporal face.  Since a literal
row supplies at least `width` temporal faces, this particular lower-witness
coefficient tends to zero with width.  The result is only an obstruction to
promoting this computed witness to a width-uniform response floor; it says
nothing about the actual response or transfer operator.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialResponseWidthObstruction

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse

def responseMarginBase : Q' := Q'.mkPos 1 32 (by decide)

private theorem costCap_ge_five {w : Q'} (hw0 : (0 : Q') < w) :
    (5 : Q') ≤ costCap hw0 := by
  have hi : (0 : Q') ≤ inverseRate hw0 := by
    unfold inverseRate
    exact Q'.le_of_lt (Q'.recipPos_pos _ _)
  unfold costCap
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 5 _ hi)
    (Q'.le_of_eqv (Q'.add_comm_eqv 5 _))

private theorem partitionScale_ge_one {w : Q'} (hw0 : (0 : Q') < w)
    (width : Nat) : (1 : Q') ≤ partitionScale w width := by
  unfold partitionScale
  exact Q'.add_le_self_of_nonneg 1 _
    (Q'.mul_nonneg _ _
      (kineticCap_nonnegative hw0 width)
      (SumOfSquares.q_mul_self_nonneg _))

private theorem responseDenominator_ge_one {w : Q'} (hw0 : (0 : Q') < w)
    (width : Nat) : (1 : Q') ≤ costCap hw0 * partitionScale w width := by
  have hc : (5 : Q') ≤ costCap hw0 := costCap_ge_five hw0
  have hp : (1 : Q') ≤ partitionScale w width := partitionScale_ge_one hw0 width
  have hmul := Q'.mul_le_mul_of_nonneg hc hp
    (Q'.le_of_lt (costCap_positive hw0)) (by decide : (0 : Q') ≤ 1)
  exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 5 * 1) hmul

theorem detectorScale_le_margin_power {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    detectorScale w width ≤ responseMarginBase ^ width := by
  have hhead0 : (0 : Q') ≤ headFloor w :=
    Q'.le_of_lt (headFloor_positive hw0 hw1)
  have hhead : headFloor w ≤ responseMarginBase :=
    headFloor_le_oneThirtySecond hw0 hw1
  have hkin : kineticFloor w width ≤
      responseMarginBase ^ (temporalFaces width).length := by
    unfold kineticFloor
    exact HKConv.pow_le_pow_base hhead0 hhead _
  have hkin' : kineticFloor w width ≤ responseMarginBase ^ width :=
    Q'.le_trans' _ _ _ hkin
      (HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ responseMarginBase)
        (by decide : responseMarginBase ≤ (1 : Q'))
        (width_le_temporalFaces_length width))
  have hsp : headFloor w ^ (spatialFaces width).length ≤ (1 : Q') :=
    HKPos.pow_le_one hhead0
      (Q'.le_trans' _ _ _ hhead (by decide : responseMarginBase ≤ (1 : Q'))) _
  have hsp0 : (0 : Q') ≤ headFloor w ^ (spatialFaces width).length :=
    Q'.le_of_lt (HKPos.pow_pos (headFloor_positive hw0 hw1) _)
  have hmul := Q'.mul_le_mul_of_nonneg hkin' hsp
    (Q'.pow_nonneg (responseMarginBase) (by decide) width)
    hsp0
  unfold detectorScale
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_one_eqv _))

theorem uniformFloor_le_margin_power_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    uniformFloor hw0 width ≤ responseMarginBase ^ (width + width) := by
  let A := detectorScale w width
  let D := costCap hw0 * partitionScale w width
  have hApos : (0 : Q') < A := detectorScale_positive hw0 hw1 width
  have hA0 : (0 : Q') ≤ A := Q'.le_of_lt hApos
  have hDpos : (0 : Q') < D :=
    Q'.mul_pos (costCap_positive hw0) (partitionScale_positive hw0 width)
  have hD : (1 : Q') ≤ D := responseDenominator_ge_one hw0 width
  have hsqD : A*A ≤ (A*A)*D := by
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hD
        (Q'.mul_nonneg _ _ hA0 hA0))
  have hfloor : uniformFloor hw0 width ≤ A*A := by
    change Q'.divPos (A*A) D hDpos ≤ A*A
    exact Q'.divPos_le_of_le_mul (A*A) D hDpos hsqD
  have hdet := detectorScale_le_margin_power hw0 hw1 width
  have hsq : A*A ≤ responseMarginBase^width * responseMarginBase^width :=
    Q'.mul_le_mul_of_nonneg hdet hdet
      (Q'.pow_nonneg responseMarginBase (by decide) width) hA0
  exact Q'.le_trans' _ _ _ hfloor
    (Q'.le_trans' _ _ _ hsq
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.pow_add_eqv responseMarginBase width width))))

def responseWidthModulus (epsilon : Q') : Nat :=
  HKConvGen.powBaseCutoff responseMarginBase epsilon

theorem uniformFloor_le_epsilon {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (width : Nat)
    (hwidth : responseWidthModulus epsilon ≤ width) :
    uniformFloor hw0 width ≤ epsilon := by
  have hpow := uniformFloor_le_margin_power_square hw0 hw1 width
  have hcut : responseWidthModulus epsilon ≤ width + width := by omega
  exact Q'.le_trans' _ _ _ hpow
    (Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ responseMarginBase)
        (by decide : responseMarginBase ≤ (1 : Q')) hcut)
      (HKConvGen.pow_base_le_cutoff (by decide : (0 : Q') < responseMarginBase)
        (by decide : responseMarginBase < (1 : Q')) he))

theorem no_width_uniform_uniformFloor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (rho : Q')
    (hrho : (0 : Q') < rho) :
    ¬ (∀ width, 0 < width → rho ≤ uniformFloor hw0 width) := by
  intro h
  let epsilon := HalfPow.half * rho
  have he : (0 : Q') < epsilon := ExpNeg.half_mul_pos _ hrho
  let width := responseWidthModulus epsilon + 1
  have hf := uniformFloor_le_epsilon hw0 hw1 epsilon he width (Nat.le_succ _)
  have hr := h width (Nat.succ_pos _)
  have hbad : rho ≤ epsilon := Q'.le_trans' _ _ _ hr hf
  have hlt : epsilon < rho := ClusteringImpliesGap.lt_of_lt_of_le
    (ClusteringImpliesGap.mul_lt_mul_of_pos_right hrho
      (by decide : HalfPow.half < (1 : Q')))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Int.not_lt.mpr hbad hlt

end YMGap.Continuum.BF4ExactSlabFixedSpatialResponseWidthObstruction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseWidthObstruction.responseMarginBase
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseWidthObstruction.detectorScale_le_margin_power
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseWidthObstruction.uniformFloor_le_margin_power_square
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseWidthObstruction.responseWidthModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseWidthObstruction.uniformFloor_le_epsilon
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseWidthObstruction.no_width_uniform_uniformFloor
