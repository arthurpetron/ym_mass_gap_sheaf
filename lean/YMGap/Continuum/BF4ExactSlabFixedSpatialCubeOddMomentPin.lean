/-
# Literal original odd cube moments

The odd partition and numerator retain the original vacuum message U=T1.
The seven-moment theorem first pays original transfer/action restriction;
supported testing then returns the original U inside the cube background.
Raw original message locality is never assumed. The optional mean pin keeps
the existing OWN mean and its head guard, not a new cube center.
No positivity, mean bound, gain sign or scaling estimate is proved here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddMomentPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence (heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval (cubeOddBackground)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial (mean mean_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation "N" => List.length (baseLinks 2)
attribute [local irreducible] baseLinks cubeWeight cubeTransfer bentObservable transferStep weightedMass
  terminalMessage
  YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.kineticWeight
  YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.spatialWeight

/-- The original odd partition at cutoff one, width two, terminal depth zero. -/
def oddPartition (w : Q') : Q' :=
  weightedMass w 1 2 (transferStep w 1 2 polyOne)

/-- Its original bent-loop numerator, with exactly the same U and weight. -/
def oddNumerator (w : Q') : Q' :=
  weightedMass w 1 2 (polyMul bentObservable (transferStep w 1 2 polyOne))

private theorem cubeWeight_supported (w : Q') : SupportedQuaternionBlocks N (cubeWeight w 1) := by
  unfold cubeWeight
  exact heatProduct_supported w 1 2 cubeFaces

theorem oddPartition_background_pin (w : Q') :
    oddPartition w ≈ quaternionHaar N (cubeOddBackground w) := by
  have h := (original_seven_bent_moments_cube w 1).1
  change weightedMass w 1 2 (polyMul polyOne (transferStep w 1 2 polyOne)) ≈
    quaternionHaar N (polyMul (cubeWeight w 1) (polyMul polyOne (cubeTransfer w 1 polyOne))) at h
  have hleft := weightedMass_congr w 1 2 (RatPolyCoeffEqv.one_mul (transferStep w 1 2 polyOne))
  have hright := haar_of_coeff (blocks := N) ((RatPolyCoeffEqv.refl (cubeWeight w 1)).mul
    (RatPolyCoeffEqv.one_mul (cubeTransfer w 1 polyOne)))
  have ht := original_vacuum_message_cube w 1 (cubeWeight w 1) (cubeWeight_supported w)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _ hright (Q'.eqv_symm ht)))

theorem oddNumerator_background_pin (w : Q') :
    oddNumerator w ≈ quaternionHaar N (polyMul (cubeOddBackground w) bentObservable) := by
  have h := (original_seven_bent_moments_cube w 1).2.1
  change weightedMass w 1 2 (polyMul bentObservable (transferStep w 1 2 polyOne)) ≈
    quaternionHaar N (polyMul (cubeWeight w 1) (polyMul bentObservable (cubeTransfer w 1 polyOne))) at h
  have ht := original_vacuum_message_cube w 1 (polyMul (cubeWeight w 1) bentObservable)
    (supported_polyMul (cubeWeight_supported w) bentObservable_supported)
  have hs := haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_assoc (cubeWeight w 1) bentObservable
    (cubeTransfer w 1 polyOne))
  have hr : RatPolyCoeffEqv
      (polyMul (polyMul (cubeWeight w 1) bentObservable) (transferStep w 1 2 polyOne))
      (polyMul (cubeOddBackground w) bentObservable) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).trans
      (((RatPolyCoeffEqv.refl _).mul (RatPolyCoeffEqv.mul_comm _ _)).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hs)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm ht) (haar_of_coeff hr)))

/-- Compatibility with the existing original OWN edge mean, including its
actual head guard. Positivity here is supplied only for this SAME odd mass. -/
theorem mean_odd_ratio_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hhead : headCutoff w ≤ 1) (hZ : (0 : Q') < oddPartition w) :
    mean hw0 hw1 1 2 hhead 0 bentObservable ≈
      oddNumerator w * Q'.recipPos (oddPartition w) hZ := by
  have hzero : terminalMessage w 1 2 0 = polyOne := by
    unfold terminalMessage
    rfl
  have hone : terminalMessage w 1 2 1 = transferStep w 1 2 polyOne := by
    simpa only [hzero] using (terminalMessage_next w 1 2 0).symm
  have ht0 : RatPolyCoeffEqv (terminalMessage w 1 2 0) polyOne := by
    rw [hzero]
    exact RatPolyCoeffEqv.refl _
  have ht1 : RatPolyCoeffEqv (terminalMessage w 1 2 1) (transferStep w 1 2 polyOne) := by
    rw [hone]
    exact RatPolyCoeffEqv.refl _
  have hn : weightedMass w 1 2
      (polyMul (polyMul (terminalMessage w 1 2 1) bentObservable) (terminalMessage w 1 2 0)) ≈
      oddNumerator w := weightedMass_congr w 1 2
    ((((ht1.mul (RatPolyCoeffEqv.refl bentObservable)).mul ht0).trans
      (RatPolyCoeffEqv.mul_one (polyMul (transferStep w 1 2 polyOne) bentObservable))).trans
      (RatPolyCoeffEqv.mul_comm (transferStep w 1 2 polyOne) bentObservable))
  have hz : weightedMass w 1 2
      (polyMul (terminalMessage w 1 2 1) (terminalMessage w 1 2 0)) ≈
      oddPartition w := weightedMass_congr w 1 2
    ((ht1.mul ht0).trans (RatPolyCoeffEqv.mul_one (transferStep w 1 2 polyOne)))
  have hm : middleRatio hw0 hw1 1 2 hhead 1 0 bentObservable ≈
      oddNumerator w * Q'.recipPos (oddPartition w) hZ := by
    unfold middleRatio massRatio
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hn)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _ _ hZ hz))
  exact Q'.eqv_trans _ _ _ (mean_pin hw0 hw1 1 2 hhead 0 bentObservable_supported) hm

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddMomentPin

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddMomentPin.oddPartition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddMomentPin.oddNumerator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddMomentPin.oddPartition_background_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddMomentPin.oddNumerator_background_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddMomentPin.mean_odd_ratio_pin
