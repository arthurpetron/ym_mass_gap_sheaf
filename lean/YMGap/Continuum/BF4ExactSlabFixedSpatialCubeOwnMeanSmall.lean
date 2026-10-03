/-
# A constructed small OWN mean in the original depth-zero odd law

At the explicitly bounded first coefficient, the literal original odd
partition is at least 959/1024 and its bent numerator has absolute value
at most 130/1024. Division uses that constructed positive partition.
The resulting center is the ORIGINAL odd ratio, not bare Haar centering,
and is bounded by 1/4. This is a cutoff-one, width-two finite pilot; it
supplies neither a changing-family estimate nor continuum survival.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddMomentPin
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (bentObservable)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddMomentPin
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (bent_haar_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial (mean)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local infix:50 " ≈ " => Q'.eqv
local notation "N" => List.length (baseLinks 2)
local notation:max "H" p:arg => quaternionHaar N p
attribute [local irreducible] baseLinks bentObservable cubeOddBackground oddPartition oddNumerator

def backgroundCap : Q' := Q'.mkPos 65 1024 (by decide)
def partitionFloor : Q' := Q'.mkPos 959 1024 (by decide)
def numeratorCap : Q' := Q'.mkPos 130 1024 (by decide)
def meanCap : Q' := Q'.mkPos 1 4 (by decide)

/-- All six shared-variable factors and the ORIGINAL vacuum are retained. -/
theorem cubeOddBackgroundCap_le (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) : cubeOddBackgroundCap w ≤ backgroundCap := by
  have hd := cubeFundamentalDelta_le_cap w ha hα
  have hd0 := cubeFundamentalDelta_nonnegative w ha
  have hsq : cubeFundamentalDelta w * cubeFundamentalDelta w ≤ deltaCap * deltaCap :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hd hd0)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hd (by decide))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.add_le_add hd hd) hsq) (by decide)

private theorem haar_one : H polyOne ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem background_remainder_haar (w : Q') :
    H (cubeOddBackgroundRemainder w) + 1 ≈ H (cubeOddBackground w) := by
  have hp : RatPolyCoeffEqv
      (polyAdd (cubeOddBackgroundRemainder w) polyOne) (cubeOddBackground w) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.const 1))) (.const 1)) (.var 0)
      (by decide) (fun _ => cubeOddBackground w)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm haar_one))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append N _ _)) (haar_of_coeff hp))

private theorem background_bent_remainder_haar (w : Q') :
    H (polyMul (cubeOddBackgroundRemainder w) bentObservable) ≈
      H (polyMul (cubeOddBackground w) bentObservable) := by
  have hp : RatPolyCoeffEqv
      (polyAdd (polyMul (cubeOddBackgroundRemainder w) bentObservable) bentObservable)
      (polyMul (cubeOddBackground w) bentObservable) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 0) (.neg (.const 1))) (.var 1)) (.var 1))
      (.mul (.var 0) (.var 1)) (by decide)
      (fun | 0 => cubeOddBackground w | _ => bentObservable)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _).symm)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm bent_haar_zero))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append N _ _)) (haar_of_coeff hp)))

/-- Constructed lower bound on the ORIGINAL odd partition, not the even one. -/
theorem oddPartition_floor (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) : partitionFloor ≤ oddPartition w := by
  let R := cubeOddBackgroundInterval w ha (directKernelGuard_of_coeffW_cap w hα)
  have hab : Q'.abs (H (cubeOddBackgroundRemainder w)) ≤ backgroundCap :=
    Q'.le_trans' _ _ _ R.haar_bound (cubeOddBackgroundCap_le w ha hα)
  have hl : -backgroundCap ≤ H (cubeOddBackgroundRemainder w) :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) hab))
      (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  have he : H (cubeOddBackgroundRemainder w) + 1 ≈ oddPartition w :=
    Q'.eqv_trans _ _ _ (background_remainder_haar w)
      (Q'.eqv_symm (oddPartition_background_pin w))
  exact Q'.le_trans' _ _ _ (by decide : partitionFloor ≤ -backgroundCap + 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ 1 hl) (Q'.le_of_eqv he))

theorem oddPartition_positive (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) : (0 : Q') < oddPartition w :=
  HeatKernelRGStep.lt_of_lt_of_le (by decide : (0 : Q') < partitionFloor)
    (oddPartition_floor w ha hα)

/-- Actual interacting numerator, with bare zero used only after paying the
full original odd-background remainder. -/
theorem oddNumerator_abs_le (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) : Q'.abs (oddNumerator w) ≤ numeratorCap := by
  let R := cubeOddBackgroundInterval w ha (directKernelGuard_of_coeffW_cap w hα)
  have h := (R.mul bentObservableInterval).haar_bound
  have hp : H (polyMul (cubeOddBackgroundRemainder w) bentObservable) ≈ oddNumerator w :=
    Q'.eqv_trans _ _ _ (background_bent_remainder_haar w)
      (Q'.eqv_symm (oddNumerator_background_pin w))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hp))
    (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ 2 (cubeOddBackgroundCap_le w ha hα) (by decide))
      (by decide)))

/-- The actual original odd ratio, with its OWN positive partition constructed
above. No `headCutoff` positivity premise or substitute cube mean is used. -/
def originalOddMean (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) : Q' :=
  Q'.divPos (oddNumerator w) (oddPartition w) (oddPartition_positive w ha hα)

theorem originalOddMean_bounds (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) :
    -meanCap ≤ originalOddMean w ha hα ∧ originalOddMean w ha hα ≤ meanCap := by
  have hN := oddNumerator_abs_le w ha hα
  have hZ := oddPartition_floor w ha hα
  have hupper : oddNumerator w ≤ meanCap * oddPartition w :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ hN (Q'.le_trans' _ _ _
        (by decide : numeratorCap ≤ meanCap * partitionFloor)
        (Q'.mul_le_mul_of_nonneg_left _ _ meanCap hZ (by decide))))
  have hlower : -meanCap * oddPartition w ≤ oddNumerator w := by
    have hneg : -(oddNumerator w) ≤ meanCap * oddPartition w :=
      Q'.le_trans' _ _ _ (Q'.neg_le_abs _)
        (Q'.le_trans' _ _ _ hN (Q'.le_trans' _ _ _
          (by decide : numeratorCap ≤ meanCap * partitionFloor)
          (Q'.mul_le_mul_of_nonneg_left _ _ meanCap hZ (by decide))))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_mul_eqv _ _))
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg hneg) (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
  exact ⟨Q'.le_divPos_of_mul_le _ _ (oddPartition_positive w ha hα) hlower,
    Q'.divPos_le_of_le_mul _ _ (oddPartition_positive w ha hα) hupper⟩

theorem originalOddMean_abs_le (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) : Q'.abs (originalOddMean w ha hα) ≤ meanCap :=
  Q'.abs_le (originalOddMean_bounds w ha hα).1 (originalOddMean_bounds w ha hα).2

/-- Compatibility with the existing actual edge-law mean whenever its own
head guard is available. That guard is retained, not discharged or weakened. -/
theorem existingMean_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hhead : headCutoff w ≤ 1) (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) :
    mean hw0 hw1 1 2 hhead 0 bentObservable ≈ originalOddMean w ha hα :=
  mean_odd_ratio_pin hw0 hw1 hhead (oddPartition_positive w ha hα)

theorem existingMean_abs_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hhead : headCutoff w ≤ 1) (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) :
    Q'.abs (mean hw0 hw1 1 2 hhead 0 bentObservable) ≤ meanCap :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (existingMean_pin hw0 hw1 hhead ha hα)))
    (originalOddMean_abs_le w ha hα)

/-- A concrete positive nome inhabits the original finite mean estimate. -/
theorem smallNome_originalOddMean_bound :
    Q'.abs (originalOddMean smallNome smallNome_coeff_nonneg smallNome_coeff_le_cap) ≤ meanCap :=
  originalOddMean_abs_le smallNome smallNome_coeff_nonneg smallNome_coeff_le_cap

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.backgroundCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.partitionFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.numeratorCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.meanCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.cubeOddBackgroundCap_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.oddPartition_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.oddPartition_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.oddNumerator_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.originalOddMean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.originalOddMean_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.originalOddMean_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.existingMean_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.existingMean_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall.smallNome_originalOddMean_bound
