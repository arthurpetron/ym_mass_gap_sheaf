/-
# Corrected heat-carrier common-action split

The quadratic part of the complete fourth action is exactly `-(2/3)S0` on
the corrected heat rows.  With the density sign, its contribution is
`+(2/3)S0`.  This leaf isolates that contribution inside OLD-centered `P6`
and splits it into the universal `(4/3)P4` term, the supplied OLD-center
residue, and the honest corrected-carrier scaling residual.

The corrected residual targets `Cov(A2,S0)=E[A2]` and
`kappa(A2,B2,S0)=2*R4`.  This file does not yet compile the residual to Gram
sums or bound it uniformly, compare the ORIGINAL law, control higher
remainders, or prove a continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse

local infix:50 " ≈ " => Q'.eqv

/-- Exact coefficient `2/3` produced by the density sign. -/
def heatActionTwoThird : Q' := Q'.mkPos 2 3 (by decide)

/-- Exact universal coefficient `4/3 = 2*(2/3)`. -/
def heatActionFourThird : Q' := 2 * heatActionTwoThird

/-- The density sign changes corrected `V4_quadratic=-(2/3)S0` into
`+(2/3)S0`. -/
theorem completeOpenCubeHeatNegativeActionQuadratic_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (polySmul (-1)
        (completeOpenCubeHeatActionQuadraticPolynomial
          timeBonds width stage))
      (polySmul heatActionTwoThird
        (completeOpenCubeHeatGaussianActionPolynomial
          timeBonds width stage)) := by
  let action := completeOpenCubeHeatGaussianActionPolynomial
    timeBonds width stage
  exact ((completeOpenCubeHeatActionQuadratic_coeffEqv
      timeBonds width stage).smul (-1)).trans
    ((RatPolyCoeffEqv.smul_assoc (-1) spatialHeatNegTwoThird action).trans
      (RatPolyCoeffEqv.smul_coefficient (by decide) action))

/-- Corrected one-point action-scaling defect. -/
def openCubeHeatCayleyTraceMeanScalingDefect
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let A2 := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage time
  let S0 := completeOpenCubeHeatGaussianActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  finiteGaussianCovariance noiseCount A2 S0 -
    openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage time

/-- Corrected connected action-scaling defect. -/
def openCubeHeatCayleyTraceConnectedScalingDefect
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let left := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let S0 := completeOpenCubeHeatGaussianActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  finiteGaussianThirdCumulant noiseCount left right S0 -
    2 * openCubeHeatCayleyTraceConnectedR4
      timeBonds side sidePositive stage leftTime rightTime

/-- Complete corrected scaling residual after extracting the universal
common-action piece from OLD-centered `P6`. -/
def openCubeHeatCayleyTraceP6ScalingResidual
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let leftMean := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime
  (openCubeHeatCayleyTraceConnectedScalingDefect
      timeBonds side sidePositive stage leftTime rightTime +
    (leftMean - oldCenter.c2) *
      openCubeHeatCayleyTraceMeanScalingDefect
        timeBonds side sidePositive stage rightTime) +
  openCubeHeatCayleyTraceMeanScalingDefect
      timeBonds side sidePositive stage leftTime *
    (rightMean - oldCenter.c2)

/-- Literal contribution of `-V4_quadratic` to the connected and OWN-mean
slots of corrected `P6`. -/
def openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let left := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let densityQuadratic := polySmul (-1)
    (completeOpenCubeHeatActionQuadraticPolynomial
      timeBonds (bulkSourceWidth side) stage)
  let leftMean := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime
  (finiteGaussianThirdCumulant noiseCount left right densityQuadratic +
    (leftMean - oldCenter.c2) *
      finiteGaussianCovariance noiseCount right densityQuadratic) +
  finiteGaussianCovariance noiseCount left densityQuadratic *
    (rightMean - oldCenter.c2)

/-- The same contribution expressed as `(2/3)S0`. -/
def openCubeHeatCayleyTraceGaussianActionP6Contribution
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let left := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let S0 := completeOpenCubeHeatGaussianActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  let leftMean := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime
  (heatActionTwoThird *
      finiteGaussianThirdCumulant noiseCount left right S0 +
    (leftMean - oldCenter.c2) *
      (heatActionTwoThird * finiteGaussianCovariance noiseCount right S0)) +
  (heatActionTwoThird * finiteGaussianCovariance noiseCount left S0) *
    (rightMean - oldCenter.c2)

theorem openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_action
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceGaussianActionP6Contribution
        timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let left := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let densityQuadratic := polySmul (-1)
    (completeOpenCubeHeatActionQuadraticPolynomial
      timeBonds (bulkSourceWidth side) stage)
  let S0 := completeOpenCubeHeatGaussianActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  have hdensity : RatPolyCoeffEqv densityQuadratic
      (polySmul heatActionTwoThird S0) :=
    completeOpenCubeHeatNegativeActionQuadratic_coeffEqv
      timeBonds (bulkSourceWidth side) stage
  have hconnected :
      finiteGaussianThirdCumulant noiseCount left right densityQuadratic ≈
        heatActionTwoThird *
          finiteGaussianThirdCumulant noiseCount left right S0 :=
    Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_coeffEqv noiseCount
        (RatPolyCoeffEqv.refl left) (RatPolyCoeffEqv.refl right) hdensity)
      (finiteGaussianThirdCumulant_smul_right
        noiseCount heatActionTwoThird left right S0)
  have hleft : finiteGaussianCovariance noiseCount left densityQuadratic ≈
      heatActionTwoThird * finiteGaussianCovariance noiseCount left S0 :=
    Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv noiseCount
        (RatPolyCoeffEqv.refl left) hdensity)
      (finiteGaussianCovariance_smul_right
        noiseCount heatActionTwoThird left S0)
  have hright : finiteGaussianCovariance noiseCount right densityQuadratic ≈
      heatActionTwoThird * finiteGaussianCovariance noiseCount right S0 :=
    Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv noiseCount
        (RatPolyCoeffEqv.refl right) hdensity)
      (finiteGaussianCovariance_smul_right
        noiseCount heatActionTwoThird right S0)
  unfold openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
    openCubeHeatCayleyTraceGaussianActionP6Contribution
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr' hconnected
      (Q'.mul_eqv_congr_left _ _ _ hright))
    (Q'.mul_eqv_congr_right _ _ _ hleft)

private theorem heatP6_decomposition_scalar
    (scale connected third leftMean rightMean leftAction rightAction old : Q') :
    ((scale * third +
          (leftMean - old) * (scale * rightAction)) +
        (scale * leftAction) * (rightMean - old)) ≈
      (((2 * scale) *
            (connected + (leftMean - old) * (rightMean - old)) +
          (scale * old) *
            ((leftMean - old) + (rightMean - old))) +
        scale *
          (((third - 2 * connected) +
              (leftMean - old) * (rightAction - rightMean)) +
            (leftAction - leftMean) * (rightMean - old))) := by
  let S : PolyExpr := .var 0
  let R : PolyExpr := .var 1
  let K : PolyExpr := .var 2
  let A : PolyExpr := .var 3
  let B : PolyExpr := .var 4
  let X : PolyExpr := .var 5
  let Y : PolyExpr := .var 6
  let C : PolyExpr := .var 7
  exact poly_identity_of_normal_eq
    (.add
      (.add (.mul S K)
        (.mul (.add A (.neg C)) (.mul S Y)))
      (.mul (.mul S X) (.add B (.neg C))))
    (.add
      (.add
        (.mul (.mul (.const 2) S)
          (.add R (.mul (.add A (.neg C)) (.add B (.neg C)))))
        (.mul (.mul S C)
          (.add (.add A (.neg C)) (.add B (.neg C)))))
      (.mul S
        (.add
          (.add
            (.add K (.neg (.mul (.const 2) R)))
            (.mul (.add A (.neg C)) (.add Y (.neg B))))
          (.mul (.add X (.neg A)) (.add B (.neg C))))))
    (by decide) (fun
      | 0 => scale
      | 1 => connected
      | 2 => third
      | 3 => leftMean
      | 4 => rightMean
      | 5 => leftAction
      | 6 => rightAction
      | _ => old)

/-- Exact corrected common-action split. -/
theorem openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_decomposition
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      ((heatActionFourThird *
            openCubeHeatCayleyTraceP4
              timeBonds side sidePositive stage leftTime rightTime oldCenter +
          (heatActionTwoThird * oldCenter.c2) *
            ((openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage leftTime - oldCenter.c2) +
              (openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage rightTime - oldCenter.c2))) +
        heatActionTwoThird *
          openCubeHeatCayleyTraceP6ScalingResidual
            timeBonds side sidePositive stage leftTime rightTime oldCenter) := by
  refine Q'.eqv_trans _ _ _
    (openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_action
      timeBonds side sidePositive stage leftTime rightTime oldCenter) ?_
  unfold openCubeHeatCayleyTraceGaussianActionP6Contribution
    openCubeHeatCayleyTraceP6ScalingResidual
    openCubeHeatCayleyTraceConnectedScalingDefect
    openCubeHeatCayleyTraceMeanScalingDefect
    openCubeHeatCayleyTraceP4 heatActionFourThird
  exact heatP6_decomposition_scalar
    heatActionTwoThird
    (openCubeHeatCayleyTraceConnectedR4
      timeBonds side sidePositive stage leftTime rightTime)
    (finiteGaussianThirdCumulant
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage leftTime)
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage rightTime)
      (completeOpenCubeHeatGaussianActionPolynomial
        timeBonds (bulkSourceWidth side) stage))
    (openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage rightTime)
    (finiteGaussianCovariance
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage leftTime)
      (completeOpenCubeHeatGaussianActionPolynomial
        timeBonds (bulkSourceWidth side) stage))
    (finiteGaussianCovariance
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage rightTime)
      (completeOpenCubeHeatGaussianActionPolynomial
        timeBonds (bulkSourceWidth side) stage))
    oldCenter.c2

/-- The universal corrected `(4/3)P4` piece cancels in every cleared
two-response comparison. -/
theorem openCubeHeatCayleyTraceCommonP4_cleared_zero
    (first second : Q') :
    second * (heatActionFourThird * first) -
        first * (heatActionFourThird * second) ≈ 0 := by
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.var 1) (.mul (.var 2) (.var 0)))
      (.neg (.mul (.var 0) (.mul (.var 2) (.var 1)))))
    (.const 0) (by decide) (fun
      | 0 => first
      | 1 => second
      | _ => heatActionFourThird)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction.completeOpenCubeHeatNegativeActionQuadratic_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction.openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_decomposition
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction.openCubeHeatCayleyTraceCommonP4_cleared_zero
