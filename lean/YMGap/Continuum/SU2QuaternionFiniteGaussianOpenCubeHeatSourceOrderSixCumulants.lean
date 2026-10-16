/-
# Heat-normalized source and mixed order-six cumulants

This leaf migrates the remaining source-source and mixed source/action pieces
of the connected order-six Cayley trace-source response to the corrected
`(2L)^{-1}` heat carrier.  It reduces

  Cov(A4(left),A2(right)) + Cov(A2(left),A4(right)),
  Cov(A3(left),A3(right)),
  -kappa(A3(left),A2(right),V3),
  -kappa(A2(left),A3(right),V3)

to the existing constructive finite six-row Wick compilers using the actual
heat `A2,A3,A4` blocks and complete heat spatial cubic action.

This remains a finite FREE identity.  The final `R6`, OWN/OLD response,
ORIGINAL-law comparison, uniform sign, higher remainder and continuum/Clay
conclusions remain separate obligations.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteSecondDensityCumulant
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceMixedCubicActionCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSourceOrderSixCumulants

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Exact finite Wick value of the two even heat source covariances. -/
def openCubeHeatCayleyTraceEvenOrderSixCovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  finiteGaussianWeightedTwoFourCovarianceWickSum noiseCount
      (openCubeHeatBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage rightTime)
      (openCubeHeatBulkCayleyTraceA4RowBlocks
        timeBonds side sidePositive stage leftTime) +
    finiteGaussianWeightedTwoFourCovarianceWickSum noiseCount
      (openCubeHeatBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage leftTime)
      (openCubeHeatBulkCayleyTraceA4RowBlocks
        timeBonds side sidePositive stage rightTime)

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_evenOrderSix_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA4
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime) +
      finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA4
          timeBonds side sidePositive stage rightTime) ≈
      openCubeHeatCayleyTraceEvenOrderSixCovarianceWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftQuadratics := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightQuadratics := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  let leftQuartics := openCubeHeatBulkCayleyTraceA4RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightQuartics := openCubeHeatBulkCayleyTraceA4RowBlocks
    timeBonds side sidePositive stage rightTime
  have leftQuadraticCertificate := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage leftTime
  have rightQuadraticCertificate := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage rightTime
  have leftQuarticCertificate := openCubeHeatBulkCayleyTraceA4_coeffEqv
    timeBonds side sidePositive stage leftTime
  have rightQuarticCertificate := openCubeHeatBulkCayleyTraceA4_coeffEqv
    timeBonds side sidePositive stage rightTime
  have firstCovariance :
      finiteGaussianCovariance noiseCount
          (openCubeHeatBulkCayleyTraceA4
            timeBonds side sidePositive stage leftTime)
          (openCubeHeatBulkCayleyTraceA2
            timeBonds side sidePositive stage rightTime) ≈
        finiteGaussianWeightedTwoFourCovarianceWickSum
          noiseCount rightQuadratics leftQuartics := by
    exact Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv noiseCount
        leftQuarticCertificate rightQuadraticCertificate)
      (Q'.eqv_trans _ _ _
        (finiteGaussianCovariance_comm noiseCount
          (weightedTermPolynomial
            (leftQuartics.map (weightedQuarticRowBlockTerm noiseCount)))
          (weightedTermPolynomial
            (rightQuadratics.map
              (weightedQuadraticRowBlockTerm noiseCount))))
        (finiteGaussianCovariance_weighted_two_four_row_blocks_wick
          noiseCount rightQuadratics leftQuartics))
  have secondCovariance :
      finiteGaussianCovariance noiseCount
          (openCubeHeatBulkCayleyTraceA2
            timeBonds side sidePositive stage leftTime)
          (openCubeHeatBulkCayleyTraceA4
            timeBonds side sidePositive stage rightTime) ≈
        finiteGaussianWeightedTwoFourCovarianceWickSum
          noiseCount leftQuadratics rightQuartics := by
    exact Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv noiseCount
        leftQuadraticCertificate rightQuarticCertificate)
      (finiteGaussianCovariance_weighted_two_four_row_blocks_wick
        noiseCount leftQuadratics rightQuartics)
  unfold openCubeHeatCayleyTraceEvenOrderSixCovarianceWickSum
  exact Q'.add_eqv_congr' firstCovariance secondCovariance

/-- Exact finite Wick value of the heat cubic-cubic source covariance. -/
def openCubeHeatCayleyTraceCubicOrderSixCovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedThreeThreeCovarianceWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage rightTime)

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_cubicOrderSix_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage rightTime) ≈
      openCubeHeatCayleyTraceCubicOrderSixCovarianceWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftBlocks := openCubeHeatBulkCayleyTraceA3RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightBlocks := openCubeHeatBulkCayleyTraceA3RowBlocks
    timeBonds side sidePositive stage rightTime
  have leftCertificate := openCubeHeatBulkCayleyTraceA3_coeffEqv
    timeBonds side sidePositive stage leftTime
  have rightCertificate := openCubeHeatBulkCayleyTraceA3_coeffEqv
    timeBonds side sidePositive stage rightTime
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv noiseCount
      leftCertificate rightCertificate)
    (finiteGaussianCovariance_weighted_three_three_row_blocks_wick
      noiseCount leftBlocks rightBlocks)

/-- Sum of all three heat source-source order-six covariance values. -/
def openCubeHeatCayleyTraceSourceOrderSixCovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  openCubeHeatCayleyTraceEvenOrderSixCovarianceWickSum
      timeBonds side sidePositive stage leftTime rightTime +
    openCubeHeatCayleyTraceCubicOrderSixCovarianceWickSum
      timeBonds side sidePositive stage leftTime rightTime

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_sourceOrderSix_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    (finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA4
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime) +
      finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA4
          timeBonds side sidePositive stage rightTime)) +
      finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage rightTime) ≈
      openCubeHeatCayleyTraceSourceOrderSixCovarianceWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  exact Q'.add_eqv_congr'
    (finiteGaussianCovariance_openCubeHeat_cayleyTrace_evenOrderSix_wick
      timeBonds side sidePositive stage leftTime rightTime)
    (finiteGaussianCovariance_openCubeHeat_cayleyTrace_cubicOrderSix_wick
      timeBonds side sidePositive stage leftTime rightTime)

/-- Wick value of `kappa(A3(left),A2(right),V3)` on the heat carrier. -/
def openCubeHeatCayleyTraceLeftCubicMixedActionWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedThreeTwoThreeWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage rightTime)
    (completeOpenCubeHeatSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)

/-- Wick value of `kappa(A2(left),A3(right),V3)` on the heat carrier. -/
def openCubeHeatCayleyTraceRightCubicMixedActionWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedThreeTwoThreeWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage rightTime)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage leftTime)
    (completeOpenCubeHeatSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)

private theorem completeHeatActionCubicCertificate
    (timeBonds side stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeHeatSpatialCubicPolynomial
        timeBonds (bulkSourceWidth side) stage)
      (weightedTermPolynomial
        ((completeOpenCubeHeatSpatialCubicRowBlocks
          timeBonds (bulkSourceWidth side) stage).map
            (weightedCubicRowBlockTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  have noiseEquality : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) =
        bulkSourceNoiseCount timeBonds side := by
    unfold combGaugePlaquetteNoiseCount bulkSourceNoiseCount
    rfl
  rw [← noiseEquality]
  exact completeOpenCubeHeatSpatialCubicPolynomial_coeffEqv
    timeBonds (bulkSourceWidth side) stage

theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_leftCubic_mixedAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceLeftCubicMixedActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let cubicBlocks := openCubeHeatBulkCayleyTraceA3RowBlocks
    timeBonds side sidePositive stage leftTime
  let quadraticBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  let actionBlocks := completeOpenCubeHeatSpatialCubicRowBlocks
    timeBonds (bulkSourceWidth side) stage
  have cubicCertificate := openCubeHeatBulkCayleyTraceA3_coeffEqv
    timeBonds side sidePositive stage leftTime
  have quadraticCertificate := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage rightTime
  have actionCertificate := completeHeatActionCubicCertificate
    timeBonds side stage
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_coeffEqv noiseCount
      cubicCertificate quadraticCertificate actionCertificate)
    (finiteGaussianThirdCumulant_weighted_three_two_three_row_blocks_wick
      noiseCount cubicBlocks quadraticBlocks actionBlocks)

theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_rightCubic_mixedAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceRightCubicMixedActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let cubicBlocks := openCubeHeatBulkCayleyTraceA3RowBlocks
    timeBonds side sidePositive stage rightTime
  let quadraticBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let actionBlocks := completeOpenCubeHeatSpatialCubicRowBlocks
    timeBonds (bulkSourceWidth side) stage
  have cubicCertificate := openCubeHeatBulkCayleyTraceA3_coeffEqv
    timeBonds side sidePositive stage rightTime
  have quadraticCertificate := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage leftTime
  have actionCertificate := completeHeatActionCubicCertificate
    timeBonds side stage
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_swap_left_middle noiseCount
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage leftTime)
      (openCubeHeatBulkCayleyTraceA3
        timeBonds side sidePositive stage rightTime)
      (completeOpenCubeHeatSpatialCubicPolynomial
        timeBonds (bulkSourceWidth side) stage))
    (Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_coeffEqv noiseCount
        cubicCertificate quadraticCertificate actionCertificate)
      (finiteGaussianThirdCumulant_weighted_three_two_three_row_blocks_wick
        noiseCount cubicBlocks quadraticBlocks actionBlocks))

/-- Signed Wick value of both mixed heat source/action terms. -/
def openCubeHeatCayleyTraceSignedMixedActionWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  -openCubeHeatCayleyTraceLeftCubicMixedActionWickSum
      timeBonds side sidePositive stage leftTime rightTime +
    -openCubeHeatCayleyTraceRightCubicMixedActionWickSum
      timeBonds side sidePositive stage leftTime rightTime

theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_signedMixedAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    -finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) +
      -finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceSignedMixedActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  exact Q'.add_eqv_congr'
    (Q'.neg_eqv_congr _ _
      (finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_leftCubic_mixedAction_wick
        timeBonds side sidePositive stage leftTime rightTime))
    (Q'.neg_eqv_congr _ _
      (finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_rightCubic_mixedAction_wick
        timeBonds side sidePositive stage leftTime rightTime))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSourceOrderSixCumulants

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSourceOrderSixCumulants.finiteGaussianCovariance_openCubeHeat_cayleyTrace_sourceOrderSix_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSourceOrderSixCumulants.finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_signedMixedAction_wick
