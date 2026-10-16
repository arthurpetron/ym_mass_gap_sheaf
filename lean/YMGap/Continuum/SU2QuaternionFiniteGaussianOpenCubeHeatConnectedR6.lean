/-
# Complete connected heat-normalized Cayley trace-source R6

The connected order-six coefficient on the corrected `(2L)^{-1}` carrier is
the sum of the complete source-source covariance, the two signed mixed
source/action cumulants, and the complete second-density cumulant.  Every
component already uses the literal heat trace-source coefficients and the
same finite heat Heron rows, so this leaf performs only their exact assembly.

This is the complete connected finite FREE `R6`.  OWN normalization, supplied
OLD-center residual products, ORIGINAL-law comparison, a uniform sign, higher
remainders and continuum/Clay conclusions remain open.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSourceOrderSixCumulants

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatConnectedR6

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSourceOrderSixCumulants

local infix:50 " ≈ " => Q'.eqv

/-- Complete finite Wick value of corrected connected trace-source `R6`. -/
def openCubeHeatCayleyTraceConnectedR6WickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  (openCubeHeatCayleyTraceSourceOrderSixCovarianceWickSum
      timeBonds side sidePositive stage leftTime rightTime +
    openCubeHeatCayleyTraceSignedMixedActionWickSum
      timeBonds side sidePositive stage leftTime rightTime) +
    openCubeHeatCayleyTraceCompleteSecondDensityWickSum
      timeBonds side sidePositive stage leftTime rightTime

/-- Exact connected finite FREE `R6` on the corrected heat carrier. -/
theorem finiteGaussian_openCubeHeat_cayleyTrace_connectedR6_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    (((finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
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
          timeBonds side sidePositive stage rightTime)) +
      (-finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
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
            timeBonds (bulkSourceWidth side) stage))) +
      finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatSecondDensityPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceConnectedR6WickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (finiteGaussianCovariance_openCubeHeat_cayleyTrace_sourceOrderSix_wick
        timeBonds side sidePositive stage leftTime rightTime)
      (finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_signedMixedAction_wick
        timeBonds side sidePositive stage leftTime rightTime))
    (finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_completeSecondDensity_wick
      timeBonds side sidePositive stage leftTime rightTime)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatConnectedR6

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatConnectedR6.finiteGaussian_openCubeHeat_cayleyTrace_connectedR6_wick
