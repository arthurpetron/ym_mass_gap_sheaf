/-
# Complete finite connected Cayley trace-source R6

The connected order-six coefficient for two Cayley trace-source insertions is

  Cov(A4,B2) + Cov(A2,B4) + Cov(A3,B3)
    - kappa(A3,B2,V3) - kappa(A2,B3,V3)
    + kappa(A2,B2,V3^2/2 - V4 + J2).

Every component on the right now has an exact finite Wick compiler on the
same open-cube rooted-comb/Heron carrier.  This leaf supplies the literal
signed assembly and pays the factor sixteen in the final density term coming
from `A2=4*bulkSourceHeronRadialSquare` in both source slots.

This is the complete connected finite FREE coefficient `R6`.  It does not
include OWN-normalization means, supplied OLD-center residual products, a
higher remainder, ORIGINAL-law comparison, a uniform estimate or a physical
mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceMixedCubicActionCumulant
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceConnectedR6

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceMixedCubicActionCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Exact trace-source-scaled connected value of the complete finite second
density.  Each `A2` contributes its literal factor four. -/
def openCubeBulkCayleyTraceSecondDensityWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  4 * (4 * openCubeBulkCompleteSecondDensityWickSum
    timeBonds side sidePositive stage leftTime rightTime)

/-- The complete second-density insertion against the two literal trace
source quadratics is the checked bulk-source value with both factors four
retained. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_completeSecondDensity_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeSecondDensityPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceSecondDensityWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let left := bulkSourceHeronRadialSquare
    timeBonds side sidePositive stage leftTime
  let right := bulkSourceHeronRadialSquare
    timeBonds side sidePositive stage rightTime
  let density := completeOpenCubeSecondDensityPolynomial
    timeBonds (bulkSourceWidth side) stage
  let baseValue := openCubeBulkCompleteSecondDensityWickSum
    timeBonds side sidePositive stage leftTime rightTime
  have base : finiteGaussianThirdCumulant N left right density ≈
      baseValue := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (finiteGaussianThirdCumulant_center_left_middle
          N 0 0 left right density))
      (finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeSecondDensity_wick
        timeBonds side sidePositive stage leftTime rightTime 0 0)
  have middleScaled :
      finiteGaussianThirdCumulant N left (polySmul 4 right) density ≈
        4 * baseValue :=
    Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_smul_middle N 4 left right density)
      (Q'.mul_eqv_congr_left 4 _ _ base)
  have bothScaled :
      finiteGaussianThirdCumulant N
          (polySmul 4 left) (polySmul 4 right) density ≈
        4 * (4 * baseValue) :=
    Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_smul_left N 4 left
        (polySmul 4 right) density)
      (Q'.mul_eqv_congr_left 4 _ _ middleScaled)
  unfold openCubeBulkCayleyTraceA2
    openCubeBulkCayleyTraceSecondDensityWickSum
  exact bothScaled

/-- Complete finite Wick value of the connected trace-source order-six
coefficient `R6`. -/
def openCubeBulkCayleyTraceConnectedR6WickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  (openCubeBulkCayleyTraceSourceOrderSixCovarianceWickSum
      timeBonds side sidePositive stage leftTime rightTime +
    openCubeBulkCayleyTraceSignedMixedActionWickSum
      timeBonds side sidePositive stage leftTime rightTime) +
    openCubeBulkCayleyTraceSecondDensityWickSum
      timeBonds side sidePositive stage leftTime rightTime

/-- The literal connected finite FREE `R6` is exactly the displayed signed
sum of source-source, mixed source/action and complete second-density Wick
values. -/
theorem finiteGaussian_openCube_bulk_cayley_trace_connectedR6_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    (((finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
          (openCubeBulkCayleyTraceA4
            timeBonds side sidePositive stage leftTime)
          (openCubeBulkCayleyTraceA2
            timeBonds side sidePositive stage rightTime) +
        finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
          (openCubeBulkCayleyTraceA2
            timeBonds side sidePositive stage leftTime)
          (openCubeBulkCayleyTraceA4
            timeBonds side sidePositive stage rightTime)) +
      finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage rightTime)) +
      (-finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
          (openCubeBulkCayleyTraceA3
            timeBonds side sidePositive stage leftTime)
          (openCubeBulkCayleyTraceA2
            timeBonds side sidePositive stage rightTime)
          (completeOpenCubeSpatialCubicPolynomial
            timeBonds (bulkSourceWidth side) stage) +
        -finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
          (openCubeBulkCayleyTraceA2
            timeBonds side sidePositive stage leftTime)
          (openCubeBulkCayleyTraceA3
            timeBonds side sidePositive stage rightTime)
          (completeOpenCubeSpatialCubicPolynomial
            timeBonds (bulkSourceWidth side) stage))) +
      finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeSecondDensityPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceConnectedR6WickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (finiteGaussianCovariance_openCube_bulk_cayley_trace_source_orderSix_wick
        timeBonds side sidePositive stage leftTime rightTime)
      (finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_signedMixedAction_wick
        timeBonds side sidePositive stage leftTime rightTime))
    (finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_completeSecondDensity_wick
      timeBonds side sidePositive stage leftTime rightTime)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceConnectedR6

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceConnectedR6.finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_completeSecondDensity_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceConnectedR6.finiteGaussian_openCube_bulk_cayley_trace_connectedR6_wick
