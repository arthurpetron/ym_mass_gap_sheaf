/-
# Complete heat-normalized finite second-density response

This leaf assembles the corrected-carrier second density

  V3^2/2 - V4_spatial - V4_kinetic + J2

from the four component polynomials and their already checked connected Wick
responses.  All components use the same `(2L)^{-1}` heat Heron rows and the
actual heat-normalized trace-source quadratics `A2(left),A2(right)`.

The result is only a finite FREE connected insertion on the corrected carrier.
It does not yet add source-source or mixed source/action order-six terms,
construct OWN/OLD coefficients, compare the ORIGINAL law, prove a uniform
sign, control higher remainders, or establish a continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatFourthActionHaarCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteSecondDensityCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatFourthActionHaarCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Literal complete second density on the corrected heat carrier. -/
def completeOpenCubeHeatSecondDensityPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polyAdd
    (completeOpenCubeHeatSpatialCubicPairPolynomial timeBonds width stage)
    (polyAdd
      (polySmul (-1)
        (completeOpenCubeHeatSpatialFourthActionPolynomial
          timeBonds width stage))
      (polyAdd
        (polySmul (-1)
          (completeOpenCubeHeatKineticFourthActionPolynomial
            timeBonds width stage))
        (completeOpenCubeHeatCayleyHaarJ2Polynomial
          timeBonds width stage)))

/-- Exact assembled connected value of the corrected complete second density. -/
def openCubeHeatCayleyTraceCompleteSecondDensityWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  openCubeHeatCayleyTraceCompleteSpatialCubicPairWickSum
      timeBonds side sidePositive stage leftTime rightTime +
    ((-1) *
      openCubeHeatCayleyTraceSpatialFourthActionWickSum
        timeBonds side sidePositive stage leftTime rightTime +
      ((-1) *
        openCubeHeatCayleyTraceKineticFourthActionWickSum
          timeBonds side sidePositive stage leftTime rightTime +
        openCubeHeatCayleyTraceHaarJ2TriangleSum
          timeBonds side sidePositive stage leftTime rightTime))

/-- Exact signed assembly of the complete corrected second-density response. -/
theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_completeSecondDensity_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatSecondDensityPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceCompleteSecondDensityWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let left := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let cubic := completeOpenCubeHeatSpatialCubicPairPolynomial
    timeBonds (bulkSourceWidth side) stage
  let spatial := completeOpenCubeHeatSpatialFourthActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  let kinetic := completeOpenCubeHeatKineticFourthActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  let haar := completeOpenCubeHeatCayleyHaarJ2Polynomial
    timeBonds (bulkSourceWidth side) stage
  have hcubic : finiteGaussianThirdCumulant noiseCount left right cubic ≈
      openCubeHeatCayleyTraceCompleteSpatialCubicPairWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
    exact finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_completeSpatialCubicPair_wick
      timeBonds side sidePositive stage leftTime rightTime
  have hspatialBase : finiteGaussianThirdCumulant noiseCount left right spatial ≈
      openCubeHeatCayleyTraceSpatialFourthActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
    exact finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_spatialFourthAction_wick
      timeBonds side sidePositive stage leftTime rightTime
  have hspatial : finiteGaussianThirdCumulant noiseCount left right
        (polySmul (-1) spatial) ≈
      (-1) * openCubeHeatCayleyTraceSpatialFourthActionWickSum
        timeBonds side sidePositive stage leftTime rightTime :=
    Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_smul_right
        noiseCount (-1) left right spatial)
      (Q'.mul_eqv_congr_left (-1) _ _ hspatialBase)
  have hkineticBase : finiteGaussianThirdCumulant noiseCount left right kinetic ≈
      openCubeHeatCayleyTraceKineticFourthActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
    exact finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_kineticFourthAction_wick
      timeBonds side sidePositive stage leftTime rightTime
  have hkinetic : finiteGaussianThirdCumulant noiseCount left right
        (polySmul (-1) kinetic) ≈
      (-1) * openCubeHeatCayleyTraceKineticFourthActionWickSum
        timeBonds side sidePositive stage leftTime rightTime :=
    Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_smul_right
        noiseCount (-1) left right kinetic)
      (Q'.mul_eqv_congr_left (-1) _ _ hkineticBase)
  have hhaar : finiteGaussianThirdCumulant noiseCount left right haar ≈
      openCubeHeatCayleyTraceHaarJ2TriangleSum
        timeBonds side sidePositive stage leftTime rightTime := by
    exact finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_haarJ2_triangle
      timeBonds side sidePositive stage leftTime rightTime
  have hsplitCubic := finiteGaussianThirdCumulant_add_right
    noiseCount left right cubic
      (polyAdd (polySmul (-1) spatial)
        (polyAdd (polySmul (-1) kinetic) haar))
  have hsplitSpatial := finiteGaussianThirdCumulant_add_right
    noiseCount left right (polySmul (-1) spatial)
      (polyAdd (polySmul (-1) kinetic) haar)
  have hsplitKinetic := finiteGaussianThirdCumulant_add_right
    noiseCount left right (polySmul (-1) kinetic) haar
  unfold completeOpenCubeHeatSecondDensityPolynomial
    openCubeHeatCayleyTraceCompleteSecondDensityWickSum
  exact Q'.eqv_trans _ _ _ hsplitCubic
    (Q'.add_eqv_congr' hcubic
      (Q'.eqv_trans _ _ _ hsplitSpatial
        (Q'.add_eqv_congr' hspatial
          (Q'.eqv_trans _ _ _ hsplitKinetic
            (Q'.add_eqv_congr' hkinetic hhaar)))))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteSecondDensityCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteSecondDensityCumulant.finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_completeSecondDensity_wick
