/-
# Actual open-cube mixed Cayley source/action cumulants

The order-six trace-source response contains the two mixed connected terms

  -kappa(A3(left), A2(right), V3)
  -kappa(A2(left), A3(right), V3),

where `V3` is the TOTAL spatial action cubic over every history slice and
internal spatial face.  This leaf applies the checked `3+2+3` compiler to the
exact Cayley trace-source blocks and the complete open-cube action blocks.

The output is an exact finite FREE reference-Gaussian identity.  It does not
yet assemble the complete `R6`, attach OWN/OLD mean residuals, control a
higher remainder, compare the ORIGINAL law, or prove a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceMixedCubicActionCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Wick value of `kappa(A3(left),A2(right),V3)`. -/
def openCubeBulkCayleyTraceLeftCubicMixedActionWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedThreeTwoThreeWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage leftTime)
    (openCubeBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage rightTime)
    (completeOpenCubeSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)

/-- Wick value of `kappa(A2(left),A3(right),V3)`, compiled after the checked
first-two-slot cumulant symmetry. -/
def openCubeBulkCayleyTraceRightCubicMixedActionWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedThreeTwoThreeWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage rightTime)
    (openCubeBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage leftTime)
    (completeOpenCubeSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)

private theorem completeActionCubicCertificate
    (timeBonds side stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeSpatialCubicPolynomial
        timeBonds (bulkSourceWidth side) stage)
      (weightedTermPolynomial
        ((completeOpenCubeSpatialCubicRowBlocks
          timeBonds (bulkSourceWidth side) stage).map
            (weightedCubicRowBlockTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  have noiseEquality : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) =
        bulkSourceNoiseCount timeBonds side := by
    unfold combGaugePlaquetteNoiseCount bulkSourceNoiseCount
    rfl
  rw [← noiseEquality]
  exact completeOpenCubeSpatialCubicPolynomial_coeffEqv
    timeBonds (bulkSourceWidth side) stage

/-- The first literal mixed cumulant is exactly its complete finite weighted
`3+2+3` Wick sum. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_leftCubic_mixedAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceLeftCubicMixedActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let cubicBlocks := openCubeBulkCayleyTraceA3RowBlocks
    timeBonds side sidePositive stage leftTime
  let quadraticBlocks := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  let actionBlocks := completeOpenCubeSpatialCubicRowBlocks
    timeBonds (bulkSourceWidth side) stage
  have cubicCertificate := openCubeBulkCayleyTraceA3_coeffEqv
    timeBonds side sidePositive stage leftTime
  have quadraticCertificate := openCubeBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage rightTime
  have actionCertificate := completeActionCubicCertificate
    timeBonds side stage
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_coeffEqv N
      cubicCertificate quadraticCertificate actionCertificate)
    (finiteGaussianThirdCumulant_weighted_three_two_three_row_blocks_wick
      N cubicBlocks quadraticBlocks actionBlocks)

/-- The second literal mixed cumulant is exactly its complete finite weighted
`3+2+3` Wick sum. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_rightCubic_mixedAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceRightCubicMixedActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let cubicBlocks := openCubeBulkCayleyTraceA3RowBlocks
    timeBonds side sidePositive stage rightTime
  let quadraticBlocks := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let actionBlocks := completeOpenCubeSpatialCubicRowBlocks
    timeBonds (bulkSourceWidth side) stage
  have cubicCertificate := openCubeBulkCayleyTraceA3_coeffEqv
    timeBonds side sidePositive stage rightTime
  have quadraticCertificate := openCubeBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage leftTime
  have actionCertificate := completeActionCubicCertificate
    timeBonds side stage
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_swap_left_middle N
      (openCubeBulkCayleyTraceA2
        timeBonds side sidePositive stage leftTime)
      (openCubeBulkCayleyTraceA3
        timeBonds side sidePositive stage rightTime)
      (completeOpenCubeSpatialCubicPolynomial
        timeBonds (bulkSourceWidth side) stage))
    (Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_coeffEqv N
        cubicCertificate quadraticCertificate actionCertificate)
      (finiteGaussianThirdCumulant_weighted_three_two_three_row_blocks_wick
        N cubicBlocks quadraticBlocks actionBlocks))

/-- Signed finite Wick value of both mixed action terms in `R6`. -/
def openCubeBulkCayleyTraceSignedMixedActionWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  -openCubeBulkCayleyTraceLeftCubicMixedActionWickSum
      timeBonds side sidePositive stage leftTime rightTime +
    -openCubeBulkCayleyTraceRightCubicMixedActionWickSum
      timeBonds side sidePositive stage leftTime rightTime

/-- The two literal mixed cumulants with their exact response signs are the
displayed signed sum of finite weighted `3+2+3` Wick values. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_signedMixedAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    -finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
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
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceSignedMixedActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  exact Q'.add_eqv_congr'
    (Q'.neg_eqv_congr _ _
      (finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_leftCubic_mixedAction_wick
        timeBonds side sidePositive stage leftTime rightTime))
    (Q'.neg_eqv_congr _ _
      (finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_rightCubic_mixedAction_wick
        timeBonds side sidePositive stage leftTime rightTime))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceMixedCubicActionCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceMixedCubicActionCumulant.finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_leftCubic_mixedAction_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceMixedCubicActionCumulant.finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_rightCubic_mixedAction_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceMixedCubicActionCumulant.finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_signedMixedAction_wick
