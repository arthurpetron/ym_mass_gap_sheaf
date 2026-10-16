/-
# Corrected heat-carrier R4 and OWN means

This leaf reconstructs the connected fourth coefficient and the one-source
OWN coefficients on the corrected `(2L)^{-1}` heat carrier.  It compiles the
quadratic and quartic source expectations, the cubic-source/action covariance,
the full `A2` covariance with `J2-V4_spatial-V4_kinetic`, and the repeated
cubic cumulant to explicit finite Wick sums.

The supplied OLD center and the final `P4/P5/P6` products are not assembled
here.  No ORIGINAL-law comparison, uniform sign, higher-remainder estimate or
continuum/Clay conclusion is claimed.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatConnectedR6
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanCompleteWick

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatFourthActionHaarCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatConnectedR6

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem weightedRowSquares_coeffEqv
    (noiseCount : Nat) (squares : List WeightedRowSquare) :
    RatPolyCoeffEqv
      (weightedTermPolynomial
        (squares.map (weightedRowSquareTerm noiseCount)))
      (weightedTermPolynomial
        ((squares.map weightedRowSquareQuadraticBlock).map
          (weightedQuadraticRowBlockTerm noiseCount))) := by
  unfold weightedTermPolynomial weightedRowSquareTerm
    weightedRowSquareQuadraticBlock weightedQuadraticRowBlockTerm
    finiteGaussianRowSquare
    YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick.finiteGaussianRowWord
  simp only [List.map_map]
  exact RatPolyCoeffEqv.refl _

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

/-- Complete even density entering the corrected fourth OWN source mean. -/
def completeOpenCubeHeatJ2MinusV4Polynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polyAdd
    (completeOpenCubeHeatCayleyHaarJ2Polynomial timeBonds width stage)
    (polyAdd
      (polySmul (-1)
        (completeOpenCubeHeatSpatialFourthActionPolynomial
          timeBonds width stage))
      (polySmul (-1)
        (completeOpenCubeHeatKineticFourthActionPolynomial
          timeBonds width stage)))

/-- Corrected heat-carrier OWN quadratic source mean. -/
def openCubeHeatCayleyTraceOwnA2Mean
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteProductGaussian (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA2
      timeBonds side sidePositive stage time)

/-- Corrected heat-carrier OWN cubic source mean. -/
def openCubeHeatCayleyTraceOwnA3Mean
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteProductGaussian (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA3
        timeBonds side sidePositive stage time) -
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage time)
      (completeOpenCubeHeatSpatialCubicPolynomial
        timeBonds (bulkSourceWidth side) stage)

/-- Corrected heat-carrier OWN fourth source mean. -/
def openCubeHeatCayleyTraceOwnA4Mean
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let A2 := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage time
  let A3 := openCubeHeatBulkCayleyTraceA3
    timeBonds side sidePositive stage time
  let A4 := openCubeHeatBulkCayleyTraceA4
    timeBonds side sidePositive stage time
  let V3 := completeOpenCubeHeatSpatialCubicPolynomial
    timeBonds (bulkSourceWidth side) stage
  let evenDensity := completeOpenCubeHeatJ2MinusV4Polynomial
    timeBonds (bulkSourceWidth side) stage
  (((finiteProductGaussian noiseCount A4 -
      finiteGaussianCovariance noiseCount A3 V3) +
      finiteGaussianCovariance noiseCount A2 evenDensity) +
    cubicPairHalf * finiteGaussianThirdCumulant noiseCount A2 V3 V3)

/-- Corrected connected fourth coefficient. -/
def openCubeHeatCayleyTraceConnectedR4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA2
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatBulkCayleyTraceA2
      timeBonds side sidePositive stage rightTime)

/-- Explicit connected `2+2` Wick value of corrected `R4`. -/
def openCubeHeatCayleyTraceConnectedR4WickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedTwoTwoCovarianceWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage rightTime)

theorem openCubeHeatCayleyTraceConnectedR4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    openCubeHeatCayleyTraceConnectedR4
        timeBonds side sidePositive stage leftTime rightTime ≈
      openCubeHeatCayleyTraceConnectedR4WickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  unfold openCubeHeatCayleyTraceConnectedR4
    openCubeHeatCayleyTraceConnectedR4WickSum
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2_coeffEqv
        timeBonds side sidePositive stage leftTime)
      (openCubeHeatBulkCayleyTraceA2_coeffEqv
        timeBonds side sidePositive stage rightTime))
    (finiteGaussianCovariance_weighted_two_two_row_blocks_wick
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage leftTime)
      (openCubeHeatBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage rightTime))

/-- Explicit weighted Gram sum for the corrected quadratic OWN mean. -/
def openCubeHeatCayleyTraceOwnA2MeanGramSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedQuadraticExpectationGramSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)

theorem openCubeHeatCayleyTraceOwnA2Mean_gram
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage time ≈
      openCubeHeatCayleyTraceOwnA2MeanGramSum
        timeBonds side sidePositive stage time := by
  unfold openCubeHeatCayleyTraceOwnA2Mean
    openCubeHeatCayleyTraceOwnA2MeanGramSum
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2_coeffEqv
        timeBonds side sidePositive stage time))
    (finiteProductGaussian_weighted_quadratic_row_blocks_gram
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage time))

theorem finiteProductGaussian_openCubeHeat_cayleyTrace_A3_zero
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteProductGaussian (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage time) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA3_coeffEqv
        timeBonds side sidePositive stage time))
    (finiteProductGaussian_weighted_cubic_row_blocks_zero
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA3RowBlocks
        timeBonds side sidePositive stage time))

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_actionV3_zero
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeHeatSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2_coeffEqv
        timeBonds side sidePositive stage time)
      (completeHeatActionCubicCertificate timeBonds side stage))
    (finiteGaussianCovariance_weighted_two_three_row_blocks_zero
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage time)
      (completeOpenCubeHeatSpatialCubicRowBlocks
        timeBonds (bulkSourceWidth side) stage))

theorem openCubeHeatCayleyTraceOwnA3Mean_zero
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeHeatCayleyTraceOwnA3Mean
        timeBonds side sidePositive stage time ≈ 0 := by
  unfold openCubeHeatCayleyTraceOwnA3Mean
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (finiteProductGaussian_openCubeHeat_cayleyTrace_A3_zero
        timeBonds side sidePositive stage time)
      (Q'.neg_eqv_congr _ _
        (finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_actionV3_zero
          timeBonds side sidePositive stage time)))
    (poly_identity_of_normal_eq
      (.add (.const 0) (.neg (.const 0)))
      (.const 0) (by decide) (fun _ => 0))

/-- Explicit four-row Wick sum for the corrected source quartic expectation. -/
def openCubeHeatCayleyTraceA4ExpectationWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedQuarticExpectationWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA4RowBlocks
      timeBonds side sidePositive stage time)

theorem finiteProductGaussian_openCubeHeat_cayleyTrace_A4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteProductGaussian (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA4
          timeBonds side sidePositive stage time) ≈
      openCubeHeatCayleyTraceA4ExpectationWickSum
        timeBonds side sidePositive stage time := by
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA4_coeffEqv
        timeBonds side sidePositive stage time))
    (finiteProductGaussian_weighted_quartic_row_blocks_wick
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA4RowBlocks
        timeBonds side sidePositive stage time))

/-- Explicit six-row Wick value of `Cov(A3,V3)`. -/
def openCubeHeatCayleyTraceA3ActionV3CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedThreeThreeCovarianceWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage time)
    (completeOpenCubeHeatSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_A3_actionV3_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA3
          timeBonds side sidePositive stage time)
        (completeOpenCubeHeatSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceA3ActionV3CovarianceWickSum
        timeBonds side sidePositive stage time := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA3_coeffEqv
        timeBonds side sidePositive stage time)
      (completeHeatActionCubicCertificate timeBonds side stage))
    (finiteGaussianCovariance_weighted_three_three_row_blocks_wick
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatBulkCayleyTraceA3RowBlocks
        timeBonds side sidePositive stage time)
      (completeOpenCubeHeatSpatialCubicRowBlocks
        timeBonds (bulkSourceWidth side) stage))

/-- Explicit `3+2+3` Wick value of `kappa(A2,V3,V3)`. -/
def openCubeHeatCayleyTraceA2ActionV3V3CumulantWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedThreeTwoThreeWickSum
    (bulkSourceNoiseCount timeBonds side)
    (completeOpenCubeHeatSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)
    (completeOpenCubeHeatSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)

theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_A2_actionV3_actionV3_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeHeatSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage)
        (completeOpenCubeHeatSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceA2ActionV3V3CumulantWickSum
        timeBonds side sidePositive stage time := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let A2 := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage time
  let V3 := completeOpenCubeHeatSpatialCubicPolynomial
    timeBonds (bulkSourceWidth side) stage
  let A2Blocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage time
  let V3Blocks := completeOpenCubeHeatSpatialCubicRowBlocks
    timeBonds (bulkSourceWidth side) stage
  have swap := finiteGaussianThirdCumulant_swap_left_middle
    noiseCount A2 V3 V3
  have coefficients : finiteGaussianThirdCumulant noiseCount V3 A2 V3 ≈
      finiteGaussianThirdCumulant noiseCount
        (weightedTermPolynomial
          (V3Blocks.map (weightedCubicRowBlockTerm noiseCount)))
        (weightedTermPolynomial
          (A2Blocks.map (weightedQuadraticRowBlockTerm noiseCount)))
        (weightedTermPolynomial
          (V3Blocks.map (weightedCubicRowBlockTerm noiseCount))) := by
    exact finiteGaussianThirdCumulant_coeffEqv noiseCount
      (completeHeatActionCubicCertificate timeBonds side stage)
      (openCubeHeatBulkCayleyTraceA2_coeffEqv
        timeBonds side sidePositive stage time)
      (completeHeatActionCubicCertificate timeBonds side stage)
  exact Q'.eqv_trans _ _ _ swap
    (Q'.eqv_trans _ _ _ coefficients
      (finiteGaussianThirdCumulant_weighted_three_two_three_row_blocks_wick
        noiseCount V3Blocks A2Blocks V3Blocks))

private theorem finiteGaussianCovariance_quartic_quadratic_wick
    (noiseCount : Nat) (source : RatPoly)
    (sourceBlocks : List WeightedQuadraticRowBlock)
    (quarticBlocks : List WeightedQuarticRowBlock)
    (quadraticSquares : List WeightedRowSquare)
    (hsource : RatPolyCoeffEqv source
      (weightedTermPolynomial
        (sourceBlocks.map (weightedQuadraticRowBlockTerm noiseCount)))) :
    finiteGaussianCovariance noiseCount source
        (polyAdd
          (weightedTermPolynomial
            (quarticBlocks.map (weightedQuarticRowBlockTerm noiseCount)))
          (weightedTermPolynomial
            (quadraticSquares.map (weightedRowSquareTerm noiseCount)))) ≈
      finiteGaussianWeightedTwoFourCovarianceWickSum
          noiseCount sourceBlocks quarticBlocks +
        finiteGaussianWeightedTwoTwoCovarianceWickSum
          noiseCount sourceBlocks
          (quadraticSquares.map weightedRowSquareQuadraticBlock) := by
  let sourcePolynomial := weightedTermPolynomial
    (sourceBlocks.map (weightedQuadraticRowBlockTerm noiseCount))
  let quarticPolynomial := weightedTermPolynomial
    (quarticBlocks.map (weightedQuarticRowBlockTerm noiseCount))
  let quadraticPolynomial := weightedTermPolynomial
    (quadraticSquares.map (weightedRowSquareTerm noiseCount))
  have hsourceCovariance := finiteGaussianCovariance_coeffEqv noiseCount
    hsource (RatPolyCoeffEqv.refl
      (polyAdd quarticPolynomial quadraticPolynomial))
  have hsplit := finiteGaussianCovariance_add_right noiseCount
    sourcePolynomial quarticPolynomial quadraticPolynomial
  have hquartic := finiteGaussianCovariance_weighted_two_four_row_blocks_wick
    noiseCount sourceBlocks quarticBlocks
  have hquadraticCongr := finiteGaussianCovariance_coeffEqv noiseCount
    (RatPolyCoeffEqv.refl sourcePolynomial)
    (weightedRowSquares_coeffEqv noiseCount quadraticSquares)
  have hquadratic := finiteGaussianCovariance_weighted_two_two_row_blocks_wick
    noiseCount sourceBlocks
      (quadraticSquares.map weightedRowSquareQuadraticBlock)
  exact Q'.eqv_trans _ _ _ hsourceCovariance
    (Q'.eqv_trans _ _ _ hsplit
      (Q'.add_eqv_congr' hquartic
        (Q'.eqv_trans _ _ _ hquadraticCongr hquadratic)))

private theorem finiteGaussianCovariance_row_squares_wick
    (noiseCount : Nat) (source : RatPoly)
    (sourceBlocks : List WeightedQuadraticRowBlock)
    (squares : List WeightedRowSquare)
    (hsource : RatPolyCoeffEqv source
      (weightedTermPolynomial
        (sourceBlocks.map (weightedQuadraticRowBlockTerm noiseCount)))) :
    finiteGaussianCovariance noiseCount source
        (weightedTermPolynomial
          (squares.map (weightedRowSquareTerm noiseCount))) ≈
      finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount
        sourceBlocks (squares.map weightedRowSquareQuadraticBlock) := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv noiseCount hsource
      (weightedRowSquares_coeffEqv noiseCount squares))
    (finiteGaussianCovariance_weighted_two_two_row_blocks_wick
      noiseCount sourceBlocks
        (squares.map weightedRowSquareQuadraticBlock))

/-- Corrected covariance of `A2` with complete spatial `V4`. -/
def openCubeHeatCayleyTraceA2SpatialV4CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let sourceBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage time
  finiteGaussianWeightedTwoFourCovarianceWickSum noiseCount sourceBlocks
      (completeOpenCubeHeatSpatialFourthActionQuarticRowBlocks
        timeBonds (bulkSourceWidth side) stage) +
    finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount sourceBlocks
      ((completeOpenCubeHeatSpatialFourthActionQuadraticRowSquares
        timeBonds (bulkSourceWidth side) stage).map
          weightedRowSquareQuadraticBlock)

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_spatialV4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeHeatSpatialFourthActionPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceA2SpatialV4CovarianceWickSum
        timeBonds side sidePositive stage time := by
  unfold completeOpenCubeHeatSpatialFourthActionPolynomial
    openCubeHeatCayleyTraceA2SpatialV4CovarianceWickSum
  exact finiteGaussianCovariance_quartic_quadratic_wick
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA2
      timeBonds side sidePositive stage time)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)
    (completeOpenCubeHeatSpatialFourthActionQuarticRowBlocks
      timeBonds (bulkSourceWidth side) stage)
    (completeOpenCubeHeatSpatialFourthActionQuadraticRowSquares
      timeBonds (bulkSourceWidth side) stage)
    (openCubeHeatBulkCayleyTraceA2_coeffEqv
      timeBonds side sidePositive stage time)

/-- Corrected covariance of `A2` with complete kinetic `V4`. -/
def openCubeHeatCayleyTraceA2KineticV4CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let sourceBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage time
  finiteGaussianWeightedTwoFourCovarianceWickSum noiseCount sourceBlocks
      (completeOpenCubeHeatKineticFourthActionQuarticRowBlocks
        timeBonds (bulkSourceWidth side) stage) +
    finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount sourceBlocks
      ((completeOpenCubeHeatKineticFourthActionQuadraticRowSquares
        timeBonds (bulkSourceWidth side) stage).map
          weightedRowSquareQuadraticBlock)

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_kineticV4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeHeatKineticFourthActionPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceA2KineticV4CovarianceWickSum
        timeBonds side sidePositive stage time := by
  unfold completeOpenCubeHeatKineticFourthActionPolynomial
    openCubeHeatCayleyTraceA2KineticV4CovarianceWickSum
  exact finiteGaussianCovariance_quartic_quadratic_wick
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA2
      timeBonds side sidePositive stage time)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)
    (completeOpenCubeHeatKineticFourthActionQuarticRowBlocks
      timeBonds (bulkSourceWidth side) stage)
    (completeOpenCubeHeatKineticFourthActionQuadraticRowSquares
      timeBonds (bulkSourceWidth side) stage)
    (openCubeHeatBulkCayleyTraceA2_coeffEqv
      timeBonds side sidePositive stage time)

/-- Corrected covariance of `A2` with complete Cayley-Haar `J2`. -/
def openCubeHeatCayleyTraceA2HaarJ2CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedTwoTwoCovarianceWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)
    ((completeOpenCubeHeatCayleyHaarJ2RowSquares
      timeBonds (bulkSourceWidth side) stage).map
        weightedRowSquareQuadraticBlock)

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_haarJ2_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeHeatCayleyHaarJ2Polynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceA2HaarJ2CovarianceWickSum
        timeBonds side sidePositive stage time := by
  unfold completeOpenCubeHeatCayleyHaarJ2Polynomial
    openCubeHeatCayleyTraceA2HaarJ2CovarianceWickSum
  exact finiteGaussianCovariance_row_squares_wick
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA2
      timeBonds side sidePositive stage time)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)
    (completeOpenCubeHeatCayleyHaarJ2RowSquares
      timeBonds (bulkSourceWidth side) stage)
    (openCubeHeatBulkCayleyTraceA2_coeffEqv
      timeBonds side sidePositive stage time)

/-- Complete explicit corrected covariance with `J2-V4_spatial-V4_kinetic`. -/
def openCubeHeatCayleyTraceA2J2MinusV4CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  openCubeHeatCayleyTraceA2HaarJ2CovarianceWickSum
      timeBonds side sidePositive stage time +
    ((-1) * openCubeHeatCayleyTraceA2SpatialV4CovarianceWickSum
      timeBonds side sidePositive stage time +
    (-1) * openCubeHeatCayleyTraceA2KineticV4CovarianceWickSum
      timeBonds side sidePositive stage time)

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_J2MinusV4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeHeatJ2MinusV4Polynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceA2J2MinusV4CovarianceWickSum
        timeBonds side sidePositive stage time := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let source := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage time
  let haar := completeOpenCubeHeatCayleyHaarJ2Polynomial
    timeBonds (bulkSourceWidth side) stage
  let spatial := completeOpenCubeHeatSpatialFourthActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  let kinetic := completeOpenCubeHeatKineticFourthActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  have hhaar := finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_haarJ2_wick
    timeBonds side sidePositive stage time
  have hspatialBase :=
    finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_spatialV4_wick
      timeBonds side sidePositive stage time
  have hspatial : finiteGaussianCovariance noiseCount source
        (polySmul (-1) spatial) ≈
      (-1) * openCubeHeatCayleyTraceA2SpatialV4CovarianceWickSum
        timeBonds side sidePositive stage time :=
    Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_smul_right
        noiseCount (-1) source spatial)
      (Q'.mul_eqv_congr_left (-1) _ _ hspatialBase)
  have hkineticBase :=
    finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_kineticV4_wick
      timeBonds side sidePositive stage time
  have hkinetic : finiteGaussianCovariance noiseCount source
        (polySmul (-1) kinetic) ≈
      (-1) * openCubeHeatCayleyTraceA2KineticV4CovarianceWickSum
        timeBonds side sidePositive stage time :=
    Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_smul_right
        noiseCount (-1) source kinetic)
      (Q'.mul_eqv_congr_left (-1) _ _ hkineticBase)
  have hsplitOuter := finiteGaussianCovariance_add_right
    noiseCount source haar
      (polyAdd (polySmul (-1) spatial) (polySmul (-1) kinetic))
  have hsplitInner := finiteGaussianCovariance_add_right
    noiseCount source (polySmul (-1) spatial) (polySmul (-1) kinetic)
  unfold completeOpenCubeHeatJ2MinusV4Polynomial
    openCubeHeatCayleyTraceA2J2MinusV4CovarianceWickSum
  exact Q'.eqv_trans _ _ _ hsplitOuter
    (Q'.add_eqv_congr' hhaar
      (Q'.eqv_trans _ _ _ hsplitInner
        (Q'.add_eqv_congr' hspatial hkinetic)))

/-- Complete explicit finite Wick value of the corrected fourth OWN mean. -/
def openCubeHeatCayleyTraceOwnA4MeanWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  ((openCubeHeatCayleyTraceA4ExpectationWickSum
        timeBonds side sidePositive stage time -
      openCubeHeatCayleyTraceA3ActionV3CovarianceWickSum
        timeBonds side sidePositive stage time) +
    openCubeHeatCayleyTraceA2J2MinusV4CovarianceWickSum
      timeBonds side sidePositive stage time) +
  cubicPairHalf *
    openCubeHeatCayleyTraceA2ActionV3V3CumulantWickSum
      timeBonds side sidePositive stage time

theorem openCubeHeatCayleyTraceOwnA4Mean_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeHeatCayleyTraceOwnA4Mean
        timeBonds side sidePositive stage time ≈
      openCubeHeatCayleyTraceOwnA4MeanWickSum
        timeBonds side sidePositive stage time := by
  unfold openCubeHeatCayleyTraceOwnA4Mean
    openCubeHeatCayleyTraceOwnA4MeanWickSum
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (finiteProductGaussian_openCubeHeat_cayleyTrace_A4_wick
          timeBonds side sidePositive stage time)
        (Q'.neg_eqv_congr _ _
          (finiteGaussianCovariance_openCubeHeat_cayleyTrace_A3_actionV3_wick
            timeBonds side sidePositive stage time)))
      (finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_J2MinusV4_wick
        timeBonds side sidePositive stage time))
    (Q'.mul_eqv_congr_left cubicPairHalf _ _
      (finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_A2_actionV3_actionV3_wick
        timeBonds side sidePositive stage time))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick.openCubeHeatCayleyTraceConnectedR4_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick.openCubeHeatCayleyTraceOwnA3Mean_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick.openCubeHeatCayleyTraceOwnA4Mean_wick
