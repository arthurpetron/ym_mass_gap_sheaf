/-
# Exact Wick certificates for the finite Cayley trace-source OWN means

The finite OWN coefficients used by the OLD-centered response are literal
Gaussian expectations, covariances, and third cumulants.  This leaf starts
their reduction to explicit finite row sums.  In particular it compiles

* the quadratic OWN mean to a weighted Gram sum,
* the quartic source expectation to a weighted four-row Wick sum,
* the cubic-source/total-cubic-action covariance to a weighted six-row sum,
* the repeated-cubic contribution to a weighted `3+2+3` Wick sum.

The complete `J2-V4` covariance is assembled below on the same row-block
carrier.  These identities remain finite FREE reference algebra.  They do
not identify an ORIGINAL-law center, control a higher remainder, prove a
uniform signed estimate, or imply a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse

local infix:50 " ≈ " => Q'.eqv

private theorem gaussian_zero (N : Nat) :
    finiteProductGaussian N polyZero ≈ 0 := by
  rw [finiteProductGaussian_probe]
  exact Q'.eqv_refl _

private theorem gaussian_add (N : Nat) (left right : RatPoly) :
    finiteProductGaussian N (polyAdd left right) ≈
      finiteProductGaussian N left + finiteProductGaussian N right := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe,
    finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) left right

private theorem gaussian_smul (N : Nat) (weight : Q')
    (polynomial : RatPoly) :
    finiteProductGaussian N (polySmul weight polynomial) ≈
      weight * finiteProductGaussian N polynomial := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_smul (finiteGaussianMono N) weight polynomial

/-- Explicit weighted Gram sum for a finite list of quadratic row blocks. -/
def finiteGaussianWeightedQuadraticExpectationGramSum
    (N : Nat) (blocks : List WeightedQuadraticRowBlock) : Q' :=
  qListSum (blocks.map fun block =>
    block.weight * finiteRowGram N block.first block.second)

/-- Finite weighted quadratic row-block expectations reduce termwise to
their row Grams. -/
theorem finiteProductGaussian_weighted_quadratic_row_blocks_gram
    (N : Nat) : ∀ blocks : List WeightedQuadraticRowBlock,
    finiteProductGaussian N
        (weightedTermPolynomial
          (blocks.map (weightedQuadraticRowBlockTerm N))) ≈
      finiteGaussianWeightedQuadraticExpectationGramSum N blocks
  | [] => gaussian_zero N
  | block :: blocks => by
      change finiteProductGaussian N
          (polyAdd
            (polySmul block.weight
              (finiteGaussianRowWord N [block.first, block.second]))
            (weightedTermPolynomial
              (blocks.map (weightedQuadraticRowBlockTerm N)))) ≈
        block.weight * finiteRowGram N block.first block.second +
          finiteGaussianWeightedQuadraticExpectationGramSum N blocks
      exact Q'.eqv_trans _ _ _
        (gaussian_add N _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (gaussian_smul N block.weight _)
            (Q'.mul_eqv_congr_left block.weight _ _
              (finiteProductGaussian_two_row_word N
                block.first block.second)))
          (finiteProductGaussian_weighted_quadratic_row_blocks_gram
            N blocks))

/-- Explicit weighted four-row Wick sum for a finite quartic block list. -/
def finiteGaussianWeightedQuarticExpectationWickSum
    (N : Nat) (blocks : List WeightedQuarticRowBlock) : Q' :=
  qListSum (blocks.map fun block =>
    block.weight *
      finiteGaussianRowWickStep N block.first
        [block.second, block.third, block.fourth])

/-- Finite weighted quartic row-block expectations reduce termwise to the
checked four-row Wick recursion. -/
theorem finiteProductGaussian_weighted_quartic_row_blocks_wick
    (N : Nat) : ∀ blocks : List WeightedQuarticRowBlock,
    finiteProductGaussian N
        (weightedTermPolynomial
          (blocks.map (weightedQuarticRowBlockTerm N))) ≈
      finiteGaussianWeightedQuarticExpectationWickSum N blocks
  | [] => gaussian_zero N
  | block :: blocks => by
      change finiteProductGaussian N
          (polyAdd
            (polySmul block.weight
              (finiteGaussianRowWord N
                [block.first, block.second, block.third, block.fourth]))
            (weightedTermPolynomial
              (blocks.map (weightedQuarticRowBlockTerm N)))) ≈
        block.weight *
            finiteGaussianRowWickStep N block.first
              [block.second, block.third, block.fourth] +
          finiteGaussianWeightedQuarticExpectationWickSum N blocks
      exact Q'.eqv_trans _ _ _
        (gaussian_add N _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (gaussian_smul N block.weight _)
            (Q'.mul_eqv_congr_left block.weight _ _
              (finiteProductGaussian_row_word_wick N
                block.first block.second [block.third, block.fourth])))
          (finiteProductGaussian_weighted_quartic_row_blocks_wick
            N blocks))

/-- Exact finite Gram certificate for the actual quadratic OWN mean `a2`. -/
def openCubeBulkCayleyTraceOwnA2MeanGramSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedQuadraticExpectationGramSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)

/-- The literal finite OWN quadratic mean equals its explicit weighted Gram
sum. -/
theorem openCubeBulkCayleyTraceOwnA2Mean_gram
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeBulkCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage time ≈
      openCubeBulkCayleyTraceOwnA2MeanGramSum
        timeBonds side sidePositive stage time := by
  unfold openCubeBulkCayleyTraceOwnA2Mean
    openCubeBulkCayleyTraceOwnA2MeanGramSum
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA2_coeffEqv
        timeBonds side sidePositive stage time))
    (finiteProductGaussian_weighted_quadratic_row_blocks_gram
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage time))

/-- Exact finite four-row certificate for the source quartic expectation
appearing in `a4`. -/
def openCubeBulkCayleyTraceA4ExpectationWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedQuarticExpectationWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA4RowBlocks
      timeBonds side sidePositive stage time)

theorem finiteProductGaussian_openCube_bulk_cayley_trace_A4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteProductGaussian (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA4
          timeBonds side sidePositive stage time) ≈
      openCubeBulkCayleyTraceA4ExpectationWickSum
        timeBonds side sidePositive stage time := by
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA4_coeffEqv
        timeBonds side sidePositive stage time))
    (finiteProductGaussian_weighted_quartic_row_blocks_wick
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA4RowBlocks
        timeBonds side sidePositive stage time))

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

/-- Explicit six-row Wick value of `Cov(A3,V3)` in the OWN fourth mean. -/
def openCubeBulkCayleyTraceA3ActionV3CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedThreeThreeCovarianceWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage time)
    (completeOpenCubeSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)

theorem finiteGaussianCovariance_openCube_bulk_cayley_trace_A3_actionV3_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage time)
        (completeOpenCubeSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceA3ActionV3CovarianceWickSum
        timeBonds side sidePositive stage time := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA3_coeffEqv
        timeBonds side sidePositive stage time)
      (completeActionCubicCertificate timeBonds side stage))
    (finiteGaussianCovariance_weighted_three_three_row_blocks_wick
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA3RowBlocks
        timeBonds side sidePositive stage time)
      (completeOpenCubeSpatialCubicRowBlocks
        timeBonds (bulkSourceWidth side) stage))

/-- Explicit `3+2+3` Wick value of `kappa(A2,V3,V3)` in the OWN fourth
mean. -/
def openCubeBulkCayleyTraceA2ActionV3V3CumulantWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedThreeTwoThreeWickSum
    (bulkSourceNoiseCount timeBonds side)
    (completeOpenCubeSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)
    (openCubeBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)
    (completeOpenCubeSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage)

theorem finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_A2_actionV3_actionV3_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage)
        (completeOpenCubeSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceA2ActionV3V3CumulantWickSum
        timeBonds side sidePositive stage time := by
  let N := bulkSourceNoiseCount timeBonds side
  let A2 := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage time
  let V3 := completeOpenCubeSpatialCubicPolynomial
    timeBonds (bulkSourceWidth side) stage
  let A2Blocks := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage time
  let V3Blocks := completeOpenCubeSpatialCubicRowBlocks
    timeBonds (bulkSourceWidth side) stage
  have swap := finiteGaussianThirdCumulant_swap_left_middle N A2 V3 V3
  have coefficients : finiteGaussianThirdCumulant N V3 A2 V3 ≈
      finiteGaussianThirdCumulant N
        (weightedTermPolynomial
          (V3Blocks.map (weightedCubicRowBlockTerm N)))
        (weightedTermPolynomial
          (A2Blocks.map (weightedQuadraticRowBlockTerm N)))
        (weightedTermPolynomial
          (V3Blocks.map (weightedCubicRowBlockTerm N))) := by
    unfold A2 V3 A2Blocks V3Blocks
    exact finiteGaussianThirdCumulant_coeffEqv N
      (completeActionCubicCertificate timeBonds side stage)
      (openCubeBulkCayleyTraceA2_coeffEqv
        timeBonds side sidePositive stage time)
      (completeActionCubicCertificate timeBonds side stage)
  exact Q'.eqv_trans _ _ _ swap
    (Q'.eqv_trans _ _ _ coefficients
      (finiteGaussianThirdCumulant_weighted_three_two_three_row_blocks_wick
        N V3Blocks A2Blocks V3Blocks))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick.finiteProductGaussian_weighted_quadratic_row_blocks_gram
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick.finiteProductGaussian_weighted_quartic_row_blocks_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick.openCubeBulkCayleyTraceOwnA2Mean_gram
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick.finiteProductGaussian_openCube_bulk_cayley_trace_A4_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick.finiteGaussianCovariance_openCube_bulk_cayley_trace_A3_actionV3_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick.finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_A2_actionV3_actionV3_wick
