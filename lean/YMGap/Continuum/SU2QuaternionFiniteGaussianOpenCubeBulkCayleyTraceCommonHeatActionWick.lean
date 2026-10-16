/-
# Explicit Wick certificate for the common heat-action scaling residual

The preceding common-heat-action module isolates three exact normalization
diagnostics on the older inverse-of-`L` carrier: two one-point differences
`Cov(A2,S0)-E[A2]` and one connected difference
`kappa(A2,B2,S0)-2*R4`.  Because the standard product Gaussian paired with
that carrier has covariance `L^{-1}`, these differences include a fixed
factor-two normalization debt and are not pure finite-Heron errors.  This
leaf compiles all three to finite row-Gram sums on the literal carrier.

Every spatial face/time and kinetic bond/link term in `S0` is retained.  No
Gaussian expectation, covariance, or cumulant remains in the final residual
certificate.  The corrected `(2L)^{-1}` heat carrier is constructed in
`SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite`;
the source/action chain has not yet been rebuilt on it.  This is an exact
finite evaluator result; it does not prove a neighboring-scale sign, compare
the ORIGINAL law, or establish a continuum mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatActionWick

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
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
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeSquareThirdCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem polySmul_one (polynomial : RatPoly) :
    RatPolyCoeffEqv (polySmul 1 polynomial) polynomial := by
  intro weight
  exact Q'.eqv_trans _ _ _
    (ratWeightedSum_smul weight 1 polynomial)
    (Q'.one_mul_eqv _)

private theorem polySmul_polySum (scale : Q') : ∀ polynomials : List RatPoly,
    RatPolyCoeffEqv
      (polySmul scale (polySum polynomials))
      (polySum (polynomials.map (polySmul scale)))
  | [] => RatPolyCoeffEqv.zero_smul polyZero
  | polynomial :: polynomials =>
      (RatPolyCoeffEqv.smul_add scale polynomial (polySum polynomials)).trans
        ((RatPolyCoeffEqv.refl _).add
          (polySmul_polySum scale polynomials))

/-- Scale one weighted row square without changing its row. -/
def scaleWeightedRowSquare
    (scale : Q') (square : WeightedRowSquare) : WeightedRowSquare :=
  { weight := scale * square.weight
    row := square.row }

private theorem weightedRowSquares_scale_terms
    (N : Nat) (scale : Q') : ∀ squares : List WeightedRowSquare,
    RatPolyCoeffEqv
      (polySum (squares.map fun square =>
        polySmul scale
          (polySmul square.weight
            (finiteGaussianRowSquare N square.row))))
      (polySum (squares.map fun square =>
        polySmul (scale * square.weight)
          (finiteGaussianRowSquare N square.row)))
  | [] => RatPolyCoeffEqv.refl _
  | square :: squares =>
      (RatPolyCoeffEqv.smul_assoc
        scale square.weight (finiteGaussianRowSquare N square.row)).add
          (weightedRowSquares_scale_terms N scale squares)

private theorem weightedRowSquares_scale
    (N : Nat) (scale : Q') (squares : List WeightedRowSquare) :
    RatPolyCoeffEqv
      (polySmul scale
        (weightedTermPolynomial
          (squares.map (weightedRowSquareTerm N))))
      (weightedTermPolynomial
        ((squares.map (scaleWeightedRowSquare scale)).map
          (weightedRowSquareTerm N))) := by
  unfold weightedTermPolynomial weightedRowSquareTerm scaleWeightedRowSquare
  simp only [List.map_map]
  have distribute : RatPolyCoeffEqv
      (polySmul scale
        (polySum (squares.map fun square =>
          polySmul square.weight
            (finiteGaussianRowSquare N square.row))))
      (polySum (squares.map fun square =>
        polySmul scale
          (polySmul square.weight
            (finiteGaussianRowSquare N square.row)))) := by
    simpa only [List.map_map, Function.comp_apply] using
      polySmul_polySum scale
        (squares.map fun square =>
          polySmul square.weight
            (finiteGaussianRowSquare N square.row))
  exact distribute.trans
    (weightedRowSquares_scale_terms N scale squares)

private theorem weightedTermPolynomial_append
    (left right : List (Q' × RatPoly)) :
    RatPolyCoeffEqv
      (polyAdd (weightedTermPolynomial left) (weightedTermPolynomial right))
      (weightedTermPolynomial (left ++ right)) := by
  unfold weightedTermPolynomial
  simp only [List.map_append]
  exact RatPolyCoeffEqv.polySum_append _ _

private theorem weightedRowSquares_family_coeffEqv
    {Index : Type} (N : Nat)
    (weight : Index → Q')
    (polynomial : Index → RatPoly)
    (squares : Index → List WeightedRowSquare)
    (localCertificate : ∀ index,
      RatPolyCoeffEqv (polynomial index)
        (weightedTermPolynomial
          ((squares index).map (weightedRowSquareTerm N)))) :
    ∀ indices : List Index,
    RatPolyCoeffEqv
      (polySum (indices.map fun index =>
        polySmul (weight index) (polynomial index)))
      (weightedTermPolynomial
        ((indices.flatMap fun index =>
          (squares index).map
            (scaleWeightedRowSquare (weight index))).map
              (weightedRowSquareTerm N)))
  | [] => RatPolyCoeffEqv.refl _
  | index :: indices => by
      have hhead : RatPolyCoeffEqv
          (polySmul (weight index) (polynomial index))
          (weightedTermPolynomial
            (((squares index).map
              (scaleWeightedRowSquare (weight index))).map
                (weightedRowSquareTerm N))) :=
        ((localCertificate index).smul (weight index)).trans
          (weightedRowSquares_scale N (weight index) (squares index))
      have htail := weightedRowSquares_family_coeffEqv N weight polynomial
        squares localCertificate indices
      exact (hhead.add htail).trans (by
        simp only [List.flatMap_cons, List.map_append]
        exact weightedTermPolynomial_append _ _)

private theorem weightedRowSquares_coeffEqv
    (N : Nat) (squares : List WeightedRowSquare) :
    RatPolyCoeffEqv
      (weightedTermPolynomial
        (squares.map (weightedRowSquareTerm N)))
      (weightedTermPolynomial
        ((squares.map weightedRowSquareQuadraticBlock).map
          (weightedQuadraticRowBlockTerm N))) := by
  unfold weightedTermPolynomial weightedRowSquareTerm
    weightedRowSquareQuadraticBlock weightedQuadraticRowBlockTerm
    finiteGaussianRowSquare finiteGaussianRowWord
  simp only [List.map_map]
  exact RatPolyCoeffEqv.refl _

/-- The `A2=4*sourceQuadratic` family as weighted literal row squares. -/
def openCubeBulkCayleyTraceA2RowSquares
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : List WeightedRowSquare :=
  (bulkSourceHeronWeightedRowSquares
    timeBonds side sidePositive stage time).map
      (scaleWeightedRowSquare 4)

theorem openCubeBulkCayleyTraceA2RowSquares_coeffEqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    RatPolyCoeffEqv
      (openCubeBulkCayleyTraceA2
        timeBonds side sidePositive stage time)
      (weightedTermPolynomial
        ((openCubeBulkCayleyTraceA2RowSquares
          timeBonds side sidePositive stage time).map
            (weightedRowSquareTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  unfold openCubeBulkCayleyTraceA2
    openCubeBulkCayleyTraceA2RowSquares
  rw [bulkSourceHeronRadialSquare_eq_weightedRowSquares]
  exact weightedRowSquares_scale
    (bulkSourceNoiseCount timeBonds side) 4
    (bulkSourceHeronWeightedRowSquares
      timeBonds side sidePositive stage time)

/-- Three positive `F2/4` row squares on one spatial plaquette. -/
def openCubePlaquetteGaussianActionRowSquares
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedRowSquare :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianWeightedRowNormSquares 1
    (gaussianCayleyTotalRows
      (gaussianCayleySlot (rows 0) (rows 1) (rows 2) (rows 3)))

theorem openCubePlaquetteGaussianActionRowSquares_coeffEqv
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (openCubePlaquetteGaussianActionPolynomial
        timeBonds width stage time face)
      (weightedTermPolynomial
        ((openCubePlaquetteGaussianActionRowSquares
          timeBonds width stage time face).map
            (weightedRowSquareTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  unfold openCubePlaquetteGaussianActionPolynomial
    openCubePlaquetteGaussianActionRowSquares
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  let total := gaussianCayleyTotalRows
    (gaussianCayleySlot (rows 0) (rows 1) (rows 2) (rows 3))
  exact (polySmul_one
      (finiteGaussianRowDot
        (combGaugePlaquetteNoiseCount timeBonds width) 3 total total)).symm.trans
    (finiteGaussianWeightedRowNormSquares_coeffEqv
      (combGaugePlaquetteNoiseCount timeBonds width) 1 total)

/-- Three positive temporal-difference row squares on one kinetic insertion. -/
def openCubeKineticGaussianActionRowSquares
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    List WeightedRowSquare :=
  finiteGaussianWeightedRowNormSquares 1
    (combGaugeFreeHistoryHeronKineticDifferenceRows
      timeBonds width stage bond link)

theorem openCubeKineticGaussianActionRowSquares_coeffEqv
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    RatPolyCoeffEqv
      (openCubeKineticGaussianActionPolynomial
        timeBonds width stage bond link)
      (weightedTermPolynomial
        ((openCubeKineticGaussianActionRowSquares
          timeBonds width stage bond link).map
            (weightedRowSquareTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  unfold openCubeKineticGaussianActionPolynomial
    openCubeKineticGaussianActionRowSquares
  let difference := combGaugeFreeHistoryHeronKineticDifferenceRows
    timeBonds width stage bond link
  exact (polySmul_one
      (finiteGaussianRowDot
        (combGaugePlaquetteNoiseCount timeBonds width) 3
        difference difference)).symm.trans
    (finiteGaussianWeightedRowNormSquares_coeffEqv
      (combGaugePlaquetteNoiseCount timeBonds width) 1 difference)

/-- Complete weighted row-square list for the actual pulled-back `S0`. -/
def completeOpenCubeGaussianActionRowSquares
    (timeBonds width stage : Nat) : List WeightedRowSquare :=
  ((completeOpenCubeSpatialHeatActionFourthInsertions
      timeBonds width).flatMap fun insertion =>
        (openCubePlaquetteGaussianActionRowSquares
          timeBonds width stage insertion.time insertion.face).map
            (scaleWeightedRowSquare insertion.weight)) ++
  ((completeOpenCubeKineticFourthActionInsertions
      timeBonds width).flatMap fun insertion =>
        (openCubeKineticGaussianActionRowSquares
          timeBonds width stage insertion.bond insertion.link).map
            (scaleWeightedRowSquare insertion.weight))

theorem completeOpenCubeGaussianActionRowSquares_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeGaussianActionPolynomial
        timeBonds width stage)
      (weightedTermPolynomial
        ((completeOpenCubeGaussianActionRowSquares
          timeBonds width stage).map
            (weightedRowSquareTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  let N := combGaugePlaquetteNoiseCount timeBonds width
  let spatialInsertions := completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width
  let kineticInsertions := completeOpenCubeKineticFourthActionInsertions
    timeBonds width
  let spatialSquares := fun insertion : OpenCubeSpatialHeatActionFourthInsertion =>
    openCubePlaquetteGaussianActionRowSquares
      timeBonds width stage insertion.time insertion.face
  let kineticSquares := fun insertion : OpenCubeKineticFourthActionInsertion =>
    openCubeKineticGaussianActionRowSquares
      timeBonds width stage insertion.bond insertion.link
  have hspatial := weightedRowSquares_family_coeffEqv N
    (fun insertion : OpenCubeSpatialHeatActionFourthInsertion => insertion.weight)
    (fun insertion => openCubePlaquetteGaussianActionPolynomial
      timeBonds width stage insertion.time insertion.face)
    spatialSquares
    (fun insertion => openCubePlaquetteGaussianActionRowSquares_coeffEqv
      timeBonds width stage insertion.time insertion.face)
    spatialInsertions
  have hkinetic := weightedRowSquares_family_coeffEqv N
    (fun insertion : OpenCubeKineticFourthActionInsertion => insertion.weight)
    (fun insertion => openCubeKineticGaussianActionPolynomial
      timeBonds width stage insertion.bond insertion.link)
    kineticSquares
    (fun insertion => openCubeKineticGaussianActionRowSquares_coeffEqv
      timeBonds width stage insertion.bond insertion.link)
    kineticInsertions
  unfold completeOpenCubeGaussianActionPolynomial
    completeOpenCubeSpatialGaussianActionPolynomial
    completeOpenCubeKineticGaussianActionPolynomial
    completeOpenCubeGaussianActionRowSquares
  refine (hspatial.add hkinetic).trans ?_
  simpa only [N, spatialInsertions, kineticInsertions,
    spatialSquares, kineticSquares, List.map_append] using
    (weightedTermPolynomial_append
      ((spatialInsertions.flatMap fun insertion =>
        (spatialSquares insertion).map
          (scaleWeightedRowSquare insertion.weight)).map
            (weightedRowSquareTerm N))
      ((kineticInsertions.flatMap fun insertion =>
        (kineticSquares insertion).map
          (scaleWeightedRowSquare insertion.weight)).map
            (weightedRowSquareTerm N)))

/-- Explicit two-row covariance value for one trace source against `S0`. -/
def openCubeBulkCayleyTraceA2GaussianActionCovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  finiteGaussianWeightedTwoTwoCovarianceWickSum N
    ((openCubeBulkCayleyTraceA2RowSquares
      timeBonds side sidePositive stage time).map
        weightedRowSquareQuadraticBlock)
    ((completeOpenCubeGaussianActionRowSquares
      timeBonds (bulkSourceWidth side) stage).map
        weightedRowSquareQuadraticBlock)

theorem finiteGaussianCovariance_openCube_bulk_cayley_trace_A2_gaussianAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeGaussianActionPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceA2GaussianActionCovarianceWickSum
        timeBonds side sidePositive stage time := by
  let N := bulkSourceNoiseCount timeBonds side
  let sourceSquares := openCubeBulkCayleyTraceA2RowSquares
    timeBonds side sidePositive stage time
  let actionSquares := completeOpenCubeGaussianActionRowSquares
    timeBonds (bulkSourceWidth side) stage
  have noiseEquality : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) = N := by
    unfold N bulkSourceNoiseCount combGaugePlaquetteNoiseCount
    rfl
  have hsource := (openCubeBulkCayleyTraceA2RowSquares_coeffEqv
    timeBonds side sidePositive stage time).trans
      (weightedRowSquares_coeffEqv N sourceSquares)
  have hactionBase := completeOpenCubeGaussianActionRowSquares_coeffEqv
    timeBonds (bulkSourceWidth side) stage
  rw [noiseEquality] at hactionBase
  have haction := hactionBase.trans
    (weightedRowSquares_coeffEqv N actionSquares)
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv N hsource haction)
    (finiteGaussianCovariance_weighted_two_two_row_blocks_wick N
      (sourceSquares.map weightedRowSquareQuadraticBlock)
      (actionSquares.map weightedRowSquareQuadraticBlock))

/-- Exact finite Gram value of the one-point action-scaling defect. -/
def openCubeBulkCayleyTraceHeatMeanScalingDefectWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  openCubeBulkCayleyTraceA2GaussianActionCovarianceWickSum
      timeBonds side sidePositive stage time -
    openCubeBulkCayleyTraceOwnA2MeanGramSum
      timeBonds side sidePositive stage time

theorem openCubeBulkCayleyTraceHeatMeanScalingDefect_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeBulkCayleyTraceHeatMeanScalingDefect
        timeBonds side sidePositive stage time ≈
      openCubeBulkCayleyTraceHeatMeanScalingDefectWickSum
        timeBonds side sidePositive stage time := by
  unfold openCubeBulkCayleyTraceHeatMeanScalingDefect
    openCubeBulkCayleyTraceHeatMeanScalingDefectWickSum
  exact Q'.add_eqv_congr'
    (finiteGaussianCovariance_openCube_bulk_cayley_trace_A2_gaussianAction_wick
      timeBonds side sidePositive stage time)
    (Q'.neg_eqv_congr _ _
      (openCubeBulkCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage time))

/-- Explicit `2+2+2` Gram-triangle value for two trace sources and `S0`. -/
def openCubeBulkCayleyTraceA2A2GaussianActionThirdCumulantWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedRowSquaresTriangleSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA2RowSquares
      timeBonds side sidePositive stage leftTime)
    (openCubeBulkCayleyTraceA2RowSquares
      timeBonds side sidePositive stage rightTime)
    (completeOpenCubeGaussianActionRowSquares
      timeBonds (bulkSourceWidth side) stage)

theorem finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_A2_A2_gaussianAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeGaussianActionPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceA2A2GaussianActionThirdCumulantWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let leftSquares := openCubeBulkCayleyTraceA2RowSquares
    timeBonds side sidePositive stage leftTime
  let rightSquares := openCubeBulkCayleyTraceA2RowSquares
    timeBonds side sidePositive stage rightTime
  let actionSquares := completeOpenCubeGaussianActionRowSquares
    timeBonds (bulkSourceWidth side) stage
  have noiseEquality : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) = N := by
    unfold N bulkSourceNoiseCount combGaugePlaquetteNoiseCount
    rfl
  have hleft := openCubeBulkCayleyTraceA2RowSquares_coeffEqv
    timeBonds side sidePositive stage leftTime
  have hright := openCubeBulkCayleyTraceA2RowSquares_coeffEqv
    timeBonds side sidePositive stage rightTime
  have haction := completeOpenCubeGaussianActionRowSquares_coeffEqv
    timeBonds (bulkSourceWidth side) stage
  rw [noiseEquality] at haction
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_coeffEqv N hleft hright haction)
    (finiteGaussianThirdCumulant_weighted_row_squares_triangle
      N leftSquares rightSquares actionSquares)

/-- Explicit `2+2` connected Wick value of `R4`. -/
def openCubeBulkCayleyTraceConnectedR4WickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  finiteGaussianWeightedTwoTwoCovarianceWickSum N
    ((openCubeBulkCayleyTraceA2RowSquares
      timeBonds side sidePositive stage leftTime).map
        weightedRowSquareQuadraticBlock)
    ((openCubeBulkCayleyTraceA2RowSquares
      timeBonds side sidePositive stage rightTime).map
        weightedRowSquareQuadraticBlock)

theorem openCubeBulkCayleyTraceConnectedR4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    openCubeBulkCayleyTraceConnectedR4
        timeBonds side sidePositive stage leftTime rightTime ≈
      openCubeBulkCayleyTraceConnectedR4WickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let leftSquares := openCubeBulkCayleyTraceA2RowSquares
    timeBonds side sidePositive stage leftTime
  let rightSquares := openCubeBulkCayleyTraceA2RowSquares
    timeBonds side sidePositive stage rightTime
  have hleft := (openCubeBulkCayleyTraceA2RowSquares_coeffEqv
    timeBonds side sidePositive stage leftTime).trans
      (weightedRowSquares_coeffEqv N leftSquares)
  have hright := (openCubeBulkCayleyTraceA2RowSquares_coeffEqv
    timeBonds side sidePositive stage rightTime).trans
      (weightedRowSquares_coeffEqv N rightSquares)
  unfold openCubeBulkCayleyTraceConnectedR4
    openCubeBulkCayleyTraceConnectedR4WickSum
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv N hleft hright)
    (finiteGaussianCovariance_weighted_two_two_row_blocks_wick N
      (leftSquares.map weightedRowSquareQuadraticBlock)
      (rightSquares.map weightedRowSquareQuadraticBlock))

/-- Exact finite Gram value of the connected action-scaling defect. -/
def openCubeBulkCayleyTraceHeatConnectedScalingDefectWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  openCubeBulkCayleyTraceA2A2GaussianActionThirdCumulantWickSum
      timeBonds side sidePositive stage leftTime rightTime -
    2 * openCubeBulkCayleyTraceConnectedR4WickSum
      timeBonds side sidePositive stage leftTime rightTime

theorem openCubeBulkCayleyTraceHeatConnectedScalingDefect_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    openCubeBulkCayleyTraceHeatConnectedScalingDefect
        timeBonds side sidePositive stage leftTime rightTime ≈
      openCubeBulkCayleyTraceHeatConnectedScalingDefectWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  unfold openCubeBulkCayleyTraceHeatConnectedScalingDefect
    openCubeBulkCayleyTraceHeatConnectedScalingDefectWickSum
  exact Q'.add_eqv_congr'
    (finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_A2_A2_gaussianAction_wick
      timeBonds side sidePositive stage leftTime rightTime)
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left 2 _ _
        (openCubeBulkCayleyTraceConnectedR4_wick
          timeBonds side sidePositive stage leftTime rightTime)))

/-- Complete explicit Gram certificate for the residual left after the
universal `(4/3)P4` heat-action cancellation. -/
def openCubeBulkCayleyTraceHeatP6ScalingResidualWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let leftMean := openCubeBulkCayleyTraceOwnA2MeanGramSum
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeBulkCayleyTraceOwnA2MeanGramSum
    timeBonds side sidePositive stage rightTime
  (openCubeBulkCayleyTraceHeatConnectedScalingDefectWickSum
      timeBonds side sidePositive stage leftTime rightTime +
    (leftMean - oldCenter.c2) *
      openCubeBulkCayleyTraceHeatMeanScalingDefectWickSum
        timeBonds side sidePositive stage rightTime) +
  openCubeBulkCayleyTraceHeatMeanScalingDefectWickSum
      timeBonds side sidePositive stage leftTime *
    (rightMean - oldCenter.c2)

theorem openCubeBulkCayleyTraceHeatP6ScalingResidual_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeBulkCayleyTraceHeatP6ScalingResidual
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeBulkCayleyTraceHeatP6ScalingResidualWickSum
        timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  unfold openCubeBulkCayleyTraceHeatP6ScalingResidual
    openCubeBulkCayleyTraceHeatP6ScalingResidualWickSum
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (openCubeBulkCayleyTraceHeatConnectedScalingDefect_wick
        timeBonds side sidePositive stage leftTime rightTime)
      (mul_congr
        (Q'.add_eqv_congr'
          (openCubeBulkCayleyTraceOwnA2Mean_gram
            timeBonds side sidePositive stage leftTime)
          (Q'.eqv_refl _))
        (openCubeBulkCayleyTraceHeatMeanScalingDefect_wick
          timeBonds side sidePositive stage rightTime)))
    (mul_congr
      (openCubeBulkCayleyTraceHeatMeanScalingDefect_wick
        timeBonds side sidePositive stage leftTime)
      (Q'.add_eqv_congr'
        (openCubeBulkCayleyTraceOwnA2Mean_gram
          timeBonds side sidePositive stage rightTime)
        (Q'.eqv_refl _)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatActionWick

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatActionWick.completeOpenCubeGaussianActionRowSquares_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatActionWick.finiteGaussianCovariance_openCube_bulk_cayley_trace_A2_gaussianAction_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatActionWick.finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_A2_A2_gaussianAction_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatActionWick.openCubeBulkCayleyTraceHeatConnectedScalingDefect_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatActionWick.openCubeBulkCayleyTraceHeatP6ScalingResidual_wick
