/-
# Explicit Wick certificate for the corrected heat scaling residual

This leaf compiles the corrected common-action defects

  Cov(A2,S0)-E[A2],
  kappa(A2(left),A2(right),S0)-2*R4

and their complete OLD-centered `P6` residual to finite row-Gram sums.  Every
spatial face/time and kinetic bond/link term in the corrected heat `S0` is
retained.  No Gaussian evaluator, covariance, or cumulant remains in the
final residual certificate.

This does not yet contract the sums with the checked Heron covariance defect,
prove a uniform bound or sign, compare the ORIGINAL law, control higher
remainders, or establish a continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatActionWick

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeSquareThirdCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction

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

/-- Scale the coefficient of one weighted row square without changing its
row. -/
def scaleCommonActionWeightedRowSquare
    (scale : Q') (square : WeightedRowSquare) : WeightedRowSquare :=
  { weight := scale * square.weight
    row := square.row }

private theorem weightedRowSquares_scale_terms
    (noiseCount : Nat) (scale : Q') : ∀ squares : List WeightedRowSquare,
    RatPolyCoeffEqv
      (polySum (squares.map fun square =>
        polySmul scale
          (polySmul square.weight
            (finiteGaussianRowSquare noiseCount square.row))))
      (polySum (squares.map fun square =>
        polySmul (scale * square.weight)
          (finiteGaussianRowSquare noiseCount square.row)))
  | [] => RatPolyCoeffEqv.refl _
  | square :: squares =>
      (RatPolyCoeffEqv.smul_assoc
        scale square.weight
          (finiteGaussianRowSquare noiseCount square.row)).add
        (weightedRowSquares_scale_terms noiseCount scale squares)

private theorem weightedRowSquares_scale
    (noiseCount : Nat) (scale : Q') (squares : List WeightedRowSquare) :
    RatPolyCoeffEqv
      (polySmul scale
        (weightedTermPolynomial
          (squares.map (weightedRowSquareTerm noiseCount))))
      (weightedTermPolynomial
        ((squares.map (scaleCommonActionWeightedRowSquare scale)).map
          (weightedRowSquareTerm noiseCount))) := by
  unfold weightedTermPolynomial weightedRowSquareTerm
    scaleCommonActionWeightedRowSquare
  simp only [List.map_map]
  have distribute : RatPolyCoeffEqv
      (polySmul scale
        (polySum (squares.map fun square =>
          polySmul square.weight
            (finiteGaussianRowSquare noiseCount square.row))))
      (polySum (squares.map fun square =>
        polySmul scale
          (polySmul square.weight
            (finiteGaussianRowSquare noiseCount square.row)))) := by
    simpa only [List.map_map, Function.comp_apply] using
      polySmul_polySum scale
        (squares.map fun square =>
          polySmul square.weight
            (finiteGaussianRowSquare noiseCount square.row))
  exact distribute.trans
    (weightedRowSquares_scale_terms noiseCount scale squares)

private theorem weightedTermPolynomial_append
    (left right : List (Q' × RatPoly)) :
    RatPolyCoeffEqv
      (polyAdd (weightedTermPolynomial left) (weightedTermPolynomial right))
      (weightedTermPolynomial (left ++ right)) := by
  unfold weightedTermPolynomial
  simp only [List.map_append]
  exact RatPolyCoeffEqv.polySum_append _ _

private theorem weightedRowSquares_family_coeffEqv
    {Index : Type} (noiseCount : Nat)
    (weight : Index → Q')
    (polynomial : Index → RatPoly)
    (squares : Index → List WeightedRowSquare)
    (localCertificate : ∀ index,
      RatPolyCoeffEqv (polynomial index)
        (weightedTermPolynomial
          ((squares index).map (weightedRowSquareTerm noiseCount)))) :
    ∀ indices : List Index,
    RatPolyCoeffEqv
      (polySum (indices.map fun index =>
        polySmul (weight index) (polynomial index)))
      (weightedTermPolynomial
        ((indices.flatMap fun index =>
          (squares index).map
            (scaleCommonActionWeightedRowSquare (weight index))).map
              (weightedRowSquareTerm noiseCount)))
  | [] => RatPolyCoeffEqv.refl _
  | index :: indices => by
      have hhead : RatPolyCoeffEqv
          (polySmul (weight index) (polynomial index))
          (weightedTermPolynomial
            (((squares index).map
              (scaleCommonActionWeightedRowSquare (weight index))).map
                (weightedRowSquareTerm noiseCount))) :=
        ((localCertificate index).smul (weight index)).trans
          (weightedRowSquares_scale noiseCount
            (weight index) (squares index))
      have htail := weightedRowSquares_family_coeffEqv noiseCount
        weight polynomial squares localCertificate indices
      exact (hhead.add htail).trans (by
        simp only [List.flatMap_cons, List.map_append]
        exact weightedTermPolynomial_append _ _)

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
    finiteGaussianRowSquare finiteGaussianRowWord
  simp only [List.map_map]
  exact RatPolyCoeffEqv.refl _

private def quadraticBlocksToSquares
    (blocks : List WeightedQuadraticRowBlock) : List WeightedRowSquare :=
  blocks.map fun block => { weight := block.weight, row := block.first }

private theorem polySum_congr {Index : Type}
    (left right : Index → RatPoly) : ∀ items : List Index,
    (∀ item, item ∈ items → RatPolyCoeffEqv (left item) (right item)) →
    RatPolyCoeffEqv (polySum (items.map left)) (polySum (items.map right))
  | [], _ => RatPolyCoeffEqv.refl _
  | item :: items, hypothesis =>
      (hypothesis item List.mem_cons_self).add
        (polySum_congr left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem quadraticBlocksToSquares_polynomial
    (noiseCount : Nat) (blocks : List WeightedQuadraticRowBlock)
    (diagonal : ∀ block, block ∈ blocks → block.first = block.second) :
    RatPolyCoeffEqv
      (weightedTermPolynomial
        (blocks.map (weightedQuadraticRowBlockTerm noiseCount)))
      (weightedTermPolynomial
        ((quadraticBlocksToSquares blocks).map
          (weightedRowSquareTerm noiseCount))) := by
  unfold quadraticBlocksToSquares weightedTermPolynomial
    weightedQuadraticRowBlockTerm weightedRowSquareTerm
    finiteGaussianRowSquare finiteGaussianRowWord
  simp only [List.map_map]
  exact polySum_congr _ _ blocks (fun block membership => by
    change RatPolyCoeffEqv
      (polySmul block.weight
        (polyMul
          (YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP.finiteLinearRow
            noiseCount block.first)
          (YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP.finiteLinearRow
            noiseCount block.second)))
      (polySmul block.weight
        (polyMul
          (YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP.finiteLinearRow
            noiseCount block.first)
          (YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP.finiteLinearRow
            noiseCount block.first)))
    rw [← diagonal block membership]
    exact RatPolyCoeffEqv.refl _)

private theorem heatA2Blocks_diagonal
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) (block : WeightedQuadraticRowBlock)
    (membership : block ∈ openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time) :
    block.first = block.second := by
  unfold openCubeHeatBulkCayleyTraceA2RowBlocks at membership
  simp only [List.mem_map] at membership
  rcases membership with ⟨base, baseMembership, rfl⟩
  unfold bulkSourceHeatQuadraticRowBlocks at baseMembership
  simp only [List.mem_map] at baseMembership
  rcases baseMembership with ⟨rowIndex, _rowMembership, rfl⟩
  rfl

/-- Actual heat `A2` as weighted literal row squares. -/
def openCubeHeatCayleyTraceA2RowSquares
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : List WeightedRowSquare :=
  quadraticBlocksToSquares
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)

theorem openCubeHeatCayleyTraceA2RowSquares_coeffEqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    RatPolyCoeffEqv
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage time)
      (weightedTermPolynomial
        ((openCubeHeatCayleyTraceA2RowSquares
          timeBonds side sidePositive stage time).map
            (weightedRowSquareTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  exact (openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage time).trans
      (quadraticBlocksToSquares_polynomial
        (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2RowBlocks
          timeBonds side sidePositive stage time)
        (heatA2Blocks_diagonal
          timeBonds side sidePositive stage time))

/-- Converting the literal heat `A2` squares back to diagonal quadratic
blocks recovers the original checked block list exactly. -/
theorem openCubeHeatCayleyTraceA2RowSquares_map_quadraticBlock
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    (openCubeHeatCayleyTraceA2RowSquares
        timeBonds side sidePositive stage time).map
        weightedRowSquareQuadraticBlock =
      openCubeHeatBulkCayleyTraceA2RowBlocks
        timeBonds side sidePositive stage time := by
  unfold openCubeHeatCayleyTraceA2RowSquares quadraticBlocksToSquares
  rw [List.map_map]
  conv => rhs; rw [← List.map_id
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time)]
  apply List.map_congr_left
  intro block membership
  have diagonal := heatA2Blocks_diagonal
    timeBonds side sidePositive stage time block membership
  cases block with
  | mk weight first second =>
      simp only at diagonal
      subst second
      rfl

/-- Three positive heat-row squares of one spatial action insertion. -/
def openCubeHeatPlaquetteGaussianActionRowSquares
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedRowSquare :=
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianWeightedRowNormSquares 1
    (gaussianCayleyTotalRows
      (gaussianCayleySlot (rows 0) (rows 1) (rows 2) (rows 3)))

theorem openCubeHeatPlaquetteGaussianActionRowSquares_coeffEqv
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (openCubeHeatPlaquetteGaussianActionPolynomial
        timeBonds width stage time face)
      (weightedTermPolynomial
        ((openCubeHeatPlaquetteGaussianActionRowSquares
          timeBonds width stage time face).map
            (weightedRowSquareTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  unfold openCubeHeatPlaquetteGaussianActionPolynomial
    openCubeHeatPlaquetteGaussianActionRowSquares
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  let total := gaussianCayleyTotalRows
    (gaussianCayleySlot (rows 0) (rows 1) (rows 2) (rows 3))
  exact (polySmul_one
      (finiteGaussianRowDot
        (combGaugePlaquetteNoiseCount timeBonds width) 3 total total)).symm.trans
    (finiteGaussianWeightedRowNormSquares_coeffEqv
      (combGaugePlaquetteNoiseCount timeBonds width) 1 total)

/-- Three positive heat-row temporal-difference action squares. -/
def openCubeHeatKineticGaussianActionRowSquares
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    List WeightedRowSquare :=
  finiteGaussianWeightedRowNormSquares 1
    (combGaugeHeatFreeHistoryHeronKineticDifferenceRows
      timeBonds width stage bond link)

theorem openCubeHeatKineticGaussianActionRowSquares_coeffEqv
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    RatPolyCoeffEqv
      (openCubeHeatKineticGaussianActionPolynomial
        timeBonds width stage bond link)
      (weightedTermPolynomial
        ((openCubeHeatKineticGaussianActionRowSquares
          timeBonds width stage bond link).map
            (weightedRowSquareTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  unfold openCubeHeatKineticGaussianActionPolynomial
    openCubeHeatKineticGaussianActionRowSquares
  let difference := combGaugeHeatFreeHistoryHeronKineticDifferenceRows
    timeBonds width stage bond link
  exact (polySmul_one
      (finiteGaussianRowDot
        (combGaugePlaquetteNoiseCount timeBonds width) 3
        difference difference)).symm.trans
    (finiteGaussianWeightedRowNormSquares_coeffEqv
      (combGaugePlaquetteNoiseCount timeBonds width) 1 difference)

/-- Complete weighted row-square list for corrected positive action `S0`. -/
def completeOpenCubeHeatGaussianActionRowSquares
    (timeBonds width stage : Nat) : List WeightedRowSquare :=
  ((completeOpenCubeSpatialHeatActionFourthInsertions
      timeBonds width).flatMap fun insertion =>
        (openCubeHeatPlaquetteGaussianActionRowSquares
          timeBonds width stage insertion.time insertion.face).map
            (scaleCommonActionWeightedRowSquare insertion.weight)) ++
  ((completeOpenCubeKineticFourthActionInsertions
      timeBonds width).flatMap fun insertion =>
        (openCubeHeatKineticGaussianActionRowSquares
          timeBonds width stage insertion.bond insertion.link).map
            (scaleCommonActionWeightedRowSquare insertion.weight))

theorem completeOpenCubeHeatGaussianActionRowSquares_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeHeatGaussianActionPolynomial
        timeBonds width stage)
      (weightedTermPolynomial
        ((completeOpenCubeHeatGaussianActionRowSquares
          timeBonds width stage).map
            (weightedRowSquareTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  let noiseCount := combGaugePlaquetteNoiseCount timeBonds width
  let spatialInsertions := completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width
  let kineticInsertions := completeOpenCubeKineticFourthActionInsertions
    timeBonds width
  let spatialSquares :=
    fun insertion : OpenCubeSpatialHeatActionFourthInsertion =>
      openCubeHeatPlaquetteGaussianActionRowSquares
        timeBonds width stage insertion.time insertion.face
  let kineticSquares :=
    fun insertion : OpenCubeKineticFourthActionInsertion =>
      openCubeHeatKineticGaussianActionRowSquares
        timeBonds width stage insertion.bond insertion.link
  have hspatial := weightedRowSquares_family_coeffEqv noiseCount
    (fun insertion : OpenCubeSpatialHeatActionFourthInsertion =>
      insertion.weight)
    (fun insertion => openCubeHeatPlaquetteGaussianActionPolynomial
      timeBonds width stage insertion.time insertion.face)
    spatialSquares
    (fun insertion =>
      openCubeHeatPlaquetteGaussianActionRowSquares_coeffEqv
        timeBonds width stage insertion.time insertion.face)
    spatialInsertions
  have hkinetic := weightedRowSquares_family_coeffEqv noiseCount
    (fun insertion : OpenCubeKineticFourthActionInsertion => insertion.weight)
    (fun insertion => openCubeHeatKineticGaussianActionPolynomial
      timeBonds width stage insertion.bond insertion.link)
    kineticSquares
    (fun insertion =>
      openCubeHeatKineticGaussianActionRowSquares_coeffEqv
        timeBonds width stage insertion.bond insertion.link)
    kineticInsertions
  unfold completeOpenCubeHeatGaussianActionPolynomial
    completeOpenCubeHeatSpatialGaussianActionPolynomial
    completeOpenCubeHeatKineticGaussianActionPolynomial
    completeOpenCubeHeatGaussianActionRowSquares
  refine (hspatial.add hkinetic).trans ?_
  simpa only [noiseCount, spatialInsertions, kineticInsertions,
    spatialSquares, kineticSquares, List.map_append] using
    (weightedTermPolynomial_append
      ((spatialInsertions.flatMap fun insertion =>
        (spatialSquares insertion).map
          (scaleCommonActionWeightedRowSquare insertion.weight)).map
            (weightedRowSquareTerm noiseCount))
      ((kineticInsertions.flatMap fun insertion =>
        (kineticSquares insertion).map
          (scaleCommonActionWeightedRowSquare insertion.weight)).map
            (weightedRowSquareTerm noiseCount)))

/-- Explicit covariance value of one corrected heat source against `S0`. -/
def openCubeHeatCayleyTraceA2GaussianActionCovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount
    ((openCubeHeatCayleyTraceA2RowSquares
      timeBonds side sidePositive stage time).map
        weightedRowSquareQuadraticBlock)
    ((completeOpenCubeHeatGaussianActionRowSquares
      timeBonds (bulkSourceWidth side) stage).map
        weightedRowSquareQuadraticBlock)

theorem finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_gaussianAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage time)
        (completeOpenCubeHeatGaussianActionPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceA2GaussianActionCovarianceWickSum
        timeBonds side sidePositive stage time := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let sourceSquares := openCubeHeatCayleyTraceA2RowSquares
    timeBonds side sidePositive stage time
  let actionSquares := completeOpenCubeHeatGaussianActionRowSquares
    timeBonds (bulkSourceWidth side) stage
  have noiseEquality : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) = noiseCount := by
    unfold noiseCount bulkSourceNoiseCount combGaugePlaquetteNoiseCount
    rfl
  have hsource := (openCubeHeatCayleyTraceA2RowSquares_coeffEqv
    timeBonds side sidePositive stage time).trans
      (weightedRowSquares_coeffEqv noiseCount sourceSquares)
  have hactionBase := completeOpenCubeHeatGaussianActionRowSquares_coeffEqv
    timeBonds (bulkSourceWidth side) stage
  rw [noiseEquality] at hactionBase
  have haction := hactionBase.trans
    (weightedRowSquares_coeffEqv noiseCount actionSquares)
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv noiseCount hsource haction)
    (finiteGaussianCovariance_weighted_two_two_row_blocks_wick noiseCount
      (sourceSquares.map weightedRowSquareQuadraticBlock)
      (actionSquares.map weightedRowSquareQuadraticBlock))

/-- Explicit Gram value of the corrected one-point scaling defect. -/
def openCubeHeatCayleyTraceMeanScalingDefectWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  openCubeHeatCayleyTraceA2GaussianActionCovarianceWickSum
      timeBonds side sidePositive stage time -
    openCubeHeatCayleyTraceOwnA2MeanGramSum
      timeBonds side sidePositive stage time

theorem openCubeHeatCayleyTraceMeanScalingDefect_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeHeatCayleyTraceMeanScalingDefect
        timeBonds side sidePositive stage time ≈
      openCubeHeatCayleyTraceMeanScalingDefectWickSum
        timeBonds side sidePositive stage time := by
  unfold openCubeHeatCayleyTraceMeanScalingDefect
    openCubeHeatCayleyTraceMeanScalingDefectWickSum
  exact Q'.add_eqv_congr'
    (finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_gaussianAction_wick
      timeBonds side sidePositive stage time)
    (Q'.neg_eqv_congr _ _
      (openCubeHeatCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage time))

/-- Explicit `2+2+2` Gram-triangle value for two heat sources and `S0`. -/
def openCubeHeatCayleyTraceA2A2GaussianActionThirdCumulantWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedRowSquaresTriangleSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatCayleyTraceA2RowSquares
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatCayleyTraceA2RowSquares
      timeBonds side sidePositive stage rightTime)
    (completeOpenCubeHeatGaussianActionRowSquares
      timeBonds (bulkSourceWidth side) stage)

theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_A2_A2_gaussianAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatGaussianActionPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceA2A2GaussianActionThirdCumulantWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftSquares := openCubeHeatCayleyTraceA2RowSquares
    timeBonds side sidePositive stage leftTime
  let rightSquares := openCubeHeatCayleyTraceA2RowSquares
    timeBonds side sidePositive stage rightTime
  let actionSquares := completeOpenCubeHeatGaussianActionRowSquares
    timeBonds (bulkSourceWidth side) stage
  have noiseEquality : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) = noiseCount := by
    unfold noiseCount bulkSourceNoiseCount combGaugePlaquetteNoiseCount
    rfl
  have hleft := openCubeHeatCayleyTraceA2RowSquares_coeffEqv
    timeBonds side sidePositive stage leftTime
  have hright := openCubeHeatCayleyTraceA2RowSquares_coeffEqv
    timeBonds side sidePositive stage rightTime
  have haction := completeOpenCubeHeatGaussianActionRowSquares_coeffEqv
    timeBonds (bulkSourceWidth side) stage
  rw [noiseEquality] at haction
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_coeffEqv noiseCount
      hleft hright haction)
    (finiteGaussianThirdCumulant_weighted_row_squares_triangle
      noiseCount leftSquares rightSquares actionSquares)

/-- Explicit Gram value of the corrected connected scaling defect. -/
def openCubeHeatCayleyTraceConnectedScalingDefectWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  openCubeHeatCayleyTraceA2A2GaussianActionThirdCumulantWickSum
      timeBonds side sidePositive stage leftTime rightTime -
    2 * openCubeHeatCayleyTraceConnectedR4WickSum
      timeBonds side sidePositive stage leftTime rightTime

theorem openCubeHeatCayleyTraceConnectedScalingDefect_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    openCubeHeatCayleyTraceConnectedScalingDefect
        timeBonds side sidePositive stage leftTime rightTime ≈
      openCubeHeatCayleyTraceConnectedScalingDefectWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  unfold openCubeHeatCayleyTraceConnectedScalingDefect
    openCubeHeatCayleyTraceConnectedScalingDefectWickSum
  exact Q'.add_eqv_congr'
    (finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_A2_A2_gaussianAction_wick
      timeBonds side sidePositive stage leftTime rightTime)
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left 2 _ _
        (openCubeHeatCayleyTraceConnectedR4_wick
          timeBonds side sidePositive stage leftTime rightTime)))

/-- Complete explicit Gram certificate for the corrected `P6` scaling
residual. -/
def openCubeHeatCayleyTraceP6ScalingResidualWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let leftMean := openCubeHeatCayleyTraceOwnA2MeanGramSum
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeHeatCayleyTraceOwnA2MeanGramSum
    timeBonds side sidePositive stage rightTime
  (openCubeHeatCayleyTraceConnectedScalingDefectWickSum
      timeBonds side sidePositive stage leftTime rightTime +
    (leftMean - oldCenter.c2) *
      openCubeHeatCayleyTraceMeanScalingDefectWickSum
        timeBonds side sidePositive stage rightTime) +
  openCubeHeatCayleyTraceMeanScalingDefectWickSum
      timeBonds side sidePositive stage leftTime *
    (rightMean - oldCenter.c2)

theorem openCubeHeatCayleyTraceP6ScalingResidual_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6ScalingResidual
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceP6ScalingResidualWickSum
        timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  unfold openCubeHeatCayleyTraceP6ScalingResidual
    openCubeHeatCayleyTraceP6ScalingResidualWickSum
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceConnectedScalingDefect_wick
        timeBonds side sidePositive stage leftTime rightTime)
      (mul_congr
        (Q'.add_eqv_congr'
          (openCubeHeatCayleyTraceOwnA2Mean_gram
            timeBonds side sidePositive stage leftTime)
          (Q'.eqv_refl _))
        (openCubeHeatCayleyTraceMeanScalingDefect_wick
          timeBonds side sidePositive stage rightTime)))
    (mul_congr
      (openCubeHeatCayleyTraceMeanScalingDefect_wick
        timeBonds side sidePositive stage leftTime)
      (Q'.add_eqv_congr'
        (openCubeHeatCayleyTraceOwnA2Mean_gram
          timeBonds side sidePositive stage rightTime)
        (Q'.eqv_refl _)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick.completeOpenCubeHeatGaussianActionRowSquares_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick.finiteGaussianCovariance_openCubeHeat_cayleyTrace_A2_gaussianAction_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick.finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_A2_A2_gaussianAction_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick.openCubeHeatCayleyTraceConnectedScalingDefect_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick.openCubeHeatCayleyTraceP6ScalingResidual_wick
