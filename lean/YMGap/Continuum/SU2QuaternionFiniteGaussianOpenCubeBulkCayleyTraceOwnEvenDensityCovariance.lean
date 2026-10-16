/-
# Exact OWN covariance with the complete even density

The fourth trace-source OWN mean contains

  Cov(A2, J2 - V4_spatial - V4_kinetic).

This leaf compiles that literal common-carrier covariance to finite row sums.
The Cayley-Haar and quadratic action pieces use weighted `2+2` covariance
contractions; the quartic action pieces use the checked weighted `2+4`
compiler.  Every history slice, internal spatial face, temporal bond, and
comb-gauge link in the canonical finite families is retained.

This is finite FREE reference algebra.  It proves no sign, cutoff-uniform
bound, ORIGINAL-law comparison, higher-remainder estimate, or physical mass
gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
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
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

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

/-- Covariance is additive in its right polynomial slot. -/
theorem finiteGaussianCovariance_add_right
    (N : Nat) (left right₁ right₂ : RatPoly) :
    finiteGaussianCovariance N left (polyAdd right₁ right₂) ≈
      finiteGaussianCovariance N left right₁ +
        finiteGaussianCovariance N left right₂ := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N
          (RatPolyCoeffEqv.mul_add_right left right₁ right₂))
        (gaussian_add N (polyMul left right₁) (polyMul left right₂)))
      (Q'.neg_eqv_congr _ _
        (mul_congr (Q'.eqv_refl _)
          (gaussian_add N right₁ right₂))))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.add (.var 3) (.var 4)))))
      (.add
        (.add (.var 0) (.neg (.mul (.var 2) (.var 3))))
        (.add (.var 1) (.neg (.mul (.var 2) (.var 4)))))
      (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul left right₁)
        | 1 => finiteProductGaussian N (polyMul left right₂)
        | 2 => finiteProductGaussian N left
        | 3 => finiteProductGaussian N right₁
        | _ => finiteProductGaussian N right₂))

/-- A rational scalar pulls out of the right covariance slot. -/
theorem finiteGaussianCovariance_smul_right
    (N : Nat) (weight : Q') (left right : RatPoly) :
    finiteGaussianCovariance N left (polySmul weight right) ≈
      weight * finiteGaussianCovariance N left right := by
  have product : finiteProductGaussian N
        (polyMul left (polySmul weight right)) ≈
      weight * finiteProductGaussian N (polyMul left right) :=
    Q'.eqv_trans _ _ _
      (finiteProductGaussian_coeffEqv N
        (RatPolyCoeffEqv.polyMul_smul_right weight left right))
      (gaussian_smul N weight (polyMul left right))
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' product
      (Q'.neg_eqv_congr _ _
        (mul_congr (Q'.eqv_refl _)
          (gaussian_smul N weight right))))
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.mul (.var 0) (.var 3)))))
      (.mul (.var 0)
        (.add (.var 1) (.neg (.mul (.var 2) (.var 3)))))
      (by decide) (fun
        | 0 => weight
        | 1 => finiteProductGaussian N (polyMul left right)
        | 2 => finiteProductGaussian N left
        | _ => finiteProductGaussian N right))

/-- Exact connected four-row reduction of a quadratic/quadratic covariance. -/
def finiteGaussianTwoTwoCovarianceWickReduction
    (N : Nat) (a b c d : Nat → Q') : Q' :=
  finiteGaussianRowWickStep N a [b, c, d] -
    finiteRowGram N a b * finiteRowGram N c d

theorem finiteGaussianCovariance_two_two_row_words_wick
    (N : Nat) (a b c d : Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d]) ≈
      finiteGaussianTwoTwoCovarianceWickReduction N a b c d := by
  have productPolynomial : RatPolyCoeffEqv
      (polyMul
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d]))
      (finiteGaussianRowWord N [a, b, c, d]) :=
    finiteGaussianRowWord_append_nonempty N a c [b] [d]
  have productValue := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N productPolynomial)
    (finiteProductGaussian_row_word_wick N a b [c, d])
  have leftValue := finiteProductGaussian_two_row_word N a b
  have rightValue := finiteProductGaussian_two_row_word N c d
  unfold finiteGaussianCovariance
    finiteGaussianTwoTwoCovarianceWickReduction
  exact Q'.add_eqv_congr' productValue
    (Q'.neg_eqv_congr _ _ (mul_congr leftValue rightValue))

/-- Explicit weighted double sum of connected `2+2` Wick reductions. -/
def finiteGaussianWeightedTwoTwoCovarianceWickSum
    (N : Nat)
    (left right : List WeightedQuadraticRowBlock) : Q' :=
  qListSum (left.map fun leftTerm =>
    qListSum (right.map fun rightTerm =>
      (leftTerm.weight * rightTerm.weight) *
        finiteGaussianTwoTwoCovarianceWickReduction N
          leftTerm.first leftTerm.second
          rightTerm.first rightTerm.second))

/-- Covariance of two finite weighted quadratic row-block sums is the
displayed double connected four-row Wick sum. -/
theorem finiteGaussianCovariance_weighted_two_two_row_blocks_wick
    (N : Nat)
    (left right : List WeightedQuadraticRowBlock) :
    finiteGaussianCovariance N
        (weightedTermPolynomial
          (left.map (weightedQuadraticRowBlockTerm N)))
        (weightedTermPolynomial
          (right.map (weightedQuadraticRowBlockTerm N))) ≈
      finiteGaussianWeightedTwoTwoCovarianceWickSum N left right := by
  let quadraticPolynomial := fun quadratic : WeightedQuadraticRowBlock =>
    polySmul quadratic.weight
      (finiteGaussianRowWord N [quadratic.first, quadratic.second])
  let reduced := fun leftTerm : WeightedQuadraticRowBlock =>
    fun rightTerm : WeightedQuadraticRowBlock =>
      (leftTerm.weight * rightTerm.weight) *
        finiteGaussianTwoTwoCovarianceWickReduction N
          leftTerm.first leftTerm.second
          rightTerm.first rightTerm.second
  unfold weightedTermPolynomial weightedQuadraticRowBlockTerm
    finiteGaussianWeightedTwoTwoCovarianceWickSum
  simp only [List.map_map]
  change finiteGaussianCovariance N
      (polySum (left.map quadraticPolynomial))
      (polySum (right.map quadraticPolynomial)) ≈
    qListSum (left.map fun leftTerm =>
      qListSum (right.map (reduced leftTerm)))
  have expandLeft :
      finiteGaussianCovariance N
          (polySum (left.map quadraticPolynomial))
          (polySum (right.map quadraticPolynomial)) ≈
        qListSum (left.map fun leftTerm =>
          finiteGaussianCovariance N (quadraticPolynomial leftTerm)
            (polySum (right.map quadraticPolynomial))) := by
    simpa only [List.map_map, Function.comp_apply] using
      finiteGaussianCovariance_polySum_left N
        (polySum (right.map quadraticPolynomial))
        (left.map quadraticPolynomial)
  have reduceLeft :
      qListSum (left.map fun leftTerm =>
          finiteGaussianCovariance N (quadraticPolynomial leftTerm)
            (polySum (right.map quadraticPolynomial))) ≈
        qListSum (left.map fun leftTerm =>
          qListSum (right.map (reduced leftTerm))) := by
    exact finiteGaussianCovariance_qListSum_congr _ _ left
      (fun leftTerm _ => by
        have expandRight :
            finiteGaussianCovariance N (quadraticPolynomial leftTerm)
                (polySum (right.map quadraticPolynomial)) ≈
              qListSum (right.map fun rightTerm =>
                finiteGaussianCovariance N (quadraticPolynomial leftTerm)
                  (quadraticPolynomial rightTerm)) := by
          simpa only [List.map_map, Function.comp_apply] using
            finiteGaussianCovariance_polySum_right N
              (quadraticPolynomial leftTerm)
              (right.map quadraticPolynomial)
        have reduceRight :
            qListSum (right.map fun rightTerm =>
                finiteGaussianCovariance N (quadraticPolynomial leftTerm)
                  (quadraticPolynomial rightTerm)) ≈
              qListSum (right.map (reduced leftTerm)) := by
          exact finiteGaussianCovariance_qListSum_congr _ _ right
            (fun rightTerm _ => by
              exact Q'.eqv_trans _ _ _
                (finiteGaussianCovariance_smul N
                  leftTerm.weight rightTerm.weight _ _)
                (Q'.mul_eqv_congr_left _ _ _
                  (finiteGaussianCovariance_two_two_row_words_wick N
                    leftTerm.first leftTerm.second
                    rightTerm.first rightTerm.second)))
        exact Q'.eqv_trans _ _ _ expandRight reduceRight)
  exact Q'.eqv_trans _ _ _ expandLeft reduceLeft

/-- View one weighted row square as an ordered quadratic row block. -/
def weightedRowSquareQuadraticBlock
    (square : WeightedRowSquare) : WeightedQuadraticRowBlock :=
  { weight := square.weight
    first := square.row
    second := square.row }

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

private theorem openCubeNormalizedH4Certificate
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
        timeBonds width stage time face)
      (weightedTermPolynomial
        ((openCubePlaquetteNormalizedH4RowBlocks
          timeBonds width stage time face).map
            (weightedQuarticRowBlockTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  let N := combGaugePlaquetteNoiseCount timeBonds width
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  have certificate :=
    finiteGaussianNormalizedCayleyH4Polynomial_quarticTerms
      N (rows 0) (rows 1) (rows 2) (rows 3)
  rw [finiteGaussianNormalizedCayleyH4QuarticTerms_eq_rowBlocks]
    at certificate
  unfold combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
    openCubePlaquetteNormalizedH4RowBlocks
  exact certificate

/-- Exact local covariance with one complete spatial fourth-action
coefficient. -/
def openCubeCayleyTraceA2SpatialV4LocalWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime insertionTime : Nat) (face : Z4Plaq) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  let source := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage sourceTime
  spatialHeatQuarter *
      finiteGaussianWeightedTwoFourCovarianceWickSum N source
        (openCubePlaquetteNormalizedH4RowBlocks
          timeBonds (bulkSourceWidth side) stage insertionTime face) +
    (finiteGaussianWeightedTwoFourCovarianceWickSum N source
        (openCubePlaquetteH2SquareActionRowBlocks
          timeBonds (bulkSourceWidth side) stage insertionTime face) +
      finiteGaussianWeightedTwoTwoCovarianceWickSum N source
        ((openCubePlaquetteH2ActionRowSquares
          timeBonds (bulkSourceWidth side) stage insertionTime face).map
            weightedRowSquareQuadraticBlock))

theorem finiteGaussianCovariance_openCube_cayley_trace_A2_spatialV4_local_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime insertionTime : Nat) (face : Z4Plaq) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (weightedTermPolynomial
          ((openCubeBulkCayleyTraceA2RowBlocks
            timeBonds side sidePositive stage sourceTime).map
              (weightedQuadraticRowBlockTerm
                (bulkSourceNoiseCount timeBonds side))))
        (combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
          timeBonds (bulkSourceWidth side) stage insertionTime face) ≈
      openCubeCayleyTraceA2SpatialV4LocalWickSum
        timeBonds side sidePositive stage sourceTime insertionTime face := by
  let N := bulkSourceNoiseCount timeBonds side
  let width := bulkSourceWidth side
  let sourceBlocks := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage sourceTime
  let source := weightedTermPolynomial
    (sourceBlocks.map (weightedQuadraticRowBlockTerm N))
  let f4 := combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
    timeBonds width stage insertionTime face
  let f4Blocks := openCubePlaquetteNormalizedH4RowBlocks
    timeBonds width stage insertionTime face
  let h2square := finiteGaussianCayleyH2SquareActionPolynomial N
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage insertionTime face) 0)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage insertionTime face) 1)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage insertionTime face) 2)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage insertionTime face) 3)
  let h2squareBlocks := openCubePlaquetteH2SquareActionRowBlocks
    timeBonds width stage insertionTime face
  let h2 := finiteGaussianCayleyH2ActionPolynomial N
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage insertionTime face) 0)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage insertionTime face) 1)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage insertionTime face) 2)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage insertionTime face) 3)
  let h2Squares := openCubePlaquetteH2ActionRowSquares
    timeBonds width stage insertionTime face
  let h2Blocks := h2Squares.map weightedRowSquareQuadraticBlock
  have noiseEquality : combGaugePlaquetteNoiseCount timeBonds width = N := by
    unfold width N bulkSourceWidth bulkSourceNoiseCount
    rfl
  have hf4Base : finiteGaussianCovariance N source f4 ≈
      finiteGaussianWeightedTwoFourCovarianceWickSum N
        sourceBlocks f4Blocks := by
    exact Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv N (RatPolyCoeffEqv.refl _)
        (by
          rw [← noiseEquality]
          exact openCubeNormalizedH4Certificate
            timeBonds width stage insertionTime face))
      (finiteGaussianCovariance_weighted_two_four_row_blocks_wick
        N sourceBlocks f4Blocks)
  have hf4 : finiteGaussianCovariance N source
        (polySmul spatialHeatQuarter f4) ≈
      spatialHeatQuarter *
        finiteGaussianWeightedTwoFourCovarianceWickSum N
          sourceBlocks f4Blocks :=
    Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_smul_right N spatialHeatQuarter source f4)
      (Q'.mul_eqv_congr_left spatialHeatQuarter _ _ hf4Base)
  have hh2square : finiteGaussianCovariance N source h2square ≈
      finiteGaussianWeightedTwoFourCovarianceWickSum N
        sourceBlocks h2squareBlocks := by
    exact finiteGaussianCovariance_weighted_two_four_row_blocks_wick
      N sourceBlocks h2squareBlocks
  have hh2 : finiteGaussianCovariance N source h2 ≈
      finiteGaussianWeightedTwoTwoCovarianceWickSum N
        sourceBlocks h2Blocks := by
    exact Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv N (RatPolyCoeffEqv.refl _)
        (weightedRowSquares_coeffEqv N h2Squares))
      (finiteGaussianCovariance_weighted_two_two_row_blocks_wick
        N sourceBlocks h2Blocks)
  have splitOuter := finiteGaussianCovariance_add_right N source
    (polySmul spatialHeatQuarter f4) (polyAdd h2square h2)
  have splitInner := finiteGaussianCovariance_add_right N source h2square h2
  unfold combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
    finiteGaussianSpatialHeatActionFourthPolynomial
    openCubeCayleyTraceA2SpatialV4LocalWickSum
  exact Q'.eqv_trans _ _ _ splitOuter
    (Q'.add_eqv_congr' hf4
      (Q'.eqv_trans _ _ _ splitInner
        (Q'.add_eqv_congr' hh2square hh2)))

/-- Exact local covariance with one complete kinetic fourth-action
coefficient. -/
def openCubeCayleyTraceA2KineticV4LocalWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime bond : Nat) (link : Z4Link) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  let source := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage sourceTime
  finiteGaussianWeightedTwoFourCovarianceWickSum N source
      (openCubeKineticFourthActionQuarticRowBlocks
        timeBonds (bulkSourceWidth side) stage bond link) +
    finiteGaussianWeightedTwoTwoCovarianceWickSum N source
      ((openCubeKineticFourthActionQuadraticRowSquares
        timeBonds (bulkSourceWidth side) stage bond link).map
          weightedRowSquareQuadraticBlock)

theorem finiteGaussianCovariance_openCube_cayley_trace_A2_kineticV4_local_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime bond : Nat) (link : Z4Link) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (weightedTermPolynomial
          ((openCubeBulkCayleyTraceA2RowBlocks
            timeBonds side sidePositive stage sourceTime).map
              (weightedQuadraticRowBlockTerm
                (bulkSourceNoiseCount timeBonds side))))
        (combGaugeFreeHistoryKineticFourthActionPolynomial
          timeBonds (bulkSourceWidth side) stage bond link) ≈
      openCubeCayleyTraceA2KineticV4LocalWickSum
        timeBonds side sidePositive stage sourceTime bond link := by
  let N := bulkSourceNoiseCount timeBonds side
  let sourceBlocks := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage sourceTime
  let source := weightedTermPolynomial
    (sourceBlocks.map (weightedQuadraticRowBlockTerm N))
  let quarticBlocks := openCubeKineticFourthActionQuarticRowBlocks
    timeBonds (bulkSourceWidth side) stage bond link
  let quadraticSquares := openCubeKineticFourthActionQuadraticRowSquares
    timeBonds (bulkSourceWidth side) stage bond link
  let quadraticBlocks := quadraticSquares.map weightedRowSquareQuadraticBlock
  let quartic := weightedTermPolynomial
    (quarticBlocks.map (weightedQuarticRowBlockTerm N))
  let quadratic := weightedTermPolynomial
    (quadraticSquares.map (weightedRowSquareTerm N))
  have hquartic : finiteGaussianCovariance N source quartic ≈
      finiteGaussianWeightedTwoFourCovarianceWickSum N
        sourceBlocks quarticBlocks :=
    finiteGaussianCovariance_weighted_two_four_row_blocks_wick
      N sourceBlocks quarticBlocks
  have hquadratic : finiteGaussianCovariance N source quadratic ≈
      finiteGaussianWeightedTwoTwoCovarianceWickSum N
        sourceBlocks quadraticBlocks := by
    exact Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv N (RatPolyCoeffEqv.refl _)
        (weightedRowSquares_coeffEqv N quadraticSquares))
      (finiteGaussianCovariance_weighted_two_two_row_blocks_wick
        N sourceBlocks quadraticBlocks)
  unfold combGaugeFreeHistoryKineticFourthActionPolynomial
    finiteGaussianKineticFourthActionPolynomial
    finiteGaussianKineticFourthActionQuarticPolynomial
    finiteGaussianKineticFourthActionQuadraticPolynomial
    openCubeCayleyTraceA2KineticV4LocalWickSum
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_add_right N source quartic quadratic)
    (Q'.add_eqv_congr' hquartic hquadratic)

/-- Exact local covariance with one product-Cayley Haar `J2` coefficient. -/
def openCubeCayleyTraceA2HaarJ2LocalWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime insertionTime : Nat) (link : Z4Link) : Q' :=
  finiteGaussianWeightedTwoTwoCovarianceWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage sourceTime)
    ((openCubeCayleyHaarJ2RowSquares
      timeBonds (bulkSourceWidth side) stage insertionTime link).map
        weightedRowSquareQuadraticBlock)

theorem finiteGaussianCovariance_openCube_cayley_trace_A2_haarJ2_local_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime insertionTime : Nat) (link : Z4Link) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (weightedTermPolynomial
          ((openCubeBulkCayleyTraceA2RowBlocks
            timeBonds side sidePositive stage sourceTime).map
              (weightedQuadraticRowBlockTerm
                (bulkSourceNoiseCount timeBonds side))))
        (combGaugeFreeHistoryCayleyHaarJ2Polynomial
          timeBonds (bulkSourceWidth side) stage insertionTime link) ≈
      openCubeCayleyTraceA2HaarJ2LocalWickSum
        timeBonds side sidePositive stage sourceTime insertionTime link := by
  let N := bulkSourceNoiseCount timeBonds side
  let sourceBlocks := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage sourceTime
  let squares := openCubeCayleyHaarJ2RowSquares
    timeBonds (bulkSourceWidth side) stage insertionTime link
  let blocks := squares.map weightedRowSquareQuadraticBlock
  unfold combGaugeFreeHistoryCayleyHaarJ2Polynomial
    finiteGaussianCayleyHaarJ2Polynomial
    openCubeCayleyTraceA2HaarJ2LocalWickSum
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv N (RatPolyCoeffEqv.refl _)
      (weightedRowSquares_coeffEqv N squares))
    (finiteGaussianCovariance_weighted_two_two_row_blocks_wick
      N sourceBlocks blocks)

private theorem qListSum_congr {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → left item ≈ right item) →
    qListSum (items.map left) ≈ qListSum (items.map right)
  | [], _ => Q'.eqv_refl _
  | item :: items, hypothesis =>
      Q'.add_eqv_congr'
        (hypothesis item List.mem_cons_self)
        (qListSum_congr left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

/-- Complete spatial `V4` covariance as a finite weighted family sum. -/
def openCubeBulkCayleyTraceA2CompleteSpatialV4CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime : Nat) : Q' :=
  qListSum ((completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds (bulkSourceWidth side)).map fun insertion =>
      insertion.weight *
        openCubeCayleyTraceA2SpatialV4LocalWickSum
          timeBonds side sidePositive stage sourceTime
          insertion.time insertion.face)

theorem finiteGaussianCovariance_openCube_cayley_trace_A2_completeSpatialV4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage sourceTime)
        (completeOpenCubeSpatialHeatActionFourthPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceA2CompleteSpatialV4CovarianceWickSum
        timeBonds side sidePositive stage sourceTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let sourceBlocks := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage sourceTime
  let source := weightedTermPolynomial
    (sourceBlocks.map (weightedQuadraticRowBlockTerm N))
  let insertions := completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds (bulkSourceWidth side)
  let polynomials := insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
        timeBonds (bulkSourceWidth side) stage
        insertion.time insertion.face)
  have sourceCertificate := openCubeBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage sourceTime
  have hsource : finiteGaussianCovariance N
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage sourceTime)
        (polySum polynomials) ≈
      finiteGaussianCovariance N source (polySum polynomials) :=
    finiteGaussianCovariance_coeffEqv N sourceCertificate
      (RatPolyCoeffEqv.refl _)
  have hsum := finiteGaussianCovariance_polySum_right N source polynomials
  have hterms : qListSum (polynomials.map fun polynomial =>
        finiteGaussianCovariance N source polynomial) ≈
      openCubeBulkCayleyTraceA2CompleteSpatialV4CovarianceWickSum
        timeBonds side sidePositive stage sourceTime := by
    unfold polynomials
      openCubeBulkCayleyTraceA2CompleteSpatialV4CovarianceWickSum
    simp only [List.map_map]
    exact qListSum_congr _ _ insertions (fun insertion _ =>
      Q'.eqv_trans _ _ _
        (finiteGaussianCovariance_smul_right N insertion.weight source _)
        (Q'.mul_eqv_congr_left insertion.weight _ _
          (finiteGaussianCovariance_openCube_cayley_trace_A2_spatialV4_local_wick
            timeBonds side sidePositive stage sourceTime
            insertion.time insertion.face)))
  unfold completeOpenCubeSpatialHeatActionFourthPolynomial
    openCubeSpatialHeatActionFourthInsertionPolynomial
  exact Q'.eqv_trans _ _ _ hsource
    (Q'.eqv_trans _ _ _ hsum hterms)

/-- Complete kinetic `V4` covariance as a finite weighted family sum. -/
def openCubeBulkCayleyTraceA2CompleteKineticV4CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime : Nat) : Q' :=
  qListSum ((completeOpenCubeKineticFourthActionInsertions
    timeBonds (bulkSourceWidth side)).map fun insertion =>
      insertion.weight *
        openCubeCayleyTraceA2KineticV4LocalWickSum
          timeBonds side sidePositive stage sourceTime
          insertion.bond insertion.link)

theorem finiteGaussianCovariance_openCube_cayley_trace_A2_completeKineticV4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage sourceTime)
        (completeOpenCubeKineticFourthActionPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceA2CompleteKineticV4CovarianceWickSum
        timeBonds side sidePositive stage sourceTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let sourceBlocks := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage sourceTime
  let source := weightedTermPolynomial
    (sourceBlocks.map (weightedQuadraticRowBlockTerm N))
  let insertions := completeOpenCubeKineticFourthActionInsertions
    timeBonds (bulkSourceWidth side)
  let polynomials := insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryKineticFourthActionPolynomial
        timeBonds (bulkSourceWidth side) stage
        insertion.bond insertion.link)
  have hsource := finiteGaussianCovariance_coeffEqv N
    (openCubeBulkCayleyTraceA2_coeffEqv
      timeBonds side sidePositive stage sourceTime)
    (RatPolyCoeffEqv.refl (polySum polynomials))
  have hsum := finiteGaussianCovariance_polySum_right N source polynomials
  have hterms : qListSum (polynomials.map fun polynomial =>
        finiteGaussianCovariance N source polynomial) ≈
      openCubeBulkCayleyTraceA2CompleteKineticV4CovarianceWickSum
        timeBonds side sidePositive stage sourceTime := by
    unfold polynomials
      openCubeBulkCayleyTraceA2CompleteKineticV4CovarianceWickSum
    simp only [List.map_map]
    exact qListSum_congr _ _ insertions (fun insertion _ =>
      Q'.eqv_trans _ _ _
        (finiteGaussianCovariance_smul_right N insertion.weight source _)
        (Q'.mul_eqv_congr_left insertion.weight _ _
          (finiteGaussianCovariance_openCube_cayley_trace_A2_kineticV4_local_wick
            timeBonds side sidePositive stage sourceTime
            insertion.bond insertion.link)))
  unfold completeOpenCubeKineticFourthActionPolynomial
    openCubeKineticFourthActionInsertionPolynomial
  exact Q'.eqv_trans _ _ _ hsource
    (Q'.eqv_trans _ _ _ hsum hterms)

/-- Complete product-Cayley `J2` covariance as a finite weighted family sum. -/
def openCubeBulkCayleyTraceA2CompleteHaarJ2CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime : Nat) : Q' :=
  qListSum ((completeOpenCubeCayleyHaarJ2Insertions
    timeBonds (bulkSourceWidth side)).map fun insertion =>
      insertion.weight *
        openCubeCayleyTraceA2HaarJ2LocalWickSum
          timeBonds side sidePositive stage sourceTime
          insertion.time insertion.link)

theorem finiteGaussianCovariance_openCube_cayley_trace_A2_completeHaarJ2_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage sourceTime)
        (completeOpenCubeCayleyHaarJ2Polynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceA2CompleteHaarJ2CovarianceWickSum
        timeBonds side sidePositive stage sourceTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let sourceBlocks := openCubeBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage sourceTime
  let source := weightedTermPolynomial
    (sourceBlocks.map (weightedQuadraticRowBlockTerm N))
  let insertions := completeOpenCubeCayleyHaarJ2Insertions
    timeBonds (bulkSourceWidth side)
  let polynomials := insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryCayleyHaarJ2Polynomial
        timeBonds (bulkSourceWidth side) stage
        insertion.time insertion.link)
  have hsource := finiteGaussianCovariance_coeffEqv N
    (openCubeBulkCayleyTraceA2_coeffEqv
      timeBonds side sidePositive stage sourceTime)
    (RatPolyCoeffEqv.refl (polySum polynomials))
  have hsum := finiteGaussianCovariance_polySum_right N source polynomials
  have hterms : qListSum (polynomials.map fun polynomial =>
        finiteGaussianCovariance N source polynomial) ≈
      openCubeBulkCayleyTraceA2CompleteHaarJ2CovarianceWickSum
        timeBonds side sidePositive stage sourceTime := by
    unfold polynomials
      openCubeBulkCayleyTraceA2CompleteHaarJ2CovarianceWickSum
    simp only [List.map_map]
    exact qListSum_congr _ _ insertions (fun insertion _ =>
      Q'.eqv_trans _ _ _
        (finiteGaussianCovariance_smul_right N insertion.weight source _)
        (Q'.mul_eqv_congr_left insertion.weight _ _
          (finiteGaussianCovariance_openCube_cayley_trace_A2_haarJ2_local_wick
            timeBonds side sidePositive stage sourceTime
            insertion.time insertion.link)))
  unfold completeOpenCubeCayleyHaarJ2Polynomial
    openCubeCayleyHaarJ2InsertionPolynomial
  exact Q'.eqv_trans _ _ _ hsource
    (Q'.eqv_trans _ _ _ hsum hterms)

/-- Explicit complete finite Wick value of `Cov(A2,J2-V4)`. -/
def openCubeBulkCayleyTraceA2J2MinusV4CovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime : Nat) : Q' :=
  openCubeBulkCayleyTraceA2CompleteHaarJ2CovarianceWickSum
      timeBonds side sidePositive stage sourceTime +
    ((-1) *
      openCubeBulkCayleyTraceA2CompleteSpatialV4CovarianceWickSum
        timeBonds side sidePositive stage sourceTime +
      (-1) *
        openCubeBulkCayleyTraceA2CompleteKineticV4CovarianceWickSum
          timeBonds side sidePositive stage sourceTime)

/-- The literal common-carrier covariance with `J2-V4_spatial-V4_kinetic`
is exactly the displayed complete finite Wick-family expression. -/
theorem finiteGaussianCovariance_openCube_bulk_cayley_trace_A2_J2MinusV4_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage sourceTime : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage sourceTime)
        (completeOpenCubeJ2MinusV4Polynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeBulkCayleyTraceA2J2MinusV4CovarianceWickSum
        timeBonds side sidePositive stage sourceTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let A2 := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage sourceTime
  let haar := completeOpenCubeCayleyHaarJ2Polynomial
    timeBonds (bulkSourceWidth side) stage
  let spatial := completeOpenCubeSpatialHeatActionFourthPolynomial
    timeBonds (bulkSourceWidth side) stage
  let kinetic := completeOpenCubeKineticFourthActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  have hhaar :=
    finiteGaussianCovariance_openCube_cayley_trace_A2_completeHaarJ2_wick
      timeBonds side sidePositive stage sourceTime
  have hspatialBase :=
    finiteGaussianCovariance_openCube_cayley_trace_A2_completeSpatialV4_wick
      timeBonds side sidePositive stage sourceTime
  have hkineticBase :=
    finiteGaussianCovariance_openCube_cayley_trace_A2_completeKineticV4_wick
      timeBonds side sidePositive stage sourceTime
  have hspatial : finiteGaussianCovariance N A2 (polySmul (-1) spatial) ≈
      (-1) *
        openCubeBulkCayleyTraceA2CompleteSpatialV4CovarianceWickSum
          timeBonds side sidePositive stage sourceTime :=
    Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_smul_right N (-1) A2 spatial)
      (Q'.mul_eqv_congr_left (-1) _ _ hspatialBase)
  have hkinetic : finiteGaussianCovariance N A2 (polySmul (-1) kinetic) ≈
      (-1) *
        openCubeBulkCayleyTraceA2CompleteKineticV4CovarianceWickSum
          timeBonds side sidePositive stage sourceTime :=
    Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_smul_right N (-1) A2 kinetic)
      (Q'.mul_eqv_congr_left (-1) _ _ hkineticBase)
  have splitOuter := finiteGaussianCovariance_add_right N A2 haar
    (polyAdd (polySmul (-1) spatial) (polySmul (-1) kinetic))
  have splitInner := finiteGaussianCovariance_add_right N A2
    (polySmul (-1) spatial) (polySmul (-1) kinetic)
  unfold completeOpenCubeJ2MinusV4Polynomial
    openCubeBulkCayleyTraceA2J2MinusV4CovarianceWickSum
  exact Q'.eqv_trans _ _ _ splitOuter
    (Q'.add_eqv_congr' hhaar
      (Q'.eqv_trans _ _ _ splitInner
        (Q'.add_eqv_congr' hspatial hkinetic)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance.finiteGaussianCovariance_weighted_two_two_row_blocks_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance.finiteGaussianCovariance_openCube_cayley_trace_A2_completeSpatialV4_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance.finiteGaussianCovariance_openCube_cayley_trace_A2_completeKineticV4_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance.finiteGaussianCovariance_openCube_cayley_trace_A2_completeHaarJ2_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance.finiteGaussianCovariance_openCube_bulk_cayley_trace_A2_J2MinusV4_wick
