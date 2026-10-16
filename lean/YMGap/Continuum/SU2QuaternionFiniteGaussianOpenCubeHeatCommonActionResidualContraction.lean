/-
# Heat common-action defects as one residual contraction

For a finite weighted quadratic action, define the row-pair scaling kernel

  D(u,v) = 2 * sum_a w_a <u,a><v,a> - <u,v>.

The corrected one-point common-action defect is the weighted contraction of
`D(u,u)` over the source rows.  The corrected connected defect is the weighted
contraction of `4<u,v>D(u,v)` over the two source-row families.  Thus both
defects are controlled by the same finite action-scaling residual rather than
by unrelated Wick sums.

The specialization below uses the complete heat-normalized open-cube source
and action rows.  It does not yet rewrite `D` through the entrywise Heron
covariance residual, prove a cutoff-uniform bound, compare the ORIGINAL law,
control higher remainders, or establish a continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_congr_local {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → left item ≈ right item) →
    qListSum (items.map left) ≈ qListSum (items.map right)
  | [], _ => Q'.eqv_refl _
  | item :: items, hypothesis =>
      Q'.add_eqv_congr'
        (hypothesis item List.mem_cons_self)
        (qListSum_congr_local left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem qListSum_mul_left_local {Index : Type}
    (scale : Q') (value : Index → Q') : ∀ items : List Index,
    scale * qListSum (items.map value) ≈
      qListSum (items.map fun item => scale * value item)
  | [] => Q'.mul_zero_eqv _
  | item :: items => by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv scale (value item)
          (qListSum (items.map value)))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (qListSum_mul_left_local scale value items))

private theorem qListSum_sub_local {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    qListSum (items.map left) - qListSum (items.map right) ≈
      qListSum (items.map fun item => left item - right item)
  | [] => Q'.eqv_refl _
  | item :: items => by
      exact Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1))
            (.neg (.add (.var 2) (.var 3))))
          (.add (.add (.var 0) (.neg (.var 2)))
            (.add (.var 1) (.neg (.var 3))))
          (by decide) (fun
            | 0 => left item
            | 1 => qListSum (items.map left)
            | 2 => right item
            | _ => qListSum (items.map right)))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (qListSum_sub_local left right items))

/-- A diagonal `2+2` Wick reduction is twice the squared row Gram. -/
theorem finiteGaussianTwoTwoCovarianceWickReduction_row_squares
    (noiseCount : Nat) (left right : Nat → Q') :
    finiteGaussianTwoTwoCovarianceWickReduction noiseCount
        left left right right ≈
      2 * (finiteRowGram noiseCount left right *
        finiteRowGram noiseCount left right) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finiteGaussianCovariance_two_two_row_words_wick
        noiseCount left left right right))
    (finiteGaussianCovariance_row_square noiseCount left right)

/-- Exact weighted Gram mean of a list of row squares. -/
def finiteGaussianWeightedRowSquaresMeanGramSum
    (noiseCount : Nat) (squares : List WeightedRowSquare) : Q' :=
  qListSum (squares.map fun square =>
    square.weight * finiteRowGram noiseCount square.row square.row)

/-- Failure of a weighted quadratic action to generate exact Gaussian
scaling on one row pair. -/
def finiteGaussianWeightedActionScalingKernel
    (noiseCount : Nat) (action : List WeightedRowSquare)
    (left right : Nat → Q') : Q' :=
  2 * qListSum (action.map fun actionTerm =>
      actionTerm.weight *
        (finiteRowGram noiseCount left actionTerm.row *
          finiteRowGram noiseCount right actionTerm.row)) -
    finiteRowGram noiseCount left right

/-- One-point contraction of the common action-scaling kernel. -/
def finiteGaussianWeightedMeanScalingResidualContraction
    (noiseCount : Nat) (source action : List WeightedRowSquare) : Q' :=
  qListSum (source.map fun sourceTerm =>
    sourceTerm.weight *
      finiteGaussianWeightedActionScalingKernel
        noiseCount action sourceTerm.row sourceTerm.row)

/-- Connected two-source contraction of the same action-scaling kernel. -/
def finiteGaussianWeightedConnectedScalingResidualContraction
    (noiseCount : Nat)
    (left right action : List WeightedRowSquare) : Q' :=
  qListSum (left.map fun leftTerm =>
    qListSum (right.map fun rightTerm =>
      (leftTerm.weight * rightTerm.weight) *
        (4 * finiteRowGram noiseCount leftTerm.row rightTerm.row *
          finiteGaussianWeightedActionScalingKernel
            noiseCount action leftTerm.row rightTerm.row)))

private theorem weightedRowSquareCovarianceWickSum_reduction
    (noiseCount : Nat) (left right : List WeightedRowSquare) :
    finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount
        (left.map weightedRowSquareQuadraticBlock)
        (right.map weightedRowSquareQuadraticBlock) ≈
      qListSum (left.map fun leftTerm =>
        qListSum (right.map fun rightTerm =>
          (leftTerm.weight * rightTerm.weight) *
            (2 * (finiteRowGram noiseCount leftTerm.row rightTerm.row *
              finiteRowGram noiseCount leftTerm.row rightTerm.row)))) := by
  unfold finiteGaussianWeightedTwoTwoCovarianceWickSum
    weightedRowSquareQuadraticBlock
  simp only [List.map_map]
  apply qListSum_congr_local
  intro leftTerm _leftMembership
  apply qListSum_congr_local
  intro rightTerm _rightMembership
  exact Q'.mul_eqv_congr_left _ _ _
    (finiteGaussianTwoTwoCovarianceWickReduction_row_squares
      noiseCount leftTerm.row rightTerm.row)

private theorem weightedRowSquareCovarianceInner_eq
    (noiseCount : Nat) (sourceTerm : WeightedRowSquare)
    (action : List WeightedRowSquare) :
    qListSum (action.map fun actionTerm =>
        (sourceTerm.weight * actionTerm.weight) *
          (2 * (finiteRowGram noiseCount sourceTerm.row actionTerm.row *
            finiteRowGram noiseCount sourceTerm.row actionTerm.row))) ≈
      sourceTerm.weight *
        (2 * qListSum (action.map fun actionTerm =>
          actionTerm.weight *
            (finiteRowGram noiseCount sourceTerm.row actionTerm.row *
              finiteRowGram noiseCount sourceTerm.row actionTerm.row))) := by
  let base := fun actionTerm : WeightedRowSquare =>
    actionTerm.weight *
      (finiteRowGram noiseCount sourceTerm.row actionTerm.row *
        finiteRowGram noiseCount sourceTerm.row actionTerm.row)
  have hterm :
      qListSum (action.map fun actionTerm =>
          (sourceTerm.weight * actionTerm.weight) *
            (2 * (finiteRowGram noiseCount sourceTerm.row actionTerm.row *
              finiteRowGram noiseCount sourceTerm.row actionTerm.row))) ≈
        qListSum (action.map fun actionTerm =>
          sourceTerm.weight * (2 * base actionTerm)) :=
    qListSum_congr_local _ _ action (fun actionTerm _ =>
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1))
          (.mul (.const 2) (.mul (.var 2) (.var 2))))
        (.mul (.var 0)
          (.mul (.const 2) (.mul (.var 1) (.mul (.var 2) (.var 2)))))
        (by decide) (fun
          | 0 => sourceTerm.weight
          | 1 => actionTerm.weight
          | _ => finiteRowGram noiseCount sourceTerm.row actionTerm.row))
  have htwo :
      2 * qListSum (action.map base) ≈
        qListSum (action.map fun actionTerm => 2 * base actionTerm) :=
    qListSum_mul_left_local 2 base action
  have hsource :
      sourceTerm.weight *
          qListSum (action.map fun actionTerm => 2 * base actionTerm) ≈
        qListSum (action.map fun actionTerm =>
          sourceTerm.weight * (2 * base actionTerm)) :=
    qListSum_mul_left_local sourceTerm.weight
      (fun actionTerm => 2 * base actionTerm) action
  exact Q'.eqv_trans _ _ _ hterm
    (Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left sourceTerm.weight _ _ htwo)
        hsource))

/-- The difference between a weighted row-square covariance response and its
Gaussian mean is exactly the contraction of the action-scaling kernel. -/
theorem finiteGaussianWeightedMeanScalingResidual_eq_contraction
    (noiseCount : Nat) (source action : List WeightedRowSquare) :
    finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount
        (source.map weightedRowSquareQuadraticBlock)
        (action.map weightedRowSquareQuadraticBlock) -
      finiteGaussianWeightedRowSquaresMeanGramSum noiseCount source ≈
    finiteGaussianWeightedMeanScalingResidualContraction
      noiseCount source action := by
  unfold finiteGaussianWeightedRowSquaresMeanGramSum
    finiteGaussianWeightedMeanScalingResidualContraction
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (weightedRowSquareCovarianceWickSum_reduction
        noiseCount source action)
      (Q'.eqv_refl _)) ?_
  let response := fun sourceTerm : WeightedRowSquare =>
    qListSum (action.map fun actionTerm =>
      (sourceTerm.weight * actionTerm.weight) *
        (2 * (finiteRowGram noiseCount sourceTerm.row actionTerm.row *
          finiteRowGram noiseCount sourceTerm.row actionTerm.row)))
  let mean := fun sourceTerm : WeightedRowSquare =>
    sourceTerm.weight *
      finiteRowGram noiseCount sourceTerm.row sourceTerm.row
  let residual := fun sourceTerm : WeightedRowSquare =>
    sourceTerm.weight *
      finiteGaussianWeightedActionScalingKernel
        noiseCount action sourceTerm.row sourceTerm.row
  change qListSum (source.map response) - qListSum (source.map mean) ≈
    qListSum (source.map residual)
  refine Q'.eqv_trans _ _ _
    (qListSum_sub_local response mean source) ?_
  apply qListSum_congr_local
  intro sourceTerm _sourceMembership
  unfold response mean residual finiteGaussianWeightedActionScalingKernel
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (weightedRowSquareCovarianceInner_eq noiseCount sourceTerm action)
      (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.const 2) (.var 1)))
        (.neg (.mul (.var 0) (.var 2))))
      (.mul (.var 0)
        (.add (.mul (.const 2) (.var 1)) (.neg (.var 2))))
      (by decide) (fun
        | 0 => sourceTerm.weight
        | 1 => qListSum (action.map fun actionTerm =>
            actionTerm.weight *
              (finiteRowGram noiseCount sourceTerm.row actionTerm.row *
                finiteRowGram noiseCount sourceTerm.row actionTerm.row))
        | _ => finiteRowGram noiseCount sourceTerm.row sourceTerm.row))

private theorem weightedTriangleInner_eq_kernel
    (noiseCount : Nat) (leftTerm rightTerm : WeightedRowSquare)
    (action : List WeightedRowSquare) :
    qListSum (action.map fun actionTerm =>
        leftTerm.weight * (rightTerm.weight *
          (actionTerm.weight *
            (8 * finiteRowGram noiseCount leftTerm.row rightTerm.row *
              finiteRowGram noiseCount leftTerm.row actionTerm.row *
              finiteRowGram noiseCount rightTerm.row actionTerm.row)))) -
      2 * ((leftTerm.weight * rightTerm.weight) *
        (2 * (finiteRowGram noiseCount leftTerm.row rightTerm.row *
          finiteRowGram noiseCount leftTerm.row rightTerm.row))) ≈
    (leftTerm.weight * rightTerm.weight) *
      (4 * finiteRowGram noiseCount leftTerm.row rightTerm.row *
        finiteGaussianWeightedActionScalingKernel
          noiseCount action leftTerm.row rightTerm.row) := by
  let gram := finiteRowGram noiseCount leftTerm.row rightTerm.row
  let actionSum := qListSum (action.map fun actionTerm =>
    actionTerm.weight *
      (finiteRowGram noiseCount leftTerm.row actionTerm.row *
        finiteRowGram noiseCount rightTerm.row actionTerm.row))
  have hinner :
      qListSum (action.map fun actionTerm =>
          leftTerm.weight * (rightTerm.weight *
            (actionTerm.weight *
              (8 * gram *
                finiteRowGram noiseCount leftTerm.row actionTerm.row *
                finiteRowGram noiseCount rightTerm.row actionTerm.row)))) ≈
        (leftTerm.weight * rightTerm.weight) * (8 * gram * actionSum) := by
    let base := fun actionTerm : WeightedRowSquare =>
      actionTerm.weight *
        (finiteRowGram noiseCount leftTerm.row actionTerm.row *
          finiteRowGram noiseCount rightTerm.row actionTerm.row)
    have hterm :
        qListSum (action.map fun actionTerm =>
            leftTerm.weight * (rightTerm.weight *
              (actionTerm.weight *
                (8 * gram *
                  finiteRowGram noiseCount leftTerm.row actionTerm.row *
                  finiteRowGram noiseCount rightTerm.row actionTerm.row)))) ≈
          qListSum (action.map fun actionTerm =>
            (leftTerm.weight * rightTerm.weight) *
              ((8 * gram) * base actionTerm)) :=
      qListSum_congr_local _ _ action (fun actionTerm _ =>
        poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1)
            (.mul (.var 2)
              (.mul (.mul (.mul (.const 8) (.var 3)) (.var 4))
                (.var 5)))))
          (.mul (.mul (.var 0) (.var 1))
            (.mul (.mul (.const 8) (.var 3))
              (.mul (.var 2) (.mul (.var 4) (.var 5)))))
          (by decide) (fun
            | 0 => leftTerm.weight
            | 1 => rightTerm.weight
            | 2 => actionTerm.weight
            | 3 => gram
            | 4 => finiteRowGram noiseCount leftTerm.row actionTerm.row
            | _ => finiteRowGram noiseCount rightTerm.row actionTerm.row))
    have hscaleGram :
        (8 * gram) * qListSum (action.map base) ≈
          qListSum (action.map fun actionTerm =>
            (8 * gram) * base actionTerm) :=
      qListSum_mul_left_local (8 * gram) base action
    have hscaleWeight :
        (leftTerm.weight * rightTerm.weight) *
            qListSum (action.map fun actionTerm =>
              (8 * gram) * base actionTerm) ≈
          qListSum (action.map fun actionTerm =>
            (leftTerm.weight * rightTerm.weight) *
              ((8 * gram) * base actionTerm)) :=
      qListSum_mul_left_local (leftTerm.weight * rightTerm.weight)
        (fun actionTerm => (8 * gram) * base actionTerm) action
    exact Q'.eqv_trans _ _ _ hterm
      (Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (leftTerm.weight * rightTerm.weight) _ _ hscaleGram)
          hscaleWeight))
  unfold finiteGaussianWeightedActionScalingKernel
  change _ ≈ (leftTerm.weight * rightTerm.weight) *
    (4 * gram * (2 * actionSum - gram))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hinner (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 1))
          (.mul (.mul (.const 8) (.var 2)) (.var 3)))
        (.neg (.mul (.const 2)
          (.mul (.mul (.var 0) (.var 1))
            (.mul (.const 2) (.mul (.var 2) (.var 2)))))))
      (.mul (.mul (.var 0) (.var 1))
        (.mul (.mul (.const 4) (.var 2))
          (.add (.mul (.const 2) (.var 3)) (.neg (.var 2)))))
      (by decide) (fun
        | 0 => leftTerm.weight
        | 1 => rightTerm.weight
        | 2 => gram
        | _ => actionSum))

private theorem qListSum_nested_mul_left_local {Left Right : Type}
    (scale : Q') (value : Left → Right → Q')
    (left : List Left) (right : List Right) :
    scale * qListSum (left.map fun leftTerm =>
        qListSum (right.map fun rightTerm => value leftTerm rightTerm)) ≈
      qListSum (left.map fun leftTerm =>
        qListSum (right.map fun rightTerm =>
          scale * value leftTerm rightTerm)) := by
  exact Q'.eqv_trans _ _ _
    (qListSum_mul_left_local scale
      (fun leftTerm =>
        qListSum (right.map fun rightTerm => value leftTerm rightTerm))
      left)
    (qListSum_congr_local _ _ left (fun leftTerm _ =>
      qListSum_mul_left_local scale (value leftTerm) right))

private theorem weightedRowSquareCovarianceWickSum_twice_reduction
    (noiseCount : Nat) (left right : List WeightedRowSquare) :
    2 * finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount
        (left.map weightedRowSquareQuadraticBlock)
        (right.map weightedRowSquareQuadraticBlock) ≈
      qListSum (left.map fun leftTerm =>
        qListSum (right.map fun rightTerm =>
          2 * ((leftTerm.weight * rightTerm.weight) *
            (2 * (finiteRowGram noiseCount leftTerm.row rightTerm.row *
              finiteRowGram noiseCount leftTerm.row rightTerm.row))))) := by
  let covariancePair := fun leftTerm rightTerm : WeightedRowSquare =>
    (leftTerm.weight * rightTerm.weight) *
      (2 * (finiteRowGram noiseCount leftTerm.row rightTerm.row *
        finiteRowGram noiseCount leftTerm.row rightTerm.row))
  change 2 * finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount
      (left.map weightedRowSquareQuadraticBlock)
      (right.map weightedRowSquareQuadraticBlock) ≈
    qListSum (left.map fun leftTerm =>
      qListSum (right.map fun rightTerm =>
        2 * covariancePair leftTerm rightTerm))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left 2 _ _
      (weightedRowSquareCovarianceWickSum_reduction
        noiseCount left right))
    (qListSum_nested_mul_left_local 2 covariancePair left right)

/-- The connected action response minus twice the quadratic covariance is
exactly the two-source contraction of the same scaling kernel. -/
theorem finiteGaussianWeightedConnectedScalingResidual_eq_contraction
    (noiseCount : Nat)
    (left right action : List WeightedRowSquare) :
    finiteGaussianWeightedRowSquaresTriangleSum
        noiseCount left right action -
      2 * finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount
        (left.map weightedRowSquareQuadraticBlock)
        (right.map weightedRowSquareQuadraticBlock) ≈
    finiteGaussianWeightedConnectedScalingResidualContraction
      noiseCount left right action := by
  unfold finiteGaussianWeightedRowSquaresTriangleSum
    finiteGaussianWeightedConnectedScalingResidualContraction
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (weightedRowSquareCovarianceWickSum_twice_reduction
          noiseCount left right))) ?_
  let trianglePair := fun leftTerm rightTerm : WeightedRowSquare =>
    qListSum (action.map fun actionTerm =>
      leftTerm.weight * (rightTerm.weight *
        (actionTerm.weight *
          (8 * finiteRowGram noiseCount leftTerm.row rightTerm.row *
            finiteRowGram noiseCount leftTerm.row actionTerm.row *
            finiteRowGram noiseCount rightTerm.row actionTerm.row))))
  let covariancePair := fun leftTerm rightTerm : WeightedRowSquare =>
    2 * ((leftTerm.weight * rightTerm.weight) *
      (2 * (finiteRowGram noiseCount leftTerm.row rightTerm.row *
        finiteRowGram noiseCount leftTerm.row rightTerm.row)))
  let residualPair := fun leftTerm rightTerm : WeightedRowSquare =>
    (leftTerm.weight * rightTerm.weight) *
      (4 * finiteRowGram noiseCount leftTerm.row rightTerm.row *
        finiteGaussianWeightedActionScalingKernel
          noiseCount action leftTerm.row rightTerm.row)
  let triangleRow := fun leftTerm : WeightedRowSquare =>
    qListSum (right.map (trianglePair leftTerm))
  let covarianceRow := fun leftTerm : WeightedRowSquare =>
    qListSum (right.map (covariancePair leftTerm))
  let residualRow := fun leftTerm : WeightedRowSquare =>
    qListSum (right.map (residualPair leftTerm))
  change qListSum (left.map triangleRow) -
      qListSum (left.map covarianceRow) ≈
    qListSum (left.map residualRow)
  refine Q'.eqv_trans _ _ _
    (qListSum_sub_local triangleRow covarianceRow left) ?_
  apply qListSum_congr_local
  intro leftTerm _leftMembership
  unfold triangleRow covarianceRow residualRow
  refine Q'.eqv_trans _ _ _
    (qListSum_sub_local
      (trianglePair leftTerm) (covariancePair leftTerm) right) ?_
  apply qListSum_congr_local
  intro rightTerm _rightMembership
  unfold trianglePair covariancePair residualPair
  exact weightedTriangleInner_eq_kernel
    noiseCount leftTerm rightTerm action

/-- The corrected heat one-point common-action defect as one finite residual
contraction. -/
def openCubeHeatCayleyTraceMeanScalingResidualContraction
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  finiteGaussianWeightedMeanScalingResidualContraction
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatCayleyTraceA2RowSquares
      timeBonds side sidePositive stage time)
    (completeOpenCubeHeatGaussianActionRowSquares
      timeBonds (bulkSourceWidth side) stage)

/-- The corrected heat connected common-action defect as the corresponding
two-source residual contraction. -/
def openCubeHeatCayleyTraceConnectedScalingResidualContraction
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedConnectedScalingResidualContraction
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatCayleyTraceA2RowSquares
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatCayleyTraceA2RowSquares
      timeBonds side sidePositive stage rightTime)
    (completeOpenCubeHeatGaussianActionRowSquares
      timeBonds (bulkSourceWidth side) stage)

private theorem openCubeHeatA2MeanGramSum_eq_rowSquares
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeHeatCayleyTraceOwnA2MeanGramSum
        timeBonds side sidePositive stage time ≈
      finiteGaussianWeightedRowSquaresMeanGramSum
        (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatCayleyTraceA2RowSquares
          timeBonds side sidePositive stage time) := by
  unfold openCubeHeatCayleyTraceOwnA2MeanGramSum
    finiteGaussianWeightedQuadraticExpectationGramSum
    finiteGaussianWeightedRowSquaresMeanGramSum
  rw [← openCubeHeatCayleyTraceA2RowSquares_map_quadraticBlock
    timeBonds side sidePositive stage time]
  unfold weightedRowSquareQuadraticBlock
  simp only [List.map_map]
  exact Q'.eqv_refl _

private theorem openCubeHeatR4WickSum_eq_rowSquares
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    openCubeHeatCayleyTraceConnectedR4WickSum
        timeBonds side sidePositive stage leftTime rightTime ≈
      finiteGaussianWeightedTwoTwoCovarianceWickSum
        (bulkSourceNoiseCount timeBonds side)
        ((openCubeHeatCayleyTraceA2RowSquares
          timeBonds side sidePositive stage leftTime).map
            weightedRowSquareQuadraticBlock)
        ((openCubeHeatCayleyTraceA2RowSquares
          timeBonds side sidePositive stage rightTime).map
            weightedRowSquareQuadraticBlock) := by
  unfold openCubeHeatCayleyTraceConnectedR4WickSum
  rw [openCubeHeatCayleyTraceA2RowSquares_map_quadraticBlock
      timeBonds side sidePositive stage leftTime,
    openCubeHeatCayleyTraceA2RowSquares_map_quadraticBlock
      timeBonds side sidePositive stage rightTime]
  exact Q'.eqv_refl _

theorem openCubeHeatCayleyTraceMeanScalingDefectWickSum_eq_contraction
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeHeatCayleyTraceMeanScalingDefectWickSum
        timeBonds side sidePositive stage time ≈
      openCubeHeatCayleyTraceMeanScalingResidualContraction
        timeBonds side sidePositive stage time := by
  unfold openCubeHeatCayleyTraceMeanScalingDefectWickSum
    openCubeHeatCayleyTraceA2GaussianActionCovarianceWickSum
    openCubeHeatCayleyTraceMeanScalingResidualContraction
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (openCubeHeatA2MeanGramSum_eq_rowSquares
          timeBonds side sidePositive stage time)))
    (finiteGaussianWeightedMeanScalingResidual_eq_contraction
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatCayleyTraceA2RowSquares
        timeBonds side sidePositive stage time)
      (completeOpenCubeHeatGaussianActionRowSquares
        timeBonds (bulkSourceWidth side) stage))

theorem openCubeHeatCayleyTraceConnectedScalingDefectWickSum_eq_contraction
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    openCubeHeatCayleyTraceConnectedScalingDefectWickSum
        timeBonds side sidePositive stage leftTime rightTime ≈
      openCubeHeatCayleyTraceConnectedScalingResidualContraction
        timeBonds side sidePositive stage leftTime rightTime := by
  unfold openCubeHeatCayleyTraceConnectedScalingDefectWickSum
    openCubeHeatCayleyTraceA2A2GaussianActionThirdCumulantWickSum
    openCubeHeatCayleyTraceConnectedScalingResidualContraction
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left 2 _ _
          (openCubeHeatR4WickSum_eq_rowSquares
            timeBonds side sidePositive stage leftTime rightTime))))
    (finiteGaussianWeightedConnectedScalingResidual_eq_contraction
      (bulkSourceNoiseCount timeBonds side)
      (openCubeHeatCayleyTraceA2RowSquares
        timeBonds side sidePositive stage leftTime)
      (openCubeHeatCayleyTraceA2RowSquares
        timeBonds side sidePositive stage rightTime)
      (completeOpenCubeHeatGaussianActionRowSquares
        timeBonds (bulkSourceWidth side) stage))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction.finiteGaussianWeightedMeanScalingResidual_eq_contraction
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction.finiteGaussianWeightedConnectedScalingResidual_eq_contraction
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction.openCubeHeatCayleyTraceMeanScalingDefectWickSum_eq_contraction
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction.openCubeHeatCayleyTraceConnectedScalingDefectWickSum_eq_contraction
