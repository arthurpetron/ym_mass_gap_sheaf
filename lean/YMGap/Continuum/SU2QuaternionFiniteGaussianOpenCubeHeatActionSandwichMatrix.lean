/-
# Matrix form of the complete heat action covariance sandwich

For a finite row family with Gram matrix `G` and a symmetric covariance matrix
`C`, the sum

  sum_a B_C(left,a) * B_C(right,a)

is exactly `B_{C*G*C}(left,right)`.  This leaf proves the finite identity by
explicit distributivity and Fubini, then specializes it to the complete
literal open-cube action rows.  Their checked Gram is `L`, and the rational
Heron stage covariance is symmetric, so the milestone-324 sandwich is exactly
the bilinear for `C_stage * (L * C_stage)`.

This is still a finite reference-law identity.  It does not yet include the
factor two and subtraction forming the full scaling kernel, prove a uniform
bound, compare the ORIGINAL law, control higher remainders, or establish a
continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteActionPullbackGram
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionSandwichMatrix

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompletePhysicalActionGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteActionPullbackGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem mul_congr_local {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

/-- Gram matrix of a literal finite row family. -/
def finiteRowFamilyGram
    (rows : List (Nat → Q')) (left right : Nat) : Q' :=
  listQSum (fun row => row left * row right) rows

/-- Row-vector projection through a finite matrix. -/
def finiteMatrixRowProjection
    (n : Nat) (matrix : Nat → Nat → Q')
    (row : Nat → Q') (column : Nat) : Q' :=
  listQSum (fun index => row index * matrix index column) (List.range n)

/-- Pair one finite matrix row with a supplied vector. -/
def finiteMatrixRowPairing
    (n : Nat) (matrix : Nat → Nat → Q')
    (row : Nat) (vector : Nat → Q') : Q' :=
  listQSum (fun column => matrix row column * vector column) (List.range n)

/-- Covariance sandwich over a literal finite action-row family. -/
def finiteRowFamilyCovarianceSandwich
    (n : Nat) (covariance : Nat → Nat → Q')
    (rows : List (Nat → Q')) (left right : Nat → Q') : Q' :=
  listQSum (fun row =>
    finiteMatrixBilinear n covariance left row *
      finiteMatrixBilinear n covariance right row) rows

/-- Projection-coordinate form of a row-family covariance sandwich. -/
def finiteProjectedGramSandwich
    (n : Nat) (covariance : Nat → Nat → Q')
    (rows : List (Nat → Q')) (left right : Nat → Q') : Q' :=
  listQSum (fun leftIndex =>
    listQSum (fun rightIndex =>
      (finiteMatrixRowProjection n covariance left leftIndex *
          finiteMatrixRowProjection n covariance right rightIndex) *
        finiteRowFamilyGram rows leftIndex rightIndex)
      (List.range n))
    (List.range n)

theorem finiteMatrixBilinear_eq_projection
    (n : Nat) (matrix : Nat → Nat → Q')
    (left right : Nat → Q') :
    finiteMatrixBilinear n matrix left right ≈
      listQSum (fun column =>
        finiteMatrixRowProjection n matrix left column * right column)
        (List.range n) := by
  unfold finiteMatrixBilinear finiteMatrixRowProjection
  simp only [qListSum_map_eq_listQSum_local]
  refine Q'.eqv_trans _
    (listQSum (fun row =>
      listQSum (fun column =>
        (left row * matrix row column) * right column)
        (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr
    intro row
    apply listQSum_congr
    intro column
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun
        | 0 => left row
        | 1 => right column
        | _ => matrix row column)
  · refine Q'.eqv_trans _
      (listQSum (fun column =>
        listQSum (fun row =>
          (left row * matrix row column) * right column)
          (List.range n))
        (List.range n)) _
      (listQSum_swap
        (fun column row =>
          (left row * matrix row column) * right column)
        (List.range n) (List.range n)) ?_
    apply listQSum_congr
    intro column
    exact listQSum_mul_right
      (fun row => left row * matrix row column)
      (right column) (List.range n)

private theorem finiteMatrixRowProjection_product
    (n : Nat) (leftMatrix rightMatrix : Nat → Nat → Q')
    (row : Nat → Q') (column : Nat) :
    finiteMatrixRowProjection n
        (finiteMatrixProduct n leftMatrix rightMatrix) row column ≈
      listQSum (fun middle =>
        finiteMatrixRowProjection n leftMatrix row middle *
          rightMatrix middle column)
        (List.range n) := by
  unfold finiteMatrixRowProjection finiteMatrixProduct
  refine Q'.eqv_trans _
    (listQSum (fun source =>
      listQSum (fun middle =>
        (row source * leftMatrix source middle) *
          rightMatrix middle column)
        (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (listQSum_mul_left (row source)
          (fun middle =>
            leftMatrix source middle * rightMatrix middle column)
          (List.range n)))
      (Q'.eqv_symm
        (listQSum_congr
          (fun middle => Q'.mul_assoc_eqv
            (row source) (leftMatrix source middle)
            (rightMatrix middle column))
          (List.range n)))
  · refine Q'.eqv_trans _
      (listQSum (fun middle =>
        listQSum (fun source =>
          (row source * leftMatrix source middle) *
            rightMatrix middle column)
          (List.range n))
        (List.range n)) _
      (listQSum_swap
        (fun middle source =>
          (row source * leftMatrix source middle) *
            rightMatrix middle column)
        (List.range n) (List.range n)) ?_
    apply listQSum_congr
    intro middle
    exact listQSum_mul_right
      (fun source => row source * leftMatrix source middle)
      (rightMatrix middle column) (List.range n)

private theorem finiteMatrixRowPairing_product_transpose
    (n : Nat) (leftMatrix rightMatrix : Nat → Nat → Q')
    (row : Nat) (vector : Nat → Q') :
    finiteMatrixRowPairing n
        (finiteMatrixProduct n leftMatrix
          (finiteMatrixTranspose rightMatrix)) row vector ≈
      listQSum (fun middle =>
        leftMatrix row middle *
          finiteMatrixRowProjection n rightMatrix vector middle)
        (List.range n) := by
  unfold finiteMatrixRowPairing finiteMatrixProduct finiteMatrixTranspose
    finiteMatrixRowProjection
  refine Q'.eqv_trans _
    (listQSum (fun column =>
      listQSum (fun middle =>
        (leftMatrix row middle * rightMatrix column middle) *
          vector column)
        (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr
    intro column
    exact Q'.eqv_symm
      (listQSum_mul_right
        (fun middle => leftMatrix row middle * rightMatrix column middle)
        (vector column) (List.range n))
  · refine Q'.eqv_trans _
      (listQSum (fun middle =>
        listQSum (fun column =>
          (leftMatrix row middle * rightMatrix column middle) *
            vector column)
          (List.range n))
        (List.range n)) _
      (listQSum_swap
        (fun middle column =>
          (leftMatrix row middle * rightMatrix column middle) *
            vector column)
        (List.range n) (List.range n)) ?_
    apply listQSum_congr
    intro middle
    refine Q'.eqv_trans _
      (listQSum (fun column =>
        leftMatrix row middle *
          (vector column * rightMatrix column middle))
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr
      intro column
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 2) (.var 1)))
        (by decide) (fun
          | 0 => leftMatrix row middle
          | 1 => rightMatrix column middle
          | _ => vector column)
    · exact listQSum_mul_left (leftMatrix row middle)
        (fun column => vector column * rightMatrix column middle)
        (List.range n)

theorem finiteMatrixBilinear_product
    (n : Nat) (leftMatrix rightMatrix : Nat → Nat → Q')
    (left right : Nat → Q') :
    finiteMatrixBilinear n
        (finiteMatrixProduct n leftMatrix rightMatrix) left right ≈
      listQSum (fun middle =>
        finiteMatrixRowProjection n leftMatrix left middle *
          finiteMatrixRowPairing n rightMatrix middle right)
        (List.range n) := by
  refine Q'.eqv_trans _ _ _
    (finiteMatrixBilinear_eq_projection n
      (finiteMatrixProduct n leftMatrix rightMatrix) left right) ?_
  refine Q'.eqv_trans _
    (listQSum (fun column =>
      listQSum (fun middle =>
        finiteMatrixRowProjection n leftMatrix left middle *
          rightMatrix middle column)
        (List.range n) * right column)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr
    intro column
    exact Q'.mul_eqv_congr_right _ _ _
      (finiteMatrixRowProjection_product n
        leftMatrix rightMatrix left column)
  · refine Q'.eqv_trans _
      (listQSum (fun column =>
        listQSum (fun middle =>
          (finiteMatrixRowProjection n leftMatrix left middle *
              rightMatrix middle column) * right column)
          (List.range n))
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr
      intro column
      exact Q'.eqv_symm
        (listQSum_mul_right
          (fun middle =>
            finiteMatrixRowProjection n leftMatrix left middle *
              rightMatrix middle column)
          (right column) (List.range n))
    · refine Q'.eqv_trans _
        (listQSum (fun middle =>
          listQSum (fun column =>
            (finiteMatrixRowProjection n leftMatrix left middle *
                rightMatrix middle column) * right column)
            (List.range n))
          (List.range n)) _
        (listQSum_swap
          (fun middle column =>
            (finiteMatrixRowProjection n leftMatrix left middle *
                rightMatrix middle column) * right column)
          (List.range n) (List.range n)) ?_
      apply listQSum_congr
      intro middle
      refine Q'.eqv_trans _
        (listQSum (fun column =>
          finiteMatrixRowProjection n leftMatrix left middle *
            (rightMatrix middle column * right column))
          (List.range n)) _ ?_ ?_
      · apply listQSum_congr
        intro column
        exact Q'.mul_assoc_eqv _ _ _
      · exact listQSum_mul_left
          (finiteMatrixRowProjection n leftMatrix left middle)
          (fun column => rightMatrix middle column * right column)
          (List.range n)

private theorem finiteRowFamilyCovarianceSandwich_eq_projected
    (n : Nat) (covariance : Nat → Nat → Q')
    (rows : List (Nat → Q')) (left right : Nat → Q') :
    finiteRowFamilyCovarianceSandwich n covariance rows left right ≈
      finiteProjectedGramSandwich n covariance rows left right := by
  unfold finiteRowFamilyCovarianceSandwich finiteProjectedGramSandwich
  let indices := List.range n
  let leftProjection := finiteMatrixRowProjection n covariance left
  let rightProjection := finiteMatrixRowProjection n covariance right
  refine Q'.eqv_trans _
    (listQSum (fun row =>
      listQSum (fun leftIndex =>
        listQSum (fun rightIndex =>
          (leftProjection leftIndex * row leftIndex) *
            (rightProjection rightIndex * row rightIndex))
          indices)
        indices)
      rows) _ ?_ ?_
  · apply listQSum_congr
    intro row
    exact Q'.eqv_trans _ _ _
      (mul_congr_local
        (finiteMatrixBilinear_eq_projection n covariance left row)
        (finiteMatrixBilinear_eq_projection n covariance right row))
      (Q'.eqv_symm
        (listQSum_product
          (fun leftIndex => leftProjection leftIndex * row leftIndex)
          (fun rightIndex => rightProjection rightIndex * row rightIndex)
          indices indices))
  · refine Q'.eqv_trans _
      (listQSum (fun leftIndex =>
        listQSum (fun row =>
          listQSum (fun rightIndex =>
            (leftProjection leftIndex * row leftIndex) *
              (rightProjection rightIndex * row rightIndex))
            indices)
          rows)
        indices) _
      (listQSum_swap
        (fun leftIndex row =>
          listQSum (fun rightIndex =>
            (leftProjection leftIndex * row leftIndex) *
              (rightProjection rightIndex * row rightIndex))
            indices)
        indices rows) ?_
    apply listQSum_congr
    intro leftIndex
    refine Q'.eqv_trans _
      (listQSum (fun rightIndex =>
        listQSum (fun row =>
          (leftProjection leftIndex * row leftIndex) *
            (rightProjection rightIndex * row rightIndex))
          rows)
        indices) _
      (listQSum_swap
        (fun rightIndex row =>
          (leftProjection leftIndex * row leftIndex) *
            (rightProjection rightIndex * row rightIndex))
        indices rows) ?_
    apply listQSum_congr
    intro rightIndex
    refine Q'.eqv_trans _
      (listQSum (fun row =>
        (leftProjection leftIndex * rightProjection rightIndex) *
          (row leftIndex * row rightIndex)) rows) _ ?_ ?_
    · apply listQSum_congr
      intro row
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun
          | 0 => leftProjection leftIndex
          | 1 => row leftIndex
          | 2 => rightProjection rightIndex
          | _ => row rightIndex)
    · exact listQSum_mul_left
        (leftProjection leftIndex * rightProjection rightIndex)
        (fun row => row leftIndex * row rightIndex) rows

private theorem finiteProjectedGramSandwich_eq_matrixBilinear
    (n : Nat) (covariance : Nat → Nat → Q')
    (rows : List (Nat → Q')) (left right : Nat → Q') :
    finiteProjectedGramSandwich n covariance rows left right ≈
      finiteMatrixBilinear n
        (finiteMatrixProduct n covariance
          (finiteMatrixProduct n (finiteRowFamilyGram rows)
            (finiteMatrixTranspose covariance)))
        left right := by
  let indices := List.range n
  let leftProjection := finiteMatrixRowProjection n covariance left
  let rightProjection := finiteMatrixRowProjection n covariance right
  have hmatrix := finiteMatrixBilinear_product n covariance
    (finiteMatrixProduct n (finiteRowFamilyGram rows)
      (finiteMatrixTranspose covariance)) left right
  refine Q'.eqv_trans _
    (listQSum (fun leftIndex =>
      leftProjection leftIndex *
        finiteMatrixRowPairing n
          (finiteMatrixProduct n (finiteRowFamilyGram rows)
            (finiteMatrixTranspose covariance))
          leftIndex right)
      indices) _ ?_ (Q'.eqv_symm hmatrix)
  unfold finiteProjectedGramSandwich
  apply listQSum_congr
  intro leftIndex
  refine Q'.eqv_trans _
    (listQSum (fun rightIndex =>
      leftProjection leftIndex *
        (finiteRowFamilyGram rows leftIndex rightIndex *
          rightProjection rightIndex)) indices) _ ?_ ?_
  · apply listQSum_congr
    intro rightIndex
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1)))
      (by decide) (fun
        | 0 => leftProjection leftIndex
        | 1 => rightProjection rightIndex
        | _ => finiteRowFamilyGram rows leftIndex rightIndex)
  · refine Q'.eqv_trans _
      (leftProjection leftIndex *
        listQSum (fun rightIndex =>
          finiteRowFamilyGram rows leftIndex rightIndex *
            rightProjection rightIndex) indices) _ ?_ ?_
    · exact listQSum_mul_left (leftProjection leftIndex)
        (fun rightIndex =>
          finiteRowFamilyGram rows leftIndex rightIndex *
            rightProjection rightIndex) indices
    · exact Q'.mul_eqv_congr_left (leftProjection leftIndex) _ _
        (Q'.eqv_symm
          (finiteMatrixRowPairing_product_transpose n
            (finiteRowFamilyGram rows) covariance leftIndex right))

/-- Generic finite identity: a covariance sandwich over a row family is the
bilinear form for `C * Gram(rows) * Cᵀ`. -/
theorem finiteRowFamilyCovarianceSandwich_eq_matrixBilinear
    (n : Nat) (covariance : Nat → Nat → Q')
    (rows : List (Nat → Q')) (left right : Nat → Q') :
    finiteRowFamilyCovarianceSandwich n covariance rows left right ≈
      finiteMatrixBilinear n
        (finiteMatrixProduct n covariance
          (finiteMatrixProduct n (finiteRowFamilyGram rows)
            (finiteMatrixTranspose covariance)))
        left right := by
  exact Q'.eqv_trans _ _ _
    (finiteRowFamilyCovarianceSandwich_eq_projected
      n covariance rows left right)
    (finiteProjectedGramSandwich_eq_matrixBilinear
      n covariance rows left right)

/-- Literal complete physical action-row list in the same order as the
corrected spatial-plus-kinetic insertion families. -/
def completeOpenCubePhysicalActionRows
    (timeBonds width : Nat) : List (Nat → Q') :=
  ((completeOpenCubeSpatialHeatActionFourthInsertions
      timeBonds width).map fun insertion =>
        combGaugeFreeHistoryPlaquettePhysicalActionRow
          width insertion.time insertion.face) ++
  ((completeOpenCubeKineticFourthActionInsertions
      timeBonds width).map fun insertion =>
        combGaugeFreeHistoryKineticPhysicalActionRow
          width insertion.bond insertion.link)

private theorem completePhysicalRows_gram_eq_literal
    (timeBonds width left right : Nat) :
    finiteRowFamilyGram
        (completeOpenCubePhysicalActionRows timeBonds width) left right ≈
      combGaugeFreeHistoryLiteralPhysicalActionGram
        timeBonds width left right := by
  unfold finiteRowFamilyGram completeOpenCubePhysicalActionRows
    combGaugeFreeHistoryLiteralPhysicalActionGram
  refine Q'.eqv_trans _ _ _
    (listQSum_append
      (fun row : Nat → Q' => row left * row right) _ _) ?_
  exact Q'.add_eqv_congr'
    (by
      rw [listQSum_map]
      unfold completeOpenCubeSpatialHeatActionFourthInsertions
      refine Q'.eqv_trans _ _ _
        (listQSum_flatMap _ _ (List.range (timeBonds + 1))) ?_
      apply listQSum_congr
      intro time
      rw [listQSum_map]
      exact Q'.eqv_refl _)
    (by
      rw [listQSum_map]
      unfold completeOpenCubeKineticFourthActionInsertions
      refine Q'.eqv_trans _ _ _
        (listQSum_flatMap _ _ (List.range timeBonds)) ?_
      apply listQSum_congr
      intro bond
      rw [listQSum_map]
      exact Q'.eqv_refl _)

private theorem completePhysicalRows_gram_eq_precision
    (timeBonds width : Nat) :
    FiniteMatrixEqv
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (finiteRowFamilyGram
        (completeOpenCubePhysicalActionRows timeBonds width))
      (combGaugeFreeHistoryPrecision timeBonds width) := by
  intro left right hleft hright
  exact Q'.eqv_trans _ _ _
    (completePhysicalRows_gram_eq_literal
      timeBonds width left right)
    (combGaugeFreeHistoryLiteralPhysicalActionGram_eq_precision
      timeBonds width left right hleft hright)

private theorem stageCovariance_symmetric
    (timeBonds width stage : Nat) :
    FiniteMatrixEqv
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (finiteMatrixTranspose
        (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage))
      (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage) := by
  intro left right _hleft _hright
  unfold finiteMatrixTranspose combGaugeHeatFreeHistoryStageCovariance
    factorCovariance
  simp only [qListSum_map_eq_listQSum_local]
  apply listQSum_congr
  intro noise
  exact Q'.mul_comm_eqv _ _

private theorem literalSandwich_eq_rowFamily
    (timeBonds width stage : Nat) (left right : Nat → Q') :
    combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich
        timeBonds width stage left right ≈
      finiteRowFamilyCovarianceSandwich
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
        (completeOpenCubePhysicalActionRows timeBonds width)
        left right := by
  unfold combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich
    finiteRowFamilyCovarianceSandwich
    completeOpenCubePhysicalActionRows
    combGaugeHeatFreeHistoryStageCovariance
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (listQSum_append _ _ _) ?_)
  exact Q'.add_eqv_congr'
    (by
      rw [listQSum_map]
      unfold completeOpenCubeSpatialHeatActionFourthInsertions
      refine Q'.eqv_trans _ _ _
        (listQSum_flatMap _ _ (List.range (timeBonds + 1))) ?_
      apply listQSum_congr
      intro time
      rw [listQSum_map]
      exact Q'.eqv_refl _)
    (by
      rw [listQSum_map]
      unfold completeOpenCubeKineticFourthActionInsertions
      refine Q'.eqv_trans _ _ _
        (listQSum_flatMap _ _ (List.range timeBonds)) ?_
      apply listQSum_congr
      intro bond
      rw [listQSum_map]
      exact Q'.eqv_refl _)

/-- The complete literal heat action covariance sandwich is exactly the
physical bilinear form for `C_stage * (L * C_stage)`. -/
theorem combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich_eq_matrix
    (timeBonds width stage : Nat) (left right : Nat → Q') :
    combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich
        timeBonds width stage left right ≈
      finiteMatrixBilinear
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (finiteMatrixProduct
          (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
          (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
          (finiteMatrixProduct
            (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
            (combGaugeFreeHistoryPrecision timeBonds width)
            (combGaugeHeatFreeHistoryStageCovariance
              timeBonds width stage)))
        left right := by
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let covariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let rows := completeOpenCubePhysicalActionRows timeBonds width
  refine Q'.eqv_trans _ _ _
    (literalSandwich_eq_rowFamily
      timeBonds width stage left right) ?_
  refine Q'.eqv_trans _ _ _
    (finiteRowFamilyCovarianceSandwich_eq_matrixBilinear
      n covariance rows left right) ?_
  apply finiteMatrixBilinear_congr
  exact finiteMatrixProduct_congr
    (finiteMatrixEqv_refl n covariance)
    (finiteMatrixProduct_congr
      (completePhysicalRows_gram_eq_precision timeBonds width)
      (stageCovariance_symmetric timeBonds width stage))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionSandwichMatrix

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionSandwichMatrix.finiteRowFamilyCovarianceSandwich_eq_matrixBilinear
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionSandwichMatrix.combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich_eq_matrix
