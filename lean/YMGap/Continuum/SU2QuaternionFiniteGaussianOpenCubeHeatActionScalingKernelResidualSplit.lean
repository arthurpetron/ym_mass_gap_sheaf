/-
# First-order and quadratic split of the heat action scaling residual

Because `(2L) * C_exact = I`, the transformed right row satisfies

  ((2L) * C_stage) * v
    = v + (2L) * (C_stage - C_exact) * v.

Substituting this identity into the checked covariance-error contraction
splits the complete matching-color action scaling kernel into a first-order
covariance-error bilinear and a quadratic covariance-error correction.

This is an exact finite identity.  It does not bound either term uniformly,
prove a neighboring-time sign, compare the ORIGINAL law, control higher
remainders, construct a continuum Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelGeometricEnvelope

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualSplit

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionSandwichMatrix
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private def finiteMatrixAdd
    (left right : Nat → Nat → Q') (row column : Nat) : Q' :=
  left row column + right row column

private theorem finiteMatrixAdd_congr_local
    {n : Nat}
    {leftA leftB rightA rightB : Nat → Nat → Q'}
    (hleft : FiniteMatrixEqv n leftA leftB)
    (hright : FiniteMatrixEqv n rightA rightB) :
    FiniteMatrixEqv n
      (finiteMatrixAdd leftA rightA)
      (finiteMatrixAdd leftB rightB) := by
  intro row column hrow hcolumn
  unfold finiteMatrixAdd
  exact Q'.add_eqv_congr'
    (hleft hrow hcolumn) (hright hrow hcolumn)

private theorem finiteMatrixProduct_add_right_local
    (n : Nat) (left rightA rightB : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixProduct n left (finiteMatrixAdd rightA rightB))
      (finiteMatrixAdd
        (finiteMatrixProduct n left rightA)
        (finiteMatrixProduct n left rightB)) := by
  intro row column _hrow _hcolumn
  unfold finiteMatrixProduct finiteMatrixAdd
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun middle => poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.add (.mul (.var 0) (.var 1))
          (.mul (.var 0) (.var 2)))
        (by decide) (fun
          | 0 => left row middle
          | 1 => rightA middle column
          | _ => rightB middle column))
      (List.range n))
    (listQSum_add
      (fun middle => left row middle * rightA middle column)
      (fun middle => left row middle * rightB middle column)
      (List.range n))

private theorem stageCovariance_eq_exact_add_error
    (timeBonds width stage : Nat) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let stageCovariance :=
      combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
    let exactCovariance :=
      combGaugeHeatFreeHistoryCovariance timeBonds width
    FiniteMatrixEqv n stageCovariance
      (finiteMatrixAdd exactCovariance
        (finiteMatrixSub stageCovariance exactCovariance)) := by
  dsimp only
  intro row column _hrow _hcolumn
  unfold finiteMatrixAdd finiteMatrixSub
  exact poly_identity_of_normal_eq
    (.var 0)
    (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
    (by decide) (fun
      | 0 => combGaugeHeatFreeHistoryStageCovariance
          timeBonds width stage row column
      | _ => combGaugeHeatFreeHistoryCovariance
          timeBonds width row column)

private theorem precisionStage_eq_identity_add_error
    (timeBonds width stage : Nat) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let precision := combGaugeHeatFreeHistoryPrecision timeBonds width
    let stageCovariance :=
      combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
    let exactCovariance :=
      combGaugeHeatFreeHistoryCovariance timeBonds width
    FiniteMatrixEqv n
      (finiteMatrixProduct n precision stageCovariance)
      (finiteMatrixAdd finiteIdentityMatrix
        (finiteMatrixProduct n precision
          (finiteMatrixSub stageCovariance exactCovariance))) := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let precision := combGaugeHeatFreeHistoryPrecision timeBonds width
  let stageCovariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let exactCovariance :=
    combGaugeHeatFreeHistoryCovariance timeBonds width
  intro row column hrow hcolumn
  exact Q'.eqv_trans _ _ _
    (finiteMatrixProduct_congr
      (finiteMatrixEqv_refl n precision)
      (stageCovariance_eq_exact_add_error timeBonds width stage)
      hrow hcolumn)
    (Q'.eqv_trans _ _ _
      (finiteMatrixProduct_add_right_local n precision exactCovariance
        (finiteMatrixSub stageCovariance exactCovariance) hrow hcolumn)
      (finiteMatrixAdd_congr_local
        (combGaugeHeatFreeHistoryInverseData
          timeBonds width).matrix_inverse
        (finiteMatrixEqv_refl n
          (finiteMatrixProduct n precision
            (finiteMatrixSub stageCovariance exactCovariance)))
        hrow hcolumn))

private theorem finiteMatrixRowPairing_congr_local
    {n : Nat} {left right : Nat → Nat → Q'}
    (heq : FiniteMatrixEqv n left right)
    (row : Nat) (hrow : row < n) (vector : Nat → Q') :
    finiteMatrixRowPairing n left row vector ≈
      finiteMatrixRowPairing n right row vector := by
  unfold finiteMatrixRowPairing
  apply listQSum_congr_on
  intro column hcolumn
  exact Q'.mul_eqv_congr_right _ _ _
    (heq hrow (List.mem_range.mp hcolumn))

private theorem finiteMatrixRowPairing_add_local
    (n row : Nat) (left right : Nat → Nat → Q')
    (vector : Nat → Q') :
    finiteMatrixRowPairing n (finiteMatrixAdd left right) row vector ≈
      finiteMatrixRowPairing n left row vector +
        finiteMatrixRowPairing n right row vector := by
  unfold finiteMatrixRowPairing finiteMatrixAdd
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun column => poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.add (.mul (.var 0) (.var 2))
          (.mul (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => left row column
          | 1 => right row column
          | _ => vector column))
      (List.range n))
    (listQSum_add
      (fun column => left row column * vector column)
      (fun column => right row column * vector column)
      (List.range n))

private theorem finiteIdentityMatrix_rowPairing_local
    (n row : Nat) (hrow : row < n) (vector : Nat → Q') :
    finiteMatrixRowPairing n finiteIdentityMatrix row vector ≈
      vector row := by
  unfold finiteMatrixRowPairing
  change finiteMatrixProduct n finiteIdentityMatrix
      (fun source _column => vector source) row 0 ≈ vector row
  exact finiteIdentityMatrix_mul n
    (fun source _column => vector source) hrow
    (Nat.zero_lt_of_lt hrow)

/-- Residual correction in the transformed right row. -/
def combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
    (timeBonds width stage : Nat) (rightRow : Nat → Q')
    (coordinate : Nat) : Q' :=
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteMatrixRowPairing n
    (finiteMatrixProduct n
      (combGaugeHeatFreeHistoryPrecision timeBonds width)
      (finiteMatrixSub
        (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
        (combGaugeHeatFreeHistoryCovariance timeBonds width)))
    coordinate rightRow

/-- The transformed right row is exactly the original row plus one
covariance-residual correction. -/
theorem combGaugeHeatFreeHistoryPrecisionStageRightRow_eq_identity_add_residual
    (timeBonds width stage : Nat) (rightRow : Nat → Q')
    (coordinate : Nat)
    (hcoordinate : coordinate <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    combGaugeHeatFreeHistoryPrecisionStageRightRow
        timeBonds width stage rightRow coordinate ≈
      rightRow coordinate +
        combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
          timeBonds width stage rightRow coordinate := by
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let precision := combGaugeHeatFreeHistoryPrecision timeBonds width
  let stageCovariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let exactCovariance :=
    combGaugeHeatFreeHistoryCovariance timeBonds width
  unfold combGaugeHeatFreeHistoryPrecisionStageRightRow
    combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
  exact Q'.eqv_trans _ _ _
    (finiteMatrixRowPairing_congr_local
      (precisionStage_eq_identity_add_error timeBonds width stage)
      coordinate hcoordinate rightRow)
    (Q'.eqv_trans _ _ _
      (finiteMatrixRowPairing_add_local n coordinate
        finiteIdentityMatrix
        (finiteMatrixProduct n precision
          (finiteMatrixSub stageCovariance exactCovariance))
        rightRow)
      (Q'.add_eqv_congr'
        (finiteIdentityMatrix_rowPairing_local
          n coordinate hcoordinate rightRow)
        (Q'.eqv_refl _)))

private theorem finiteMatrixBilinear_congr_right_local
    (n : Nat) (matrix : Nat → Nat → Q')
    (left right right' : Nat → Q')
    (hright : ∀ index, index < n → right index ≈ right' index) :
    finiteMatrixBilinear n matrix left right ≈
      finiteMatrixBilinear n matrix left right' := by
  unfold finiteMatrixBilinear
  simp only [qListSum_map_eq_listQSum_local]
  apply listQSum_congr
  intro leftIndex
  apply listQSum_congr_on
  intro rightIndex hrightIndex
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_left (left leftIndex) _ _
      (hright rightIndex (List.mem_range.mp hrightIndex)))

private theorem finiteMatrixBilinear_add_right_local
    (n : Nat) (matrix : Nat → Nat → Q')
    (left rightA rightB : Nat → Q') :
    finiteMatrixBilinear n matrix left
        (fun index => rightA index + rightB index) ≈
      finiteMatrixBilinear n matrix left rightA +
        finiteMatrixBilinear n matrix left rightB := by
  unfold finiteMatrixBilinear
  simp only [qListSum_map_eq_listQSum_local]
  refine Q'.eqv_trans _
    (listQSum (fun leftIndex =>
      listQSum (fun rightIndex =>
        (left leftIndex * rightA rightIndex) *
            matrix leftIndex rightIndex +
          (left leftIndex * rightB rightIndex) *
            matrix leftIndex rightIndex)
        (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr
    intro leftIndex
    apply listQSum_congr
    intro rightIndex
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
        (.mul (.mul (.var 0) (.var 2)) (.var 3)))
      (by decide) (fun
        | 0 => left leftIndex
        | 1 => rightA rightIndex
        | 2 => rightB rightIndex
        | _ => matrix leftIndex rightIndex)
  · refine Q'.eqv_trans _
      (listQSum (fun leftIndex =>
        listQSum (fun rightIndex =>
          (left leftIndex * rightA rightIndex) *
            matrix leftIndex rightIndex) (List.range n) +
        listQSum (fun rightIndex =>
          (left leftIndex * rightB rightIndex) *
            matrix leftIndex rightIndex) (List.range n))
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr
      intro leftIndex
      exact listQSum_add _ _ (List.range n)
    · exact listQSum_add _ _ (List.range n)

/-- The heat covariance-residual contraction is the sum of its first-order
covariance-error bilinear and a quadratic covariance-error correction. -/
theorem covarianceResidualBilinear_eq_linear_add_quadratic
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let covarianceError := finiteMatrixSub
      (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
      (combGaugeHeatFreeHistoryCovariance timeBonds width)
    let residualRight :=
      combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
        timeBonds width stage rightRow
    finiteMatrixBilinear n
        (combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
          timeBonds width stage)
        leftRow rightRow ≈
      finiteMatrixBilinear n covarianceError leftRow rightRow +
        finiteMatrixBilinear n covarianceError leftRow residualRight := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let covarianceError := finiteMatrixSub
    (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
    (combGaugeHeatFreeHistoryCovariance timeBonds width)
  let transformedRight :=
    combGaugeHeatFreeHistoryPrecisionStageRightRow
      timeBonds width stage rightRow
  let residualRight :=
    combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
      timeBonds width stage rightRow
  refine Q'.eqv_trans _
    (finiteMatrixBilinear n covarianceError leftRow transformedRight) _
    (covarianceResidualBilinear_eq_errorBilinear
      timeBonds width stage leftRow rightRow) ?_
  refine Q'.eqv_trans _
    (finiteMatrixBilinear n covarianceError leftRow
      (fun coordinate => rightRow coordinate + residualRight coordinate)) _
    (finiteMatrixBilinear_congr_right_local n covarianceError
      leftRow transformedRight
      (fun coordinate => rightRow coordinate + residualRight coordinate)
      (fun coordinate hcoordinate =>
        combGaugeHeatFreeHistoryPrecisionStageRightRow_eq_identity_add_residual
          timeBonds width stage rightRow coordinate hcoordinate)) ?_
  exact finiteMatrixBilinear_add_right_local n covarianceError
    leftRow rightRow residualRight

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualSplit

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualSplit.combGaugeHeatFreeHistoryPrecisionStageRightRow_eq_identity_add_residual
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualSplit.covarianceResidualBilinear_eq_linear_add_quadratic
