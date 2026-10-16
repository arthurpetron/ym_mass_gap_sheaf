/-
# Geometric envelope for the heat scaling residual right row

The residual correction

  (2L) * (C_stage - C_exact) * v

is, coordinate by coordinate, the covariance-error bilinear whose left row is
the corresponding row of `2L`.  The existing LDL/Heron entry certificate
therefore gives a stage-independent explicit coefficient times `2^-stage`.

This is a finite pointwise bound.  The coefficient may still grow with the
cutoff, volume, coordinate, or supplied row.  No uniform estimate, sign,
ORIGINAL-law comparison, continuum Hamiltonian, or mass gap is proved.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualSplit

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualRightEnvelope

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionSandwichMatrix
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualSplit

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem finiteMatrixRowPairing_product_eq_bilinear
    (n : Nat) (left right : Nat → Nat → Q')
    (row : Nat) (vector : Nat → Q') :
    finiteMatrixRowPairing n (finiteMatrixProduct n left right)
        row vector ≈
      finiteMatrixBilinear n right (fun middle => left row middle) vector := by
  unfold finiteMatrixRowPairing finiteMatrixProduct finiteMatrixBilinear
  simp only [qListSum_map_eq_listQSum_local]
  refine Q'.eqv_trans _
    (listQSum (fun column =>
      listQSum (fun middle =>
        (left row middle * right middle column) * vector column)
        (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr
    intro column
    exact Q'.eqv_symm
      (listQSum_mul_right
        (fun middle => left row middle * right middle column)
        (vector column) (List.range n))
  · refine Q'.eqv_trans _
      (listQSum (fun middle =>
        listQSum (fun column =>
          (left row middle * right middle column) * vector column)
          (List.range n))
        (List.range n)) _
      (listQSum_swap
        (fun middle column =>
          (left row middle * right middle column) * vector column)
        (List.range n) (List.range n)) ?_
    apply listQSum_congr
    intro middle
    apply listQSum_congr
    intro column
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun
        | 0 => left row middle
        | 1 => right middle column
        | _ => vector column)

/-- One row of the doubled heat precision. -/
def combGaugeHeatFreeHistoryPrecisionRow
    (timeBonds width coordinate source : Nat) : Q' :=
  combGaugeHeatFreeHistoryPrecision timeBonds width coordinate source

/-- Stage-independent coefficient for one coordinate of the residual right
row. -/
def combGaugeHeatFreeHistoryPrecisionStageResidualRightCoefficient
    (timeBonds width coordinate : Nat) (rightRow : Nat → Q') : Q' :=
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let data := combGaugeHeatFreeHistoryCovariancePositiveLDL timeBonds width
  physicalCovarianceBilinearResidualEnvelope n
    (ldlFactorResidualCoefficient n data.lower data.diagonal)
    (combGaugeHeatFreeHistoryPrecisionRow timeBonds width coordinate)
    rightRow

private theorem precisionStageResidualRightRow_eq_errorBilinear
    (timeBonds width stage : Nat) (rightRow : Nat → Q')
    (coordinate : Nat) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let covarianceError := finiteMatrixSub
      (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
      (combGaugeHeatFreeHistoryCovariance timeBonds width)
    combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
        timeBonds width stage rightRow coordinate ≈
      finiteMatrixBilinear n covarianceError
        (combGaugeHeatFreeHistoryPrecisionRow
          timeBonds width coordinate)
        rightRow := by
  dsimp only
  unfold combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
    combGaugeHeatFreeHistoryPrecisionRow
  exact finiteMatrixRowPairing_product_eq_bilinear
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryPrecision timeBonds width)
    (finiteMatrixSub
      (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
      (combGaugeHeatFreeHistoryCovariance timeBonds width))
    coordinate rightRow

/-- Every coordinate of the residual right row has an explicit
stage-independent coefficient times `2^-stage`. -/
theorem combGaugeHeatFreeHistoryPrecisionStageResidualRightRow_abs_le_geometric
    (timeBonds width stage : Nat) (rightRow : Nat → Q')
    (coordinate : Nat) :
    Q'.abs
        (combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
          timeBonds width stage rightRow coordinate) ≤
      combGaugeHeatFreeHistoryPrecisionStageResidualRightCoefficient
          timeBonds width coordinate rightRow *
        HalfPow.half ^ stage := by
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform :=
    combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
  let stageCovariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let exactCovariance :=
    combGaugeHeatFreeHistoryCovariance timeBonds width
  let precisionRow :=
    combGaugeHeatFreeHistoryPrecisionRow timeBonds width coordinate
  let entryEnvelope := ldlFactorResidualEnvelope n
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).lower
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).diagonal
    stage
  let entryCoefficient := ldlFactorResidualCoefficient n
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).lower
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).diagonal
  have herror := physicalCovarianceBilinear_error
    n n transform exactCovariance entryEnvelope
    precisionRow rightRow
    (fun left right hleft hright =>
      (combGaugeHeatFreeHistoryCovariance_heronFactor
        (timeBonds := timeBonds) (width := width) (stage := stage)
        hleft hright).2)
  change Q'.abs
      (finiteMatrixBilinear n stageCovariance precisionRow rightRow +
        -finiteMatrixBilinear n exactCovariance precisionRow rightRow) ≤
    physicalCovarianceBilinearResidualEnvelope n
      entryEnvelope precisionRow rightRow at herror
  have hresidual :
      combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
          timeBonds width stage rightRow coordinate ≈
        finiteMatrixBilinear n stageCovariance precisionRow rightRow -
          finiteMatrixBilinear n exactCovariance precisionRow rightRow := by
    exact Q'.eqv_trans _ _ _
      (precisionStageResidualRightRow_eq_errorBilinear
        timeBonds width stage rightRow coordinate)
      (finiteMatrixBilinear_sub_local n
        stageCovariance exactCovariance precisionRow rightRow)
  have henvelope := physicalResidualEnvelope_eq_coefficient_mul_half
    n stage entryEnvelope entryCoefficient precisionRow rightRow
    (fun left right =>
      ldlFactorResidualEnvelope_eq_coefficient_mul_half
        n
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal
        stage left right)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hresidual))
    (Q'.le_trans' _ _ _ herror (Q'.le_of_eqv henvelope))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualRightEnvelope

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualRightEnvelope.combGaugeHeatFreeHistoryPrecisionStageResidualRightRow_abs_le_geometric
