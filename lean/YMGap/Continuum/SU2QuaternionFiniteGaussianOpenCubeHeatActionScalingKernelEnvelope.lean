/-
# Finite Heron envelope for the complete heat action scaling kernel

The exact covariance-residual contraction from the preceding leaf is
`(C_stage-C_exact) * ((2L) * C_stage)`.  This leaf moves the right product
onto the supplied physical row and applies the existing coefficient-weighted
entrywise Heron covariance envelope.  The result is a literal finite bound
for the complete color-diagonal action scaling kernel.

The envelope is stage-, cutoff-, and row-dependent.  No uniform estimate,
neighboring-time sign, ORIGINAL-law comparison, higher-remainder control,
continuum Hamiltonian, or mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelMatrix

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionSandwichMatrix
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelMatrix

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem listQSum_sub_local {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    listQSum (fun item => left item - right item) items ≈
      listQSum left items - listQSum right items
  | [] => Q'.eqv_refl _
  | item :: items => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_sub_local left right items))
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.neg (.var 1)))
            (.add (.var 2) (.neg (.var 3))))
          (.add (.add (.var 0) (.var 2))
            (.neg (.add (.var 1) (.var 3))))
          (by decide) (fun
            | 0 => left item
            | 1 => right item
            | 2 => listQSum left items
            | _ => listQSum right items))

theorem finiteMatrixBilinear_sub_local
    (n : Nat) (leftMatrix rightMatrix : Nat → Nat → Q')
    (leftRow rightRow : Nat → Q') :
    finiteMatrixBilinear n (finiteMatrixSub leftMatrix rightMatrix)
        leftRow rightRow ≈
      finiteMatrixBilinear n leftMatrix leftRow rightRow -
        finiteMatrixBilinear n rightMatrix leftRow rightRow := by
  unfold finiteMatrixBilinear finiteMatrixSub
  simp only [qListSum_map_eq_listQSum_local]
  let indices := List.range n
  refine Q'.eqv_trans _
    (listQSum (fun left => listQSum (fun right =>
      (leftRow left * rightRow right) * leftMatrix left right -
        (leftRow left * rightRow right) * rightMatrix left right) indices)
      indices) _ ?_ ?_
  · apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1))
        (.add (.var 2) (.neg (.var 3))))
      (.add
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.neg (.mul (.mul (.var 0) (.var 1)) (.var 3))))
      (by decide) (fun
        | 0 => leftRow left
        | 1 => rightRow right
        | 2 => leftMatrix left right
        | _ => rightMatrix left right)
  · refine Q'.eqv_trans _
      (listQSum (fun left =>
        listQSum (fun right =>
          (leftRow left * rightRow right) * leftMatrix left right) indices -
        listQSum (fun right =>
          (leftRow left * rightRow right) * rightMatrix left right) indices)
        indices) _ ?_ ?_
    · apply listQSum_congr
      intro left
      exact listQSum_sub_local
        (fun right =>
          (leftRow left * rightRow right) * leftMatrix left right)
        (fun right =>
          (leftRow left * rightRow right) * rightMatrix left right)
        indices
    · exact listQSum_sub_local
        (fun left => listQSum (fun right =>
          (leftRow left * rightRow right) * leftMatrix left right) indices)
        (fun left => listQSum (fun right =>
          (leftRow left * rightRow right) * rightMatrix left right) indices)
        indices

/-- Right physical row after applying `(2L) * C_stage`. -/
def combGaugeHeatFreeHistoryPrecisionStageRightRow
    (timeBonds width stage : Nat) (rightRow : Nat → Q')
    (coordinate : Nat) : Q' :=
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteMatrixRowPairing n
    (finiteMatrixProduct n
      (combGaugeHeatFreeHistoryPrecision timeBonds width)
      (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage))
    coordinate rightRow

/-- The covariance-residual contraction is the staged covariance-error
bilinear evaluated on the transformed right row. -/
theorem covarianceResidualBilinear_eq_errorBilinear
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let transformedRight :=
      combGaugeHeatFreeHistoryPrecisionStageRightRow
        timeBonds width stage rightRow
    finiteMatrixBilinear n
        (combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
          timeBonds width stage)
        leftRow rightRow ≈
      finiteMatrixBilinear n
        (finiteMatrixSub
          (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
          (combGaugeHeatFreeHistoryCovariance timeBonds width))
        leftRow transformedRight := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let stageCovariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let exactCovariance :=
    combGaugeHeatFreeHistoryCovariance timeBonds width
  let precisionStage := finiteMatrixProduct n
    (combGaugeHeatFreeHistoryPrecision timeBonds width) stageCovariance
  let transformedRight :=
    combGaugeHeatFreeHistoryPrecisionStageRightRow
      timeBonds width stage rightRow
  unfold combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
    finiteMatrixCovarianceResidualContraction
  refine Q'.eqv_trans _
    (listQSum (fun middle =>
      finiteMatrixRowProjection n
          (finiteMatrixSub stageCovariance exactCovariance)
          leftRow middle *
        finiteMatrixRowPairing n precisionStage middle rightRow)
      (List.range n)) _
    (finiteMatrixBilinear_product n
      (finiteMatrixSub stageCovariance exactCovariance)
      precisionStage leftRow rightRow) ?_
  exact Q'.eqv_symm
    (finiteMatrixBilinear_eq_projection n
      (finiteMatrixSub stageCovariance exactCovariance)
      leftRow transformedRight)

private theorem covarianceResidualBilinear_eq_stage_sub
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let transformedRight :=
      combGaugeHeatFreeHistoryPrecisionStageRightRow
        timeBonds width stage rightRow
    finiteMatrixBilinear n
        (combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
          timeBonds width stage)
        leftRow rightRow ≈
      finiteMatrixBilinear n
          (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
          leftRow transformedRight -
        finiteMatrixBilinear n
          (combGaugeHeatFreeHistoryCovariance timeBonds width)
          leftRow transformedRight := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let stageCovariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let exactCovariance :=
    combGaugeHeatFreeHistoryCovariance timeBonds width
  let transformedRight :=
    combGaugeHeatFreeHistoryPrecisionStageRightRow
      timeBonds width stage rightRow
  refine Q'.eqv_trans _
    (finiteMatrixBilinear n
      (finiteMatrixSub stageCovariance exactCovariance)
      leftRow transformedRight) _ ?_ ?_
  · exact covarianceResidualBilinear_eq_errorBilinear
      timeBonds width stage leftRow rightRow
  · exact finiteMatrixBilinear_sub_local n
      stageCovariance exactCovariance leftRow transformedRight

/-- The complete heat covariance-residual contraction inherits the existing
coefficient-weighted finite Heron envelope after applying `(2L) * C_stage` to
the right row. -/
theorem combGaugeHeatFreeHistoryCovarianceResidualContractionBilinear_abs_le
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let transformedRight :=
      combGaugeHeatFreeHistoryPrecisionStageRightRow
        timeBonds width stage rightRow
    Q'.abs
        (finiteMatrixBilinear n
          (combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
            timeBonds width stage)
          leftRow rightRow) ≤
      combGaugeHeatFreeHistoryHeronBilinearResidualEnvelope
        timeBonds width stage leftRow transformedRight := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform :=
    combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
  let stageCovariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let exactCovariance :=
    combGaugeHeatFreeHistoryCovariance timeBonds width
  let transformedRight :=
    combGaugeHeatFreeHistoryPrecisionStageRightRow
      timeBonds width stage rightRow
  have herror := physicalCovarianceBilinear_error
    n n transform exactCovariance
    (ldlFactorResidualEnvelope n
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).lower
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).diagonal
      stage)
    leftRow transformedRight
    (fun left right hleft hright =>
      (combGaugeHeatFreeHistoryCovariance_heronFactor
        (timeBonds := timeBonds) (width := width) (stage := stage)
        hleft hright).2)
  change Q'.abs
      (finiteMatrixBilinear n stageCovariance leftRow transformedRight +
        -finiteMatrixBilinear n exactCovariance leftRow transformedRight) ≤
    combGaugeHeatFreeHistoryHeronBilinearResidualEnvelope
      timeBonds width stage leftRow transformedRight at herror
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (ExpNeg.abs_eqv_congr
        (covarianceResidualBilinear_eq_stage_sub
          timeBonds width stage leftRow rightRow)))
    herror

/-- Literal finite envelope for the complete color-resolved heat action
scaling kernel. -/
theorem completeOpenCubeHeatGaussianActionScalingKernel_abs_le
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q')
    (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (hrightComponent : rightComponent < 3) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let transform :=
      combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
    let transformedRight :=
      combGaugeHeatFreeHistoryPrecisionStageRightRow
        timeBonds width stage rightRow
    Q'.abs
        (finiteGaussianWeightedActionScalingKernel
          (combGaugePlaquetteNoiseCount timeBonds width)
          (completeOpenCubeHeatGaussianActionRowSquares
            timeBonds width stage)
          (heatColorPulledRow n transform leftRow leftComponent)
          (heatColorPulledRow n transform rightRow rightComponent)) ≤
      if leftComponent = rightComponent then
        combGaugeHeatFreeHistoryHeronBilinearResidualEnvelope
          timeBonds width stage leftRow transformedRight
      else 0 := by
  dsimp only
  have hkernel :=
    completeOpenCubeHeatGaussianActionScalingKernel_eq_covarianceResidual
      timeBonds width stage leftRow rightRow
      leftComponent rightComponent hleftComponent hrightComponent
  by_cases hcomponent : leftComponent = rightComponent
  · simp only [if_pos hcomponent] at hkernel ⊢
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hkernel))
      (combGaugeHeatFreeHistoryCovarianceResidualContractionBilinear_abs_le
        timeBonds width stage leftRow rightRow)
  · simp only [if_neg hcomponent] at hkernel ⊢
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hkernel))
      (by decide : Q'.abs (0 : Q') ≤ 0)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope.combGaugeHeatFreeHistoryCovarianceResidualContractionBilinear_abs_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope.completeOpenCubeHeatGaussianActionScalingKernel_abs_le
