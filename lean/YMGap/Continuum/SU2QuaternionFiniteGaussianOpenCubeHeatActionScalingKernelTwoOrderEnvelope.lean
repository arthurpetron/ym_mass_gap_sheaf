/-
# First-order and quadratic geometric envelope for the heat scaling kernel

The exact residual split and the pointwise residual-right estimate combine to
give a literal finite bound

  firstCoefficient * 2^-stage
    + quadraticCoefficient * 2^-stage * 2^-stage.

Both coefficients are explicit finite rational sums and are independent of
the Heron stage.  They may still grow with cutoff, volume, or supplied rows.
No uniform estimate, sign, ORIGINAL-law comparison, continuum Hamiltonian, or
mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualRightEnvelope

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelTwoOrderEnvelope

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.Q'
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
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelMatrix
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualRightEnvelope

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem listQSum_mono_local {Index : Type}
    (lower upper : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | item :: items, hypothesis =>
      Q'.add_le_add
        (hypothesis item List.mem_cons_self)
        (listQSum_mono_local lower upper items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem heatResidualEntryCoefficient_nonnegative
    (timeBonds width left right : Nat) :
    (0 : Q') ≤
      ldlFactorResidualCoefficient
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal
        left right := by
  unfold ldlFactorResidualCoefficient
  apply listQSum_nonnegative_on
  intro index hindex
  apply Q'.mul_nonneg
  · exact CReal.errAt_nonneg
      ((combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).diagonal index)
      (finiteLDLPositiveDiagonalCheck_pos
        (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
          timeBonds width)
        (List.mem_range.mp hindex)) 0
  · exact Q'.abs_nonneg _

/-- Stage-independent coefficient of the first-order covariance-error term. -/
def combGaugeHeatFreeHistoryActionScalingFirstOrderCoefficient
    (timeBonds width : Nat) (leftRow rightRow : Nat → Q') : Q' :=
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let data := combGaugeHeatFreeHistoryCovariancePositiveLDL timeBonds width
  physicalCovarianceBilinearResidualEnvelope n
    (ldlFactorResidualCoefficient n data.lower data.diagonal)
    leftRow rightRow

/-- Stage-independent coefficient of the quadratic covariance-error term. -/
def combGaugeHeatFreeHistoryActionScalingQuadraticCoefficient
    (timeBonds width : Nat) (leftRow rightRow : Nat → Q') : Q' :=
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let data := combGaugeHeatFreeHistoryCovariancePositiveLDL timeBonds width
  let entryCoefficient :=
    ldlFactorResidualCoefficient n data.lower data.diagonal
  listQSum
    (fun left => listQSum
      (fun right =>
        (Q'.abs (leftRow left) *
            combGaugeHeatFreeHistoryPrecisionStageResidualRightCoefficient
              timeBonds width right rightRow) *
          entryCoefficient left right)
      (List.range n))
    (List.range n)

private theorem physicalResidualCoefficientEnvelope_right_abs_le
    (timeBonds width stage : Nat)
    (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let data := combGaugeHeatFreeHistoryCovariancePositiveLDL timeBonds width
    let entryCoefficient :=
      ldlFactorResidualCoefficient n data.lower data.diagonal
    physicalCovarianceBilinearResidualEnvelope n entryCoefficient
        leftRow
        (combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
          timeBonds width stage rightRow) ≤
      combGaugeHeatFreeHistoryActionScalingQuadraticCoefficient
          timeBonds width leftRow rightRow *
        HalfPow.half ^ stage := by
  dsimp only
  unfold physicalCovarianceBilinearResidualEnvelope
    combGaugeHeatFreeHistoryActionScalingQuadraticCoefficient
  simp only [qListSum_map_eq_listQSum_local]
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let entryCoefficient := ldlFactorResidualCoefficient n
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).lower
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).diagonal
  let residualRight :=
    combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
      timeBonds width stage rightRow
  let residualCoefficient := fun coordinate =>
    combGaugeHeatFreeHistoryPrecisionStageResidualRightCoefficient
      timeBonds width coordinate rightRow
  let stageFactor := HalfPow.half ^ stage
  refine Q'.le_trans' _
    (listQSum (fun left => listQSum
      (fun right =>
        ((Q'.abs (leftRow left) * residualCoefficient right) *
            entryCoefficient left right) * stageFactor)
      (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_mono_local
    intro left hleft
    apply listQSum_mono_local
    intro right hright
    have habs := ExpNeg.abs_mul_le (leftRow left) (residualRight right)
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.abs (leftRow left))
      (combGaugeHeatFreeHistoryPrecisionStageResidualRightRow_abs_le_geometric
        timeBonds width stage rightRow right)
      (Q'.abs_nonneg (leftRow left))
    have hentry := heatResidualEntryCoefficient_nonnegative
      timeBonds width left right
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _
        (entryCoefficient left right) habs hentry)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _
          (entryCoefficient left right) hscaled hentry)
        (Q'.le_of_eqv
          (poly_identity_of_normal_eq
            (.mul
              (.mul (.var 0) (.mul (.var 1) (.var 2)))
              (.var 3))
            (.mul
              (.mul (.mul (.var 0) (.var 1)) (.var 3))
              (.var 2))
            (by decide) (fun
              | 0 => Q'.abs (leftRow left)
              | 1 => residualCoefficient right
              | 2 => stageFactor
              | _ => entryCoefficient left right))))
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (listQSum_congr
          (fun left => listQSum_mul_right
            (fun right =>
              (Q'.abs (leftRow left) * residualCoefficient right) *
                entryCoefficient left right)
            stageFactor (List.range n))
          (List.range n))
        (listQSum_mul_right
          (fun left => listQSum
            (fun right =>
              (Q'.abs (leftRow left) * residualCoefficient right) *
                entryCoefficient left right)
            (List.range n))
          stageFactor (List.range n)))

private theorem covarianceErrorBilinear_abs_le_geometric
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let covarianceError := finiteMatrixSub
      (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
      (combGaugeHeatFreeHistoryCovariance timeBonds width)
    Q'.abs (finiteMatrixBilinear n covarianceError leftRow rightRow) ≤
      combGaugeHeatFreeHistoryActionScalingFirstOrderCoefficient
          timeBonds width leftRow rightRow *
        HalfPow.half ^ stage := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform :=
    combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
  let stageCovariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let exactCovariance :=
    combGaugeHeatFreeHistoryCovariance timeBonds width
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
    n n transform exactCovariance entryEnvelope leftRow rightRow
    (fun left right hleft hright =>
      (combGaugeHeatFreeHistoryCovariance_heronFactor
        (timeBonds := timeBonds) (width := width) (stage := stage)
        hleft hright).2)
  change Q'.abs
      (finiteMatrixBilinear n stageCovariance leftRow rightRow +
        -finiteMatrixBilinear n exactCovariance leftRow rightRow) ≤
    physicalCovarianceBilinearResidualEnvelope n
      entryEnvelope leftRow rightRow at herror
  have hsub := finiteMatrixBilinear_sub_local n
    stageCovariance exactCovariance leftRow rightRow
  have henvelope := physicalResidualEnvelope_eq_coefficient_mul_half
    n stage entryEnvelope entryCoefficient leftRow rightRow
    (fun left right =>
      ldlFactorResidualEnvelope_eq_coefficient_mul_half
        n
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal
        stage left right)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hsub))
    (Q'.le_trans' _ _ _ herror (Q'.le_of_eqv henvelope))

private theorem quadraticCovarianceErrorBilinear_abs_le_geometric
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let covarianceError := finiteMatrixSub
      (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
      (combGaugeHeatFreeHistoryCovariance timeBonds width)
    let residualRight :=
      combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
        timeBonds width stage rightRow
    Q'.abs (finiteMatrixBilinear n covarianceError leftRow residualRight) ≤
      (combGaugeHeatFreeHistoryActionScalingQuadraticCoefficient
          timeBonds width leftRow rightRow *
        HalfPow.half ^ stage) *
        HalfPow.half ^ stage := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform :=
    combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
  let stageCovariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let exactCovariance :=
    combGaugeHeatFreeHistoryCovariance timeBonds width
  let residualRight :=
    combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
      timeBonds width stage rightRow
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
    n n transform exactCovariance entryEnvelope leftRow residualRight
    (fun left right hleft hright =>
      (combGaugeHeatFreeHistoryCovariance_heronFactor
        (timeBonds := timeBonds) (width := width) (stage := stage)
        hleft hright).2)
  change Q'.abs
      (finiteMatrixBilinear n stageCovariance leftRow residualRight +
        -finiteMatrixBilinear n exactCovariance leftRow residualRight) ≤
    physicalCovarianceBilinearResidualEnvelope n
      entryEnvelope leftRow residualRight at herror
  have hsub := finiteMatrixBilinear_sub_local n
    stageCovariance exactCovariance leftRow residualRight
  have henvelope := physicalResidualEnvelope_eq_coefficient_mul_half
    n stage entryEnvelope entryCoefficient leftRow residualRight
    (fun left right =>
      ldlFactorResidualEnvelope_eq_coefficient_mul_half
        n
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal
        stage left right)
  have hcoefficient := physicalResidualCoefficientEnvelope_right_abs_le
    timeBonds width stage leftRow rightRow
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hsub))
    (Q'.le_trans' _ _ _ herror
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv henvelope)
        (Q'.mul_le_mul_of_nonneg_right _ _
          (HalfPow.half ^ stage) hcoefficient
          (Q'.pow_nonneg _ HalfPow.half_nonneg stage))))

/-- The covariance-residual contraction has an explicit first-order
`2^-stage` term plus a quadratic `2^-2stage` term. -/
theorem combGaugeHeatFreeHistoryCovarianceResidualContractionBilinear_abs_le_two_order
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    Q'.abs
        (finiteMatrixBilinear n
          (combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
            timeBonds width stage)
          leftRow rightRow) ≤
      combGaugeHeatFreeHistoryActionScalingFirstOrderCoefficient
          timeBonds width leftRow rightRow *
        HalfPow.half ^ stage +
      (combGaugeHeatFreeHistoryActionScalingQuadraticCoefficient
          timeBonds width leftRow rightRow *
        HalfPow.half ^ stage) *
        HalfPow.half ^ stage := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let covarianceError := finiteMatrixSub
    (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
    (combGaugeHeatFreeHistoryCovariance timeBonds width)
  let residualRight :=
    combGaugeHeatFreeHistoryPrecisionStageResidualRightRow
      timeBonds width stage rightRow
  have hsplit := covarianceResidualBilinear_eq_linear_add_quadratic
    timeBonds width stage leftRow rightRow
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hsplit)) ?_
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_add_le
      (finiteMatrixBilinear n covarianceError leftRow rightRow)
      (finiteMatrixBilinear n covarianceError leftRow residualRight)) ?_
  exact Q'.add_le_add
    (covarianceErrorBilinear_abs_le_geometric
      timeBonds width stage leftRow rightRow)
    (quadraticCovarianceErrorBilinear_abs_le_geometric
      timeBonds width stage leftRow rightRow)

/-- The complete color-resolved action scaling kernel inherits the same
first-order plus quadratic geometric bound. -/
theorem completeOpenCubeHeatGaussianActionScalingKernel_abs_le_two_order
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q')
    (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (hrightComponent : rightComponent < 3) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let transform :=
      combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
    Q'.abs
        (finiteGaussianWeightedActionScalingKernel
          (combGaugePlaquetteNoiseCount timeBonds width)
          (completeOpenCubeHeatGaussianActionRowSquares
            timeBonds width stage)
          (heatColorPulledRow n transform leftRow leftComponent)
          (heatColorPulledRow n transform rightRow rightComponent)) ≤
      if leftComponent = rightComponent then
        combGaugeHeatFreeHistoryActionScalingFirstOrderCoefficient
            timeBonds width leftRow rightRow *
          HalfPow.half ^ stage +
        (combGaugeHeatFreeHistoryActionScalingQuadraticCoefficient
            timeBonds width leftRow rightRow *
          HalfPow.half ^ stage) *
          HalfPow.half ^ stage
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
      (combGaugeHeatFreeHistoryCovarianceResidualContractionBilinear_abs_le_two_order
        timeBonds width stage leftRow rightRow)
  · simp only [if_neg hcomponent] at hkernel ⊢
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hkernel))
      (by decide : Q'.abs (0 : Q') ≤ 0)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelTwoOrderEnvelope

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelTwoOrderEnvelope.combGaugeHeatFreeHistoryCovarianceResidualContractionBilinear_abs_le_two_order
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelTwoOrderEnvelope.completeOpenCubeHeatGaussianActionScalingKernel_abs_le_two_order
