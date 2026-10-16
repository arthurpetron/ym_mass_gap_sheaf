/-
# Complete heat action scaling kernel as a covariance residual

The complete weighted heat action list has a color-diagonal Gram sandwich.
On one color block, its doubled action contribution is the bilinear form for
`C_stage * ((2L) * C_stage)`.  Subtracting the source Gram therefore gives
the heat action-scaling residual matrix, and the checked inverse identity
rewrites that matrix as the staged-covariance error contraction.

This is an exact finite reference-law identity.  It does not prove an
entrywise or uniform bound, a neighboring-time sign, ORIGINAL-law transfer,
higher-remainder control, a continuum Hamiltonian, or a mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionSandwichMatrix
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelMatrix

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteActionPullbackGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionSandwichMatrix
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem listQSum_scaled_sub_local {Index : Type}
    (scale : Q') (left right : Index → Q') : ∀ items : List Index,
    scale * listQSum left items - listQSum right items ≈
      listQSum (fun item => scale * left item - right item) items
  | [] => by
      change scale * 0 - 0 ≈ 0
      exact poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.const 0)) (.neg (.const 0)))
        (.const 0) (by decide) (fun _ => scale)
  | item :: items => by
      change scale * (left item + listQSum left items) -
          (right item + listQSum right items) ≈
        (scale * left item - right item) +
          listQSum (fun other => scale * left other - right other) items
      exact Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.add
            (.mul (.var 0) (.add (.var 1) (.var 2)))
            (.neg (.add (.var 3) (.var 4))))
          (.add
            (.add (.mul (.var 0) (.var 1)) (.neg (.var 3)))
            (.add (.mul (.var 0) (.var 2)) (.neg (.var 4))))
          (by decide) (fun
            | 0 => scale
            | 1 => left item
            | 2 => listQSum left items
            | 3 => right item
            | _ => listQSum right items))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_scaled_sub_local scale left right items))

private def finiteMatrixScale
    (scale : Q') (matrix : Nat → Nat → Q')
    (row column : Nat) : Q' :=
  scale * matrix row column

private def finiteMatrixScaleSub
    (scale : Q') (left right : Nat → Nat → Q')
    (row column : Nat) : Q' :=
  scale * left row column - right row column

private theorem finiteMatrixProduct_scale_left_local
    (n : Nat) (scale : Q')
    (left right : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixProduct n (finiteMatrixScale scale left) right)
      (finiteMatrixScale scale (finiteMatrixProduct n left right)) := by
  intro row column _hrow _hcolumn
  unfold finiteMatrixProduct finiteMatrixScale
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun middle => poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => scale
          | 1 => left row middle
          | _ => right middle column))
      (List.range n))
    (listQSum_mul_left scale
      (fun middle => left row middle * right middle column)
      (List.range n))

private theorem finiteMatrixProduct_scale_right_local
    (n : Nat) (scale : Q')
    (left right : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixProduct n left (finiteMatrixScale scale right))
      (finiteMatrixScale scale (finiteMatrixProduct n left right)) := by
  intro row column _hrow _hcolumn
  unfold finiteMatrixProduct finiteMatrixScale
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun middle => poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun
          | 0 => left row middle
          | 1 => scale
          | _ => right middle column))
      (List.range n))
    (listQSum_mul_left scale
      (fun middle => left row middle * right middle column)
      (List.range n))

private theorem finiteMatrixBilinear_scale_sub_local
    (n : Nat) (scale : Q')
    (leftMatrix rightMatrix : Nat → Nat → Q')
    (leftRow rightRow : Nat → Q') :
    scale * finiteMatrixBilinear n leftMatrix leftRow rightRow -
        finiteMatrixBilinear n rightMatrix leftRow rightRow ≈
      finiteMatrixBilinear n
        (finiteMatrixScaleSub scale leftMatrix rightMatrix)
        leftRow rightRow := by
  unfold finiteMatrixBilinear finiteMatrixScaleSub
  simp only [qListSum_map_eq_listQSum_local]
  let indices := List.range n
  refine Q'.eqv_trans _
    (listQSum (fun left =>
      scale * listQSum (fun right =>
          (leftRow left * rightRow right) * leftMatrix left right)
          indices -
        listQSum (fun right =>
          (leftRow left * rightRow right) * rightMatrix left right)
          indices) indices) _ ?_ ?_
  · exact listQSum_scaled_sub_local scale
      (fun left => listQSum (fun right =>
        (leftRow left * rightRow right) * leftMatrix left right) indices)
      (fun left => listQSum (fun right =>
        (leftRow left * rightRow right) * rightMatrix left right) indices)
      indices
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum (fun right =>
        scale * ((leftRow left * rightRow right) * leftMatrix left right) -
          ((leftRow left * rightRow right) * rightMatrix left right))
        indices) _
      (listQSum_scaled_sub_local scale
        (fun right =>
          (leftRow left * rightRow right) * leftMatrix left right)
        (fun right =>
          (leftRow left * rightRow right) * rightMatrix left right)
        indices) ?_
    apply listQSum_congr
    intro right
    exact poly_identity_of_normal_eq
      (.add
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (.neg (.mul (.mul (.var 1) (.var 2)) (.var 4))))
      (.mul (.mul (.var 1) (.var 2))
        (.add (.mul (.var 0) (.var 3)) (.neg (.var 4))))
      (by decide) (fun
        | 0 => scale
        | 1 => leftRow left
        | 2 => rightRow right
        | 3 => leftMatrix left right
        | _ => rightMatrix left right)

private theorem heatActionProduct_eq_scaledFreeActionProduct
    (timeBonds width stage : Nat) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let covariance :=
      combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
    FiniteMatrixEqv n
      (finiteMatrixProduct n covariance
        (finiteMatrixProduct n
          (combGaugeHeatFreeHistoryPrecision timeBonds width) covariance))
      (finiteMatrixScale 2
        (finiteMatrixProduct n covariance
          (finiteMatrixProduct n
            (combGaugeFreeHistoryPrecision timeBonds width) covariance))) := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let covariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let freePrecision := combGaugeFreeHistoryPrecision timeBonds width
  have inner :
      FiniteMatrixEqv n
        (finiteMatrixProduct n
          (combGaugeHeatFreeHistoryPrecision timeBonds width) covariance)
        (finiteMatrixScale 2
          (finiteMatrixProduct n freePrecision covariance)) := by
    unfold combGaugeHeatFreeHistoryPrecision
    exact finiteMatrixProduct_scale_left_local
      n 2 freePrecision covariance
  intro row column hrow hcolumn
  exact Q'.eqv_trans _ _ _
    (finiteMatrixProduct_congr
      (finiteMatrixEqv_refl n covariance) inner hrow hcolumn)
    (finiteMatrixProduct_scale_right_local n 2 covariance
      (finiteMatrixProduct n freePrecision covariance) hrow hcolumn)

private theorem actionScalingResidualMatrix_eq_scaledFreeSub
    (timeBonds width stage : Nat) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let covariance :=
      combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
    FiniteMatrixEqv n
      (combGaugeHeatFreeHistoryActionScalingResidualMatrix
        timeBonds width stage)
      (finiteMatrixScaleSub 2
        (finiteMatrixProduct n covariance
          (finiteMatrixProduct n
            (combGaugeFreeHistoryPrecision timeBonds width) covariance))
        covariance) := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let covariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  intro row column hrow hcolumn
  unfold combGaugeHeatFreeHistoryActionScalingResidualMatrix
    finiteMatrixActionScalingResidual finiteMatrixScaleSub
  exact Q'.add_eqv_congr'
    (heatActionProduct_eq_scaledFreeActionProduct
      timeBonds width stage hrow hcolumn)
    (Q'.eqv_refl _)

private theorem twiceFreeActionSandwich_sub_stage_eq_actionResidual
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let covariance :=
      combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
    2 * finiteMatrixBilinear n
          (finiteMatrixProduct n covariance
            (finiteMatrixProduct n
              (combGaugeFreeHistoryPrecision timeBonds width) covariance))
          leftRow rightRow -
        finiteMatrixBilinear n covariance leftRow rightRow ≈
      finiteMatrixBilinear n
        (combGaugeHeatFreeHistoryActionScalingResidualMatrix
          timeBonds width stage)
        leftRow rightRow := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let covariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let freeActionProduct :=
    finiteMatrixProduct n covariance
      (finiteMatrixProduct n
        (combGaugeFreeHistoryPrecision timeBonds width) covariance)
  exact Q'.eqv_trans _ _ _
    (finiteMatrixBilinear_scale_sub_local n 2
      freeActionProduct covariance leftRow rightRow)
    (Q'.eqv_symm
      (finiteMatrixBilinear_congr
        (actionScalingResidualMatrix_eq_scaledFreeSub
          timeBonds width stage)
        leftRow rightRow))

/-- The complete noise-coordinate heat action scaling kernel is color
diagonal, and its matching-color entry is the physical heat action-residual
bilinear. -/
theorem completeOpenCubeHeatGaussianActionScalingKernel_eq_matrix
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q')
    (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (hrightComponent : rightComponent < 3) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let transform :=
      combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
    finiteGaussianWeightedActionScalingKernel
        (combGaugePlaquetteNoiseCount timeBonds width)
        (completeOpenCubeHeatGaussianActionRowSquares
          timeBonds width stage)
        (heatColorPulledRow n transform leftRow leftComponent)
        (heatColorPulledRow n transform rightRow rightComponent) ≈
      if leftComponent = rightComponent then
        finiteMatrixBilinear n
          (combGaugeHeatFreeHistoryActionScalingResidualMatrix
            timeBonds width stage)
          leftRow rightRow
      else 0 := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform :=
    combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
  let leftNoise := heatColorPulledRow n transform leftRow leftComponent
  let rightNoise := heatColorPulledRow n transform rightRow rightComponent
  have actionGram :=
    completeOpenCubeHeatGaussianActionGramSum_eq_literalSandwich
      timeBonds width stage leftRow rightRow
      leftComponent rightComponent hleftComponent hrightComponent
  change finiteGaussianWeightedActionGramSum
      (combGaugePlaquetteNoiseCount timeBonds width)
      (completeOpenCubeHeatGaussianActionRowSquares timeBonds width stage)
      leftNoise rightNoise ≈
    if leftComponent = rightComponent then
      combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich
        timeBonds width stage leftRow rightRow
    else 0 at actionGram
  have sourceGram := finiteRowGram_heatColorPulledRow
    n transform leftRow rightRow leftComponent rightComponent
    hleftComponent hrightComponent
  change finiteRowGram (combGaugePlaquetteNoiseCount timeBonds width)
      leftNoise rightNoise ≈
    if leftComponent = rightComponent then
      finiteMatrixBilinear n
        (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
        leftRow rightRow
    else 0 at sourceGram
  unfold finiteGaussianWeightedActionScalingKernel
  rw [qListSum_map_eq_listQSum_local]
  change 2 * finiteGaussianWeightedActionGramSum
      (combGaugePlaquetteNoiseCount timeBonds width)
      (completeOpenCubeHeatGaussianActionRowSquares timeBonds width stage)
      leftNoise rightNoise -
      finiteRowGram (combGaugePlaquetteNoiseCount timeBonds width)
        leftNoise rightNoise ≈ _
  refine Q'.eqv_trans _
    (2 * (if leftComponent = rightComponent then
        combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich
          timeBonds width stage leftRow rightRow
      else 0) -
      (if leftComponent = rightComponent then
        finiteMatrixBilinear n
          (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
          leftRow rightRow
      else 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 2 _ _ actionGram)
      (Q'.neg_eqv_congr _ _ sourceGram)
  · by_cases hcomponent : leftComponent = rightComponent
    · simp only [if_pos hcomponent]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left 2 _ _
            (combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich_eq_matrix
              timeBonds width stage leftRow rightRow))
          (Q'.eqv_refl _))
        (twiceFreeActionSandwich_sub_stage_eq_actionResidual
          timeBonds width stage leftRow rightRow)
    · simp only [if_neg hcomponent]
      exact poly_identity_of_normal_eq
        (.add (.mul (.const 2) (.const 0)) (.neg (.const 0)))
        (.const 0) (by decide) (fun _ => (0 : Q'))

/-- The same complete heat scaling kernel is exactly the finite contraction
with the staged covariance error. -/
theorem completeOpenCubeHeatGaussianActionScalingKernel_eq_covarianceResidual
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q')
    (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (hrightComponent : rightComponent < 3) :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let transform :=
      combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
    finiteGaussianWeightedActionScalingKernel
        (combGaugePlaquetteNoiseCount timeBonds width)
        (completeOpenCubeHeatGaussianActionRowSquares
          timeBonds width stage)
        (heatColorPulledRow n transform leftRow leftComponent)
        (heatColorPulledRow n transform rightRow rightComponent) ≈
      if leftComponent = rightComponent then
        finiteMatrixBilinear n
          (combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
            timeBonds width stage)
          leftRow rightRow
      else 0 := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform :=
    combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
  refine Q'.eqv_trans _ _ _
    (completeOpenCubeHeatGaussianActionScalingKernel_eq_matrix
      timeBonds width stage leftRow rightRow
      leftComponent rightComponent hleftComponent hrightComponent) ?_
  by_cases hcomponent : leftComponent = rightComponent
  · simp only [if_pos hcomponent]
    exact combGaugeHeatFreeHistoryActionScalingResidualBilinear_eq_covarianceResidual
      timeBonds width stage leftRow rightRow
  · simp only [if_neg hcomponent]
    exact Q'.eqv_refl _

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelMatrix

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelMatrix.completeOpenCubeHeatGaussianActionScalingKernel_eq_matrix
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelMatrix.completeOpenCubeHeatGaussianActionScalingKernel_eq_covarianceResidual
