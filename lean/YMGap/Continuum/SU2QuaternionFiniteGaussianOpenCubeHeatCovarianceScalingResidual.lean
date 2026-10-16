/-
# Exact heat covariance scaling-residual identity

Let `C_stage` be a finite staged covariance, `P` an exact precision, and `C`
an exact left inverse of `P`.  The quadratic-action scaling residual is

  C_stage * P * C_stage - C_stage.

Finite distributivity and `C * P = I` rewrite it exactly as

  (C_stage - C) * P * C_stage.

Thus the sole matrix obstruction is the staged covariance error `C_stage-C`.
The heat specialization uses the rational Heron factor covariance and the
checked inverse of the doubled open-cube precision.  This file proves no
entrywise or uniform bound, no ORIGINAL-law comparison, no continuum limit,
and no mass gap.
-/

import YMGap.Continuum.FiniteRationalMatrixAlgebra
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite

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

/-- Literal entrywise difference of two finite matrices. -/
def finiteMatrixSub
    (left right : Nat → Nat → Q') (row column : Nat) : Q' :=
  left row column - right row column

/-- Matrix encoding the failure of a staged covariance to obey exact
quadratic-action scaling. -/
def finiteMatrixActionScalingResidual
    (n : Nat) (stageCovariance precision : Nat → Nat → Q')
    (row column : Nat) : Q' :=
  finiteMatrixProduct n stageCovariance
      (finiteMatrixProduct n precision stageCovariance) row column -
    stageCovariance row column

/-- Matrix contraction with the staged covariance error. -/
def finiteMatrixCovarianceResidualContraction
    (n : Nat)
    (stageCovariance exactCovariance precision : Nat → Nat → Q')
    (row column : Nat) : Q' :=
  finiteMatrixProduct n
    (finiteMatrixSub stageCovariance exactCovariance)
    (finiteMatrixProduct n precision stageCovariance) row column

private theorem finiteMatrixProduct_sub_left_entry
    (n : Nat) (left right matrix : Nat → Nat → Q')
    (row column : Nat) :
    finiteMatrixProduct n (finiteMatrixSub left right) matrix row column ≈
      finiteMatrixProduct n left matrix row column -
        finiteMatrixProduct n right matrix row column := by
  unfold finiteMatrixProduct finiteMatrixSub
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun index =>
        poly_identity_of_normal_eq
          (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
          (.add (.mul (.var 0) (.var 2))
            (.neg (.mul (.var 1) (.var 2))))
          (by decide) (fun
            | 0 => left row index
            | 1 => right row index
            | _ => matrix index column))
      (List.range n))
    (listQSum_sub_local
      (fun index => left row index * matrix index column)
      (fun index => right row index * matrix index column)
      (List.range n))

/-- Exact finite matrix identity: the action-scaling defect is linear in the
staged covariance error, with the remaining factor `P*C_stage`. -/
theorem finiteMatrixActionScalingResidual_eq_covarianceResidualContraction
    (n : Nat)
    (stageCovariance exactCovariance precision : Nat → Nat → Q')
    (exactLeftInverse : FiniteMatrixEqv n
      (finiteMatrixProduct n exactCovariance precision)
      finiteIdentityMatrix) :
    FiniteMatrixEqv n
      (finiteMatrixActionScalingResidual n stageCovariance precision)
      (finiteMatrixCovarianceResidualContraction
        n stageCovariance exactCovariance precision) := by
  intro row column hrow hcolumn
  let precisionStage := finiteMatrixProduct n precision stageCovariance
  have exactTimesPrecisionStage :
      finiteMatrixProduct n exactCovariance precisionStage row column ≈
        stageCovariance row column := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (finiteMatrixProduct_assoc n exactCovariance precision
          stageCovariance hrow hcolumn))
      (Q'.eqv_trans _ _ _
        (finiteMatrixProduct_congr exactLeftInverse
          (finiteMatrixEqv_refl n stageCovariance) hrow hcolumn)
        (finiteIdentityMatrix_mul n stageCovariance hrow hcolumn))
  have contractionToScaling :
      finiteMatrixCovarianceResidualContraction
          n stageCovariance exactCovariance precision row column ≈
        finiteMatrixActionScalingResidual
          n stageCovariance precision row column := by
    unfold finiteMatrixCovarianceResidualContraction
      finiteMatrixActionScalingResidual
    exact Q'.eqv_trans _ _ _
      (finiteMatrixProduct_sub_left_entry n
        stageCovariance exactCovariance precisionStage row column)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ exactTimesPrecisionStage))
  exact Q'.eqv_symm contractionToScaling

/-- Finite physical bilinear forms respect an in-range matrix equivalence. -/
theorem finiteMatrixBilinear_congr
    {n : Nat} {leftMatrix rightMatrix : Nat → Nat → Q'}
    (matrixEqv : FiniteMatrixEqv n leftMatrix rightMatrix)
    (leftRow rightRow : Nat → Q') :
    finiteMatrixBilinear n leftMatrix leftRow rightRow ≈
      finiteMatrixBilinear n rightMatrix leftRow rightRow := by
  unfold finiteMatrixBilinear
  apply qListSum_congr_local
  intro left hleft
  apply qListSum_congr_local
  intro right hright
  exact Q'.mul_eqv_congr_left _ _ _
    (matrixEqv (List.mem_range.mp hleft) (List.mem_range.mp hright))

/-- Covariance matrix induced by the finite heat Heron transform. -/
def combGaugeHeatFreeHistoryStageCovariance
    (timeBonds width stage : Nat) (left right : Nat) : Q' :=
  factorCovariance
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
    left right

/-- Heat action-scaling residual matrix at one rational Heron stage. -/
def combGaugeHeatFreeHistoryActionScalingResidualMatrix
    (timeBonds width stage : Nat) : Nat → Nat → Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteMatrixActionScalingResidual coordinateCount
    (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
    (combGaugeHeatFreeHistoryPrecision timeBonds width)

/-- Heat covariance-error contraction matrix at one rational Heron stage. -/
def combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
    (timeBonds width stage : Nat) : Nat → Nat → Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteMatrixCovarianceResidualContraction coordinateCount
    (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
    (combGaugeHeatFreeHistoryCovariance timeBonds width)
    (combGaugeHeatFreeHistoryPrecision timeBonds width)

/-- The staged heat action-scaling matrix is exactly the checked heat
covariance-error contraction. -/
theorem combGaugeHeatFreeHistoryActionScalingResidualMatrix_eq_covarianceResidual
    (timeBonds width stage : Nat) :
    FiniteMatrixEqv
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeHeatFreeHistoryActionScalingResidualMatrix
        timeBonds width stage)
      (combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
        timeBonds width stage) := by
  unfold combGaugeHeatFreeHistoryActionScalingResidualMatrix
    combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
  exact finiteMatrixActionScalingResidual_eq_covarianceResidualContraction
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
    (combGaugeHeatFreeHistoryCovariance timeBonds width)
    (combGaugeHeatFreeHistoryPrecision timeBonds width)
    (combGaugeHeatFreeHistoryInverseData timeBonds width).inverse_matrix

/-- Every pair of finite physical rows inherits the exact heat covariance
scaling-residual rewrite. -/
theorem combGaugeHeatFreeHistoryActionScalingResidualBilinear_eq_covarianceResidual
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    finiteMatrixBilinear
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryActionScalingResidualMatrix
          timeBonds width stage)
        leftRow rightRow ≈
      finiteMatrixBilinear
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryCovarianceResidualContractionMatrix
          timeBonds width stage)
        leftRow rightRow := by
  exact finiteMatrixBilinear_congr
    (combGaugeHeatFreeHistoryActionScalingResidualMatrix_eq_covarianceResidual
      timeBonds width stage)
    leftRow rightRow

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual.finiteMatrixActionScalingResidual_eq_covarianceResidualContraction
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual.combGaugeHeatFreeHistoryActionScalingResidualMatrix_eq_covarianceResidual
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual.combGaugeHeatFreeHistoryActionScalingResidualBilinear_eq_covarianceResidual
