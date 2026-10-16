/-
# Geometric factor in the complete heat action scaling-kernel envelope

The finite Heron residual envelope factors entrywise as a stage-independent
LDL coefficient times `2^-stage`.  This leaf extracts that same factor from
the complete action scaling-kernel envelope.  Its coefficient still contains
the stage-dependent transformed right row `((2L) * C_stage) * v`; controlling
that coefficient uniformly is a separate obligation.

No cutoff- or volume-uniform estimate, neighboring-time sign, ORIGINAL-law
comparison, higher-remainder control, continuum Hamiltonian, or mass gap is
proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelGeometricEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
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
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope

local infix:50 " ≈ " => Q'.eqv

/-- Coefficient left after extracting the explicit Heron factor `2^-stage`
from the complete heat action scaling-kernel envelope. -/
def combGaugeHeatFreeHistoryActionScalingKernelResidualCoefficient
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') : Q' :=
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let data := combGaugeHeatFreeHistoryCovariancePositiveLDL timeBonds width
  physicalCovarianceBilinearResidualEnvelope n
    (ldlFactorResidualCoefficient n data.lower data.diagonal)
    leftRow
    (combGaugeHeatFreeHistoryPrecisionStageRightRow
      timeBonds width stage rightRow)

/-- The literal finite kernel envelope has an exact geometric Heron factor.
The remaining coefficient is still stage-dependent through the transformed
right row. -/
theorem combGaugeHeatFreeHistoryActionScalingKernelEnvelope_eq_geometric
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    combGaugeHeatFreeHistoryHeronBilinearResidualEnvelope
        timeBonds width stage leftRow
        (combGaugeHeatFreeHistoryPrecisionStageRightRow
          timeBonds width stage rightRow) ≈
      combGaugeHeatFreeHistoryActionScalingKernelResidualCoefficient
          timeBonds width stage leftRow rightRow *
        HalfPow.half ^ stage := by
  unfold combGaugeHeatFreeHistoryHeronBilinearResidualEnvelope
    combGaugeHeatFreeHistoryActionScalingKernelResidualCoefficient
  exact physicalResidualEnvelope_eq_coefficient_mul_half
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width)) stage
    (ldlFactorResidualEnvelope
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).lower
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).diagonal
      stage)
    (ldlFactorResidualCoefficient
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).lower
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).diagonal)
    leftRow
    (combGaugeHeatFreeHistoryPrecisionStageRightRow
      timeBonds width stage rightRow)
    (fun left right =>
      ldlFactorResidualEnvelope_eq_coefficient_mul_half
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal
        stage left right)

/-- The complete color-resolved heat action scaling kernel is bounded by its
explicit coefficient times `2^-stage`. -/
theorem completeOpenCubeHeatGaussianActionScalingKernel_abs_le_geometric
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
        combGaugeHeatFreeHistoryActionScalingKernelResidualCoefficient
            timeBonds width stage leftRow rightRow *
          HalfPow.half ^ stage
      else 0 := by
  dsimp only
  have hbound := completeOpenCubeHeatGaussianActionScalingKernel_abs_le
    timeBonds width stage leftRow rightRow
    leftComponent rightComponent hleftComponent hrightComponent
  by_cases hcomponent : leftComponent = rightComponent
  · simp only [if_pos hcomponent] at hbound ⊢
    exact Q'.le_trans' _ _ _ hbound
      (Q'.le_of_eqv
        (combGaugeHeatFreeHistoryActionScalingKernelEnvelope_eq_geometric
          timeBonds width stage leftRow rightRow))
  · simpa only [if_neg hcomponent] using hbound

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelGeometricEnvelope

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelGeometricEnvelope.combGaugeHeatFreeHistoryActionScalingKernelEnvelope_eq_geometric
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelGeometricEnvelope.completeOpenCubeHeatGaussianActionScalingKernel_abs_le_geometric
