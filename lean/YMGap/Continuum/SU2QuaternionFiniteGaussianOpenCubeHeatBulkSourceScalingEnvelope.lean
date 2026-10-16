/-
# Actual bulk-source rows in the heat action scaling envelope

The heat-normalized `A2` carrier is built from concrete bulk-source curl rows.
This leaf identifies each of those noise-coordinate rows with the Heron
pullback of its literal physical curl row and specializes the complete heat
action scaling-kernel estimate to a pair of such source rows.

The resulting first- and second-order coefficients are explicit and
independent of the Heron stage.  They may still grow with cutoff, volume,
source location, or the finite LDL data.  No uniform estimate, sign,
ORIGINAL-law comparison, continuum Hamiltonian, or mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelTwoOrderEnvelope

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelMatrix
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelTwoOrderEnvelope

local infix:50 " ≈ " => Q'.eqv

/-- Literal physical bulk-source curl row underlying one indexed color row of
the heat-normalized `A2` carrier. -/
def bulkSourcePhysicalColorCurlRow
    (side time rowIndex coordinate : Nat) : Q' :=
  combGaugeFreeHistoryCurlRow
    (bulkSourceWidth side) time
    (bulkSourceInternalFaceIndex side (rowIndex / 3)) coordinate

/-- Each heat-normalized bulk-source row is exactly the corresponding
physical curl row pulled through the heat Heron transform and embedded in its
indexed color block. -/
theorem bulkSourceHeatHeronColorCurlRow_eq_heatColorPulledRow
    (timeBonds side stage time rowIndex : Nat) :
    bulkSourceHeatHeronColorCurlRow
        timeBonds side stage time rowIndex =
      heatColorPulledRow
        (historyCoordinateCount timeBonds
          (combGaugeEdgeCount (bulkSourceWidth side)))
        (combGaugeHeatFreeHistoryHeronTransform
          timeBonds (bulkSourceWidth side) stage)
        (bulkSourcePhysicalColorCurlRow side time rowIndex)
        (rowIndex % 3) := by
  rfl

/-- Stage-independent first-order coefficient for a literal pair of indexed
bulk-source physical curl rows. -/
def bulkSourceHeatActionScalingFirstOrderCoefficient
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat) : Q' :=
  combGaugeHeatFreeHistoryActionScalingFirstOrderCoefficient
    timeBonds (bulkSourceWidth side)
    (bulkSourcePhysicalColorCurlRow side leftTime leftRowIndex)
    (bulkSourcePhysicalColorCurlRow side rightTime rightRowIndex)

/-- Stage-independent quadratic coefficient for a literal pair of indexed
bulk-source physical curl rows. -/
def bulkSourceHeatActionScalingQuadraticCoefficient
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat) : Q' :=
  combGaugeHeatFreeHistoryActionScalingQuadraticCoefficient
    timeBonds (bulkSourceWidth side)
    (bulkSourcePhysicalColorCurlRow side leftTime leftRowIndex)
    (bulkSourcePhysicalColorCurlRow side rightTime rightRowIndex)

/-- The complete heat action scaling kernel between two actual bulk-source
`A2` rows has the explicit first-order plus quadratic geometric bound. -/
theorem bulkSourceHeatActionScalingKernel_abs_le_two_order
    (timeBonds side stage leftTime rightTime leftRowIndex rightRowIndex : Nat) :
    Q'.abs
        (finiteGaussianWeightedActionScalingKernel
          (combGaugePlaquetteNoiseCount timeBonds (bulkSourceWidth side))
          (completeOpenCubeHeatGaussianActionRowSquares
            timeBonds (bulkSourceWidth side) stage)
          (bulkSourceHeatHeronColorCurlRow
            timeBonds side stage leftTime leftRowIndex)
          (bulkSourceHeatHeronColorCurlRow
            timeBonds side stage rightTime rightRowIndex)) ≤
      if leftRowIndex % 3 = rightRowIndex % 3 then
        bulkSourceHeatActionScalingFirstOrderCoefficient
            timeBonds side leftTime rightTime leftRowIndex rightRowIndex *
          HalfPow.half ^ stage +
        (bulkSourceHeatActionScalingQuadraticCoefficient
            timeBonds side leftTime rightTime leftRowIndex rightRowIndex *
          HalfPow.half ^ stage) *
          HalfPow.half ^ stage
      else 0 := by
  rw [bulkSourceHeatHeronColorCurlRow_eq_heatColorPulledRow,
    bulkSourceHeatHeronColorCurlRow_eq_heatColorPulledRow]
  exact completeOpenCubeHeatGaussianActionScalingKernel_abs_le_two_order
    timeBonds (bulkSourceWidth side) stage
    (bulkSourcePhysicalColorCurlRow side leftTime leftRowIndex)
    (bulkSourcePhysicalColorCurlRow side rightTime rightRowIndex)
    (leftRowIndex % 3) (rightRowIndex % 3)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope.bulkSourceHeatHeronColorCurlRow_eq_heatColorPulledRow
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope.bulkSourceHeatActionScalingKernel_abs_le_two_order
