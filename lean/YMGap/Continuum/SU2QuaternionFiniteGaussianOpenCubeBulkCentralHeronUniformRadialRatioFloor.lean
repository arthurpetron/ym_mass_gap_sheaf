/-
# Uniform central Heron radial-ratio floor

The central color-zero Heron row has squared norm at least `1/7`, uniformly
in the positive open-cube cutoff and Heron stage.  Combining that row floor
with the already retained source coefficient `3^(-18)` gives a single
strictly positive rational lower bound for the normalized finite Gaussian
radial ratio at the explicit central-positive stage.

This is a cutoff-uniform finite rational FREE-reference statement.  It does
not compare with the ORIGINAL interacting law, normalize the retained source
at physical scale, construct a continuum limit or Osterwalder--Schrader
theory, or prove a Hamiltonian/Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRowNormFloor
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronUniformRadialRatioFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRowNormFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCovarianceDiagonalFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge

/-- Explicit cutoff-independent lower bound retained by the normalized
central finite Gaussian radial ratio. -/
def bulkCentralHeronRadialRatioFloor : Q' :=
  2 * (bulkCoefficientFloor * combCovarianceDiagonalFloor)

theorem bulkCentralHeronRadialRatioFloor_pos :
    (0 : Q') < bulkCentralHeronRadialRatioFloor := by
  unfold bulkCentralHeronRadialRatioFloor
  exact Q'.mul_pos (by decide)
    (Q'.mul_pos (by
      unfold bulkCoefficientFloor
      decide) (by
      unfold combCovarianceDiagonalFloor
      decide))

/-- Every positive central cutoff retains the same explicit normalized
finite Gaussian radial-ratio floor at its certified positive Heron stage. -/
theorem bulkCentralHeronRadialRatioFloor_le
    (m : Nat) (hm : 0 < m) :
    bulkCentralHeronRadialRatioFloor ≤
      bulkSourceCentralPositiveHeronRadialRatio m hm := by
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
  let rowIndex := bulkSourceCentralFaceIndex m * 3
  let rowNorm :=
    finiteRowNorm2
      (coordinateCount + (coordinateCount + coordinateCount))
      (bulkSourceHeronColorCurlRow 1 (4 * m)
        (bulkSourceCentralPositiveHeronStage m) 0 rowIndex)
  have hnorm : combCovarianceDiagonalFloor ≤ rowNorm := by
    unfold rowNorm rowIndex coordinateCount
    exact
      combCovarianceDiagonalFloor_le_bulkSourceCentralHeronColorRowNorm
        m hm (bulkSourceCentralPositiveHeronStage m)
  have hweighted :
      bulkCoefficientFloor * combCovarianceDiagonalFloor ≤
        bulkCoefficientFloor * rowNorm :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hnorm (by
      unfold bulkCoefficientFloor
      decide)
  have hscaled :
      2 * (bulkCoefficientFloor * combCovarianceDiagonalFloor) ≤
        2 * (bulkCoefficientFloor * rowNorm) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hweighted (by decide)
  have hratio :=
    two_mul_bulkCoefficientFloor_mul_centralHeronRowNorm_le_ratio m hm
  unfold bulkCentralHeronRadialRatioFloor
  exact Q'.le_trans' _ _ _ hscaled (by
    unfold rowNorm rowIndex coordinateCount
    exact hratio)

#print axioms bulkCentralHeronRadialRatioFloor_pos
#print axioms bulkCentralHeronRadialRatioFloor_le

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronUniformRadialRatioFloor
