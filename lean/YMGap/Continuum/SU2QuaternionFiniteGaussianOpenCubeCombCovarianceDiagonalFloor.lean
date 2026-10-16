/-
# Uniform covariance-pivot floor for the open-cube comb history

The one-bond time-zero precision diagonal is at most seven.  Every pivot of the
constructively produced positive LDL factor is bounded by the corresponding
matrix diagonal, so the reciprocal covariance pivot is bounded below by
`1/7`, uniformly in the open-cube width and the valid chord coordinate.

Consumer: a cutoff-uniform lower bound for the central retained Heron-pulled
Gaussian row.  This is a finite rational covariance statement only.  It does
not identify the ORIGINAL interacting law, construct a continuum limit, or
prove a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPrecisionDiagonalBound

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCovarianceDiagonalFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer
open YMGap.Continuum.FiniteRationalUnitLowerInverse
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPrecisionDiagonalBound

/-- The uniform rational covariance-pivot floor. -/
def combCovarianceDiagonalFloor : Q' := Q'.mkPos 1 7 (by decide)

/-- The covariance LDL lower factor has unit diagonal because it is the
transpose of the inverse of the unit-lower precision factor. -/
theorem combGaugeFreeHistoryCovariancePositiveLDL_lower_diagonal_eq_one
    {timeBonds width index : Nat}
    (hindex : index <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).lower
      index index = 1 := by
  have hshape := positiveLDLLowerInverseData_isUnitLower
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeFreeHistoryPrecision timeBonds width)
    (combGaugeFreeHistoryPrecision_symmetric timeBonds width)
    (combGaugeFreeHistoryPrecision_strictlyPositive timeBonds width)
  change
    (positiveLDLLowerInverseData
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeFreeHistoryPrecision timeBonds width)
      (combGaugeFreeHistoryPrecision_symmetric timeBonds width)
      (combGaugeFreeHistoryPrecision_strictlyPositive timeBonds width)).inverse
        index index = 1
  exact hshape.1 hindex

/-- The covariance LDL lower factor is upper triangular: entries strictly
below its diagonal vanish. -/
theorem combGaugeFreeHistoryCovariancePositiveLDL_lower_zero_of_column_lt_row
    {timeBonds width row column : Nat}
    (hrow : row <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hcolumn : column <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hlt : column < row) :
    (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).lower
      row column = 0 := by
  have hshape := positiveLDLLowerInverseData_isUnitLower
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeFreeHistoryPrecision timeBonds width)
    (combGaugeFreeHistoryPrecision_symmetric timeBonds width)
    (combGaugeFreeHistoryPrecision_strictlyPositive timeBonds width)
  change
    (positiveLDLLowerInverseData
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeFreeHistoryPrecision timeBonds width)
      (combGaugeFreeHistoryPrecision_symmetric timeBonds width)
      (combGaugeFreeHistoryPrecision_strictlyPositive timeBonds width)).inverse
        column row = 0
  exact hshape.2 hcolumn hrow hlt

/-- Every valid time-zero chord coordinate of the one-bond covariance LDL has
reciprocal pivot at least `1/7`. -/
theorem combGaugeFreeHistoryCovariancePositiveLDL_timeZero_diagonal_floor
    {width gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    combCovarianceDiagonalFloor ≤
      (combGaugeFreeHistoryCovariancePositiveLDL 1 width).diagonal
        (historyIndex (combGaugeEdgeCount width) 0 gaugeIndex) := by
  let coordinateCount :=
    historyCoordinateCount 1 (combGaugeEdgeCount width)
  let coordinate :=
    historyIndex (combGaugeEdgeCount width) 0 gaugeIndex
  have hcoordinate : coordinate < coordinateCount := by
    unfold coordinate coordinateCount historyIndex historyCoordinateCount
      historySliceCount
    simp only [Nat.mul_zero, Nat.zero_add]
    omega
  let precisionLDL := combGaugeFreeHistoryPositiveLDL 1 width
  have hpivotPositive : (0 : Q') < precisionLDL.diagonal coordinate :=
    precisionLDL.diagonal_pos hcoordinate
  have hpivotMatrix : precisionLDL.diagonal coordinate ≤
      combGaugeFreeHistoryPrecision 1 width coordinate coordinate := by
    have hproducer :=
      positiveLDLDataOfStrictPositive_diagonal_le_matrix_diagonal
        coordinateCount
        (combGaugeFreeHistoryPrecision 1 width)
        (combGaugeFreeHistoryPrecision_symmetric 1 width)
        (combGaugeFreeHistoryPrecision_strictlyPositive 1 width)
        hcoordinate
    simpa only [precisionLDL, coordinateCount,
      combGaugeFreeHistoryPositiveLDL] using hproducer
  have hpivotSeven : precisionLDL.diagonal coordinate ≤ 7 :=
    Q'.le_trans' _ _ _ hpivotMatrix
      (combGaugeFreeHistoryPrecision_timeZero_diagonal_le_seven hgauge)
  have hfloorNonnegative : (0 : Q') ≤ combCovarianceDiagonalFloor := by
    unfold combCovarianceDiagonalFloor
    decide
  have hscaled :
      combCovarianceDiagonalFloor * precisionLDL.diagonal coordinate ≤
        combCovarianceDiagonalFloor * 7 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpivotSeven hfloorNonnegative
  have hmul :
      combCovarianceDiagonalFloor * precisionLDL.diagonal coordinate ≤ 1 :=
    Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (by
      unfold combCovarianceDiagonalFloor
      decide))
  have hquotient := Q'.le_divPos_of_mul_le
    1 (precisionLDL.diagonal coordinate) hpivotPositive hmul
  change combCovarianceDiagonalFloor ≤
    positiveDiagonalReciprocal coordinateCount precisionLDL.diagonal
      precisionLDL.diagonal_pos coordinate
  unfold positiveDiagonalReciprocal
  rw [dif_pos hcoordinate]
  unfold Q'.divPos at hquotient
  exact Q'.le_trans' _ _ _ hquotient
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

#print axioms combGaugeFreeHistoryCovariancePositiveLDL_timeZero_diagonal_floor
#print axioms combGaugeFreeHistoryCovariancePositiveLDL_lower_diagonal_eq_one
#print axioms combGaugeFreeHistoryCovariancePositiveLDL_lower_zero_of_column_lt_row

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCovarianceDiagonalFloor
