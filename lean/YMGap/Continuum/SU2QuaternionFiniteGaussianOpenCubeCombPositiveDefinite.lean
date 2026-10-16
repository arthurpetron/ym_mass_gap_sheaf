/-
# Positive-definite interface for the open-cube comb spatial precision

This leaf packages the checked strict positivity of the actual comb-gauge
`D^T D` matrix in the generic finite positive-definite interface.  It supplies
the concrete consumer for the first-pivot and recursive LDL infrastructure.

This proves every in-range diagonal entry is strictly positive and applies the
constructive all-dimension Schur recursion to produce exact positive LDL data
and an exact rational inverse for the comb spatial precision at every width.
It does not yet construct the FREE-history inverse, Gaussian law, continuum
limit, or mass gap.
-/

import YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer
open YMGap.Continuum.FiniteRationalPositiveDefiniteSchur
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix

/-- The actual finite comb-gauge spatial precision is strictly positive on
every coordinate vector carrying an explicit nonzero in-range entry. -/
theorem combGaugeSpatialPrecision_strictlyPositive (width : Nat) :
    FiniteMatrixStrictlyPositive
      (combGaugeEdgeCount width) (combGaugeSpatialPrecision width) := by
  intro coordinate gaugeIndex hgauge hcoordinate
  exact combGaugeSpatialQuadratic_positive_of_coordinate_not_eqv_zero
    width coordinate hgauge hcoordinate

/-- The actual finite comb-gauge spatial precision is symmetric. -/
theorem combGaugeSpatialPrecision_symmetric (width : Nat) :
    FiniteMatrixSymmetric
      (combGaugeEdgeCount width) (combGaugeSpatialPrecision width) := by
  intro left right _hleft _hright
  exact finiteCurlPrecision_symm
    (internalOpenCubeFaceCount width) (combGaugeCurl width) left right

/-- Every in-range diagonal of the actual comb-gauge spatial precision is a
strictly positive rational pivot candidate. -/
theorem combGaugeSpatialPrecision_diagonal_positive
    (width : Nat) {gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    (0 : Q') < combGaugeSpatialPrecision width gaugeIndex gaugeIndex := by
  exact finiteMatrixStrictlyPositive_diagonal
    (combGaugeSpatialPrecision_strictlyPositive width) hgauge

/-- The first constructive Schur pullback of every nonempty comb spatial
precision. -/
def combGaugeSpatialFirstSchur
    (width reducedSize : Nat)
    (hsize : combGaugeEdgeCount width = reducedSize + 1) :
    Nat → Nat → Q' :=
  finiteSchurPullback reducedSize (combGaugeSpatialPrecision width) (by
    rw [← hsize]
    exact combGaugeSpatialPrecision_strictlyPositive width)

/-- The first Schur pullback remains strictly positive at every width and
every nonempty comb-coordinate size. -/
theorem combGaugeSpatialFirstSchur_strictlyPositive
    (width reducedSize : Nat)
    (hsize : combGaugeEdgeCount width = reducedSize + 1) :
    FiniteMatrixStrictlyPositive reducedSize
      (combGaugeSpatialFirstSchur width reducedSize hsize) := by
  unfold combGaugeSpatialFirstSchur
  exact finiteSchurPullback_strictlyPositive _

/-- The first comb spatial Schur pullback is symmetric. -/
theorem combGaugeSpatialFirstSchur_symmetric
    (width reducedSize : Nat)
    (hsize : combGaugeEdgeCount width = reducedSize + 1) :
    FiniteMatrixSymmetric reducedSize
      (combGaugeSpatialFirstSchur width reducedSize hsize) := by
  unfold combGaugeSpatialFirstSchur
  apply finiteSchurPullback_symmetric
  rw [← hsize]
  exact combGaugeSpatialPrecision_symmetric width

/-- Exact positive LDL data for the actual comb-gauge spatial precision at
every width. -/
def combGaugeSpatialPositiveLDL (width : Nat) :
    PositiveLDLData
      (combGaugeEdgeCount width) (combGaugeSpatialPrecision width) :=
  positiveLDLDataOfStrictPositive
    (combGaugeEdgeCount width) (combGaugeSpatialPrecision width)
    (combGaugeSpatialPrecision_symmetric width)
    (combGaugeSpatialPrecision_strictlyPositive width)

/-- The recursively produced comb factors pass the existing exact finite LDL
checker. -/
theorem combGaugeSpatialPositiveLDL_check (width : Nat) :
    finiteLDLCheck (combGaugeEdgeCount width)
        (combGaugeSpatialPrecision width)
        (combGaugeSpatialPositiveLDL width).lower
        (combGaugeSpatialPositiveLDL width).diagonal = true :=
  (combGaugeSpatialPositiveLDL width).finiteLDLCheck_eq_true

/-- Every recursively produced comb pivot passes the strict-positive Boolean
checker used by the rational coordinate-factor construction. -/
theorem combGaugeSpatialPositiveLDL_diagonal_check (width : Nat) :
    finiteLDLPositiveDiagonalCheck (combGaugeEdgeCount width)
        (combGaugeSpatialPositiveLDL width).diagonal = true := by
  unfold finiteLDLPositiveDiagonalCheck
  apply List.all_eq_true.mpr
  intro index hindex
  exact decide_eq_true
    ((combGaugeSpatialPositiveLDL width).diagonal_pos
      (List.mem_range.mp hindex))

/-- Exact two-sided rational inverse data for the actual comb spatial
precision at every width. -/
def combGaugeSpatialInverseData (width : Nat) :
    FiniteMatrixInverseData
      (combGaugeEdgeCount width) (combGaugeSpatialPrecision width) :=
  finiteMatrixInverseDataOfStrictPositive
    (combGaugeEdgeCount width) (combGaugeSpatialPrecision width)
    (combGaugeSpatialPrecision_symmetric width)
    (combGaugeSpatialPrecision_strictlyPositive width)

/-- Canonical exact rational covariance for the comb spatial precision. -/
def combGaugeSpatialCovariance (width : Nat) : Nat → Nat → Q' :=
  (combGaugeSpatialInverseData width).inverse

/-- The canonical comb spatial covariance passes the repository's executable
two-sided inverse checker. -/
theorem combGaugeSpatialCovariance_inverse_check (width : Nat) :
    finiteMatrixInverseCheck (combGaugeEdgeCount width)
        (combGaugeSpatialPrecision width)
        (combGaugeSpatialCovariance width) = true :=
  (combGaugeSpatialInverseData width).finiteMatrixInverseCheck_eq_true

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialPrecision_strictlyPositive
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialPrecision_symmetric
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialPrecision_diagonal_positive
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialFirstSchur_strictlyPositive
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialFirstSchur_symmetric
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialPositiveLDL
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialPositiveLDL_check
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialPositiveLDL_diagonal_check
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialInverseData
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.combGaugeSpatialCovariance_inverse_check
