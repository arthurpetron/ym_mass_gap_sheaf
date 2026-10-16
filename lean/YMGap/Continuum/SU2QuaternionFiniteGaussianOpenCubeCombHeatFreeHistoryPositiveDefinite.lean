/-
# Heat-normalized positive covariance for the finite comb FREE history

The existing comb-history covariance is the inverse of the matrix `L` whose
quadratic form is the complete spatial-curl plus temporal-difference action.
The standard product Gaussian has density proportional to `exp(-|z|^2/2)`.
Consequently the pullback appropriate to the heat density `exp(-<a,L a>)`
must factor the inverse of `2L`, not the inverse of `L`.

This leaf constructs that corrected finite covariance without changing the
generic inverse-of-`L` carrier.  It proves strict positivity of `2L`, produces
its exact rational two-sided inverse and positive LDL data, and exposes the
corresponding rational Heron transform.  A one-coordinate Wick witness records
the factor-two obstruction explicitly: under the standard Gaussian,
`Cov(z^2,z^2)=2 E[z^2]` and the third cumulant is four times the quadratic
covariance.

The file does not yet rebuild the open-cube source/action rows with the new
heat transform, compare the ORIGINAL law, prove a uniform response estimate,
or establish a continuum theory or physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
import YMGap.Continuum.SU2QuaternionFiniteGaussianThreeSquareThirdCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeSquareThirdCumulant

local infix:50 " ≈ " => Q'.eqv

/-- The heat-law precision is twice the quadratic-action matrix. -/
def combGaugeHeatFreeHistoryPrecision
    (timeBonds width : Nat) (left right : Nat) : Q' :=
  2 * combGaugeFreeHistoryPrecision timeBonds width left right

private theorem finiteMatrixQuadratic_scale
    (n : Nat) (scale : Q') (matrix : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (fun left right => scale * matrix left right) coefficient ≈
      scale * finiteMatrixQuadratic n matrix coefficient := by
  unfold finiteMatrixQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun left => scale * listQSum
        (fun right =>
          (coefficient left * coefficient right) * matrix left right)
        (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro left _hleft
    refine Q'.eqv_trans _
      (listQSum
        (fun right => scale *
          ((coefficient left * coefficient right) * matrix left right))
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro right _hright
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 3)))
        (by decide) (fun
          | 0 => coefficient left
          | 1 => coefficient right
          | 2 => scale
          | _ => matrix left right)
    · exact listQSum_mul_left scale _ (List.range n)
  · exact listQSum_mul_left scale _ (List.range n)

/-- Doubling preserves symmetry of the complete comb-history precision. -/
theorem combGaugeHeatFreeHistoryPrecision_symmetric
    (timeBonds width : Nat) :
    FiniteMatrixSymmetric
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeHeatFreeHistoryPrecision timeBonds width) := by
  intro left right hleft hright
  unfold combGaugeHeatFreeHistoryPrecision
  exact Q'.mul_eqv_congr_left 2 _ _
    (combGaugeFreeHistoryPrecision_symmetric
      timeBonds width hleft hright)

/-- The doubled heat-law precision remains strictly positive. -/
theorem combGaugeHeatFreeHistoryPrecision_strictlyPositive
    (timeBonds width : Nat) :
    FiniteMatrixStrictlyPositive
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeHeatFreeHistoryPrecision timeBonds width) := by
  intro coefficient index hindex hcoordinate
  have hbase := combGaugeFreeHistoryPrecision_strictlyPositive
    timeBonds width coefficient index hindex hcoordinate
  have hscaled :
      (0 : Q') <
        2 * finiteMatrixQuadratic
          (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
          (combGaugeFreeHistoryPrecision timeBonds width) coefficient :=
    Q'.mul_pos (by decide) hbase
  exact Q'.pos_of_lt_of_le hscaled
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteMatrixQuadratic_scale
          (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
          2 (combGaugeFreeHistoryPrecision timeBonds width) coefficient)))

/-- Exact positive LDL data for the doubled heat-law precision. -/
def combGaugeHeatFreeHistoryPositiveLDL (timeBonds width : Nat) :
    PositiveLDLData
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeHeatFreeHistoryPrecision timeBonds width) :=
  positiveLDLDataOfStrictPositive
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryPrecision timeBonds width)
    (combGaugeHeatFreeHistoryPrecision_symmetric timeBonds width)
    (combGaugeHeatFreeHistoryPrecision_strictlyPositive timeBonds width)

/-- The doubled precision factors pass the exact finite LDL checker. -/
theorem combGaugeHeatFreeHistoryPositiveLDL_check
    (timeBonds width : Nat) :
    finiteLDLCheck
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryPrecision timeBonds width)
        (combGaugeHeatFreeHistoryPositiveLDL timeBonds width).lower
        (combGaugeHeatFreeHistoryPositiveLDL timeBonds width).diagonal = true :=
  (combGaugeHeatFreeHistoryPositiveLDL
    timeBonds width).finiteLDLCheck_eq_true

/-- Canonical constructive inverse data for the doubled heat-law precision. -/
def combGaugeHeatFreeHistoryInverseData (timeBonds width : Nat) :
    FiniteMatrixInverseData
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeHeatFreeHistoryPrecision timeBonds width) :=
  finiteMatrixInverseDataOfStrictPositive
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryPrecision timeBonds width)
    (combGaugeHeatFreeHistoryPrecision_symmetric timeBonds width)
    (combGaugeHeatFreeHistoryPrecision_strictlyPositive timeBonds width)

/-- Exact rational covariance for the finite heat Gaussian. -/
def combGaugeHeatFreeHistoryCovariance
    (timeBonds width : Nat) : Nat → Nat → Q' :=
  (combGaugeHeatFreeHistoryInverseData timeBonds width).inverse

/-- The heat covariance passes the executable two-sided inverse checker. -/
theorem combGaugeHeatFreeHistoryCovariance_inverse_check
    (timeBonds width : Nat) :
    finiteMatrixInverseCheck
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryPrecision timeBonds width)
        (combGaugeHeatFreeHistoryCovariance timeBonds width) = true :=
  (combGaugeHeatFreeHistoryInverseData
    timeBonds width).finiteMatrixInverseCheck_eq_true

/-- Positive LDL data for the exact heat covariance. -/
def combGaugeHeatFreeHistoryCovariancePositiveLDL
    (timeBonds width : Nat) :
    PositiveLDLData
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeHeatFreeHistoryCovariance timeBonds width) :=
  finiteMatrixInversePositiveLDLDataOfStrictPositive
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryPrecision timeBonds width)
    (combGaugeHeatFreeHistoryPrecision_symmetric timeBonds width)
    (combGaugeHeatFreeHistoryPrecision_strictlyPositive timeBonds width)

/-- The heat covariance factors pass the exact finite LDL checker. -/
theorem combGaugeHeatFreeHistoryCovariancePositiveLDL_check
    (timeBonds width : Nat) :
    finiteLDLCheck
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryCovariance timeBonds width)
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal = true :=
  (combGaugeHeatFreeHistoryCovariancePositiveLDL
    timeBonds width).finiteLDLCheck_eq_true

/-- Every exact heat-covariance pivot passes the positive Boolean checker. -/
theorem combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
    (timeBonds width : Nat) :
    finiteLDLPositiveDiagonalCheck
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal = true := by
  unfold finiteLDLPositiveDiagonalCheck
  apply List.all_eq_true.mpr
  intro index hindex
  exact decide_eq_true
    ((combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).diagonal_pos (List.mem_range.mp hindex))

/-- Rational Heron factor targeting the heat covariance `(2L)^{-1}`. -/
def combGaugeHeatFreeHistoryHeronTransform
    (timeBonds width stage : Nat) : Nat → Nat → Q' :=
  heronLDLTransform
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).lower
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).diagonal
    stage

/-- One finite physical coordinate pulled back through the heat-normalized
Heron factor. -/
def combGaugeHeatFreeHistoryHeronCoordinate
    (timeBonds width stage physicalIndex : Nat) : RatPoly :=
  finiteGaussianLinearCoordinate
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
    physicalIndex

/-- An arbitrary finite physical row pulled back through the heat-normalized
Heron factor. -/
def combGaugeHeatFreeHistoryHeronObservable
    (timeBonds width stage : Nat) (physicalRow : Nat → Q') : RatPoly :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteGaussianLinearObservable coordinateCount coordinateCount
    (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
    physicalRow

/-- Exact covariance bilinear for the heat-normalized rational covariance. -/
def combGaugeHeatFreeHistoryCovarianceBilinear
    (timeBonds width : Nat) (leftRow rightRow : Nat → Q') : Q' :=
  finiteMatrixBilinear
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryCovariance timeBonds width)
    leftRow rightRow

/-- One placed three-color comb-curl row under the heat-normalized factor. -/
def combGaugeHeatFreeHistoryHeronColorCurlRow
    (timeBonds width stage : Nat)
    (times faceIndices : Nat → Nat) (rowIndex coordinate : Nat) : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  threeColorRows coordinateCount
    (pulledRow coordinateCount
      (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
      (combGaugeFreeHistoryCurlRow width
        (times (rowIndex / 3)) (faceIndices (rowIndex / 3))))
    (rowIndex % 3) coordinate

/-- Weighted radial curl square under the heat-normalized factor. -/
def combGaugeHeatFreeHistoryHeronWeightedCurlRadialSquare
    (timeBonds width stage familyCount : Nat)
    (weights : Nat → Q') (times faceIndices : Nat → Nat) : RatPoly :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteGaussianWeightedRadialSquare
    (coordinateCount + (coordinateCount + coordinateCount))
    (3 * familyCount)
    (fun rowIndex => weights (rowIndex / 3))
    (combGaugeHeatFreeHistoryHeronColorCurlRow
      timeBonds width stage times faceIndices)

/-- Coefficient-weighted entrywise Heron residual for two physical rows. -/
def combGaugeHeatFreeHistoryHeronBilinearResidualEnvelope
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  physicalCovarianceBilinearResidualEnvelope coordinateCount
    (ldlFactorResidualEnvelope coordinateCount
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).lower
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).diagonal
      stage)
    leftRow rightRow

/-- The finite product-Gaussian pair moment is the staged heat-factor Gram. -/
theorem combGaugeHeatFreeHistoryHeronCoordinate_pair
    (timeBonds width stage left right : Nat) :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    finiteProductGaussian coordinateCount
        (polyMul
          (combGaugeHeatFreeHistoryHeronCoordinate
            timeBonds width stage left)
          (combGaugeHeatFreeHistoryHeronCoordinate
            timeBonds width stage right)) ≈
      factorCovariance coordinateCount
        (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
        left right := by
  exact finiteProductGaussian_linearCoordinate_pair
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
    left right

/-- The exact inverse and positive covariance factors give the entrywise
Heron residual bound for the heat-normalized carrier. -/
theorem combGaugeHeatFreeHistoryCovariance_heronFactor
    {timeBonds width stage left right : Nat}
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    (finiteMatrixProduct
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeHeatFreeHistoryPrecision timeBonds width)
        (combGaugeHeatFreeHistoryCovariance timeBonds width) left right ≈
          finiteIdentityMatrix left right) ∧
      Q'.abs
          (factorCovariance
              (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
              (combGaugeHeatFreeHistoryHeronTransform
                timeBonds width stage)
              left right +
            -combGaugeHeatFreeHistoryCovariance
              timeBonds width left right) ≤
        ldlFactorResidualEnvelope
          (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
          (combGaugeHeatFreeHistoryCovariancePositiveLDL
            timeBonds width).lower
          (combGaugeHeatFreeHistoryCovariancePositiveLDL
            timeBonds width).diagonal
          stage left right := by
  constructor
  · exact (combGaugeHeatFreeHistoryInverseData
      timeBonds width).matrix_inverse hleft hright
  · exact factorCovariance_heronLDLTransform_error
      (combGaugeHeatFreeHistoryCovariancePositiveLDL_check
        timeBonds width)
      (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
        timeBonds width)
      hleft hright

/-- The coordinate pair moment inherits the certified heat-covariance Heron
error. -/
theorem combGaugeHeatFreeHistoryHeronCoordinate_pair_error
    {timeBonds width stage left right : Nat}
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    Q'.abs
        (finiteProductGaussian coordinateCount
            (polyMul
              (combGaugeHeatFreeHistoryHeronCoordinate
                timeBonds width stage left)
              (combGaugeHeatFreeHistoryHeronCoordinate
                timeBonds width stage right)) +
          -combGaugeHeatFreeHistoryCovariance
            timeBonds width left right) ≤
      ldlFactorResidualEnvelope coordinateCount
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal
        stage left right := by
  have hmoment := combGaugeHeatFreeHistoryHeronCoordinate_pair
    timeBonds width stage left right
  have herror := (combGaugeHeatFreeHistoryCovariance_heronFactor
    (timeBonds := timeBonds) (width := width) (stage := stage)
    hleft hright).2
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (ExpNeg.abs_eqv_congr
        (Q'.add_eqv_congr_right _ _ _ hmoment)))
    herror

/-- Every finite physical row pair inherits the heat-covariance Heron error. -/
theorem combGaugeHeatFreeHistoryHeronObservable_pair_error
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    Q'.abs
        (finiteProductGaussian coordinateCount
            (polyMul
              (combGaugeHeatFreeHistoryHeronObservable
                timeBonds width stage leftRow)
              (combGaugeHeatFreeHistoryHeronObservable
                timeBonds width stage rightRow)) +
          -combGaugeHeatFreeHistoryCovarianceBilinear
            timeBonds width leftRow rightRow) ≤
      combGaugeHeatFreeHistoryHeronBilinearResidualEnvelope
        timeBonds width stage leftRow rightRow := by
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  exact finiteProductGaussian_linearObservable_pair_error
    coordinateCount coordinateCount
    (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
    (combGaugeHeatFreeHistoryCovariance timeBonds width)
    (ldlFactorResidualEnvelope coordinateCount
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).lower
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds width).diagonal
      stage)
    leftRow rightRow
    (fun left right hleft hright =>
      (combGaugeHeatFreeHistoryCovariance_heronFactor
        (timeBonds := timeBonds) (width := width) (stage := stage)
        hleft hright).2)

/-- One standard Gaussian coordinate row. -/
def oneCoordinateRow (_index : Nat) : Q' := 1

/-- The standard one-coordinate Gaussian has mean square one. -/
theorem finiteProductGaussian_oneCoordinateSquare_mean :
    finiteProductGaussian 1
        (finiteGaussianRowSquare 1 oneCoordinateRow) ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_row_pair 1 oneCoordinateRow oneCoordinateRow)
    (by decide)

/-- The unhalved standard action has twice the one-point scaling response. -/
theorem finiteGaussianCovariance_oneCoordinateSquare_action :
    finiteGaussianCovariance 1
        (finiteGaussianRowSquare 1 oneCoordinateRow)
        (finiteGaussianRowSquare 1 oneCoordinateRow) ≈ 2 := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_row_square 1 oneCoordinateRow oneCoordinateRow)
    (by decide)

/-- Explicit factor-two mismatch for an unhalved standard action. -/
theorem finiteGaussianCovariance_oneCoordinateSquare_eq_two_mean :
    finiteGaussianCovariance 1
        (finiteGaussianRowSquare 1 oneCoordinateRow)
        (finiteGaussianRowSquare 1 oneCoordinateRow) ≈
      2 * finiteProductGaussian 1
        (finiteGaussianRowSquare 1 oneCoordinateRow) := by
  exact Q'.eqv_trans _ 2 _
    finiteGaussianCovariance_oneCoordinateSquare_action
    (Q'.eqv_symm
      (Q'.mul_eqv_congr_left 2 _ _
        finiteProductGaussian_oneCoordinateSquare_mean))

/-- The third cumulant with the unhalved standard action is four times the
quadratic covariance (`8 = 4 * 2`), not twice that covariance. -/
theorem finiteGaussianThirdCumulant_oneCoordinateSquare_action :
    finiteGaussianThirdCumulant 1
        (finiteGaussianRowSquare 1 oneCoordinateRow)
        (finiteGaussianRowSquare 1 oneCoordinateRow)
        (finiteGaussianRowSquare 1 oneCoordinateRow) ≈ 8 := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_three_row_squares
      1 oneCoordinateRow oneCoordinateRow oneCoordinateRow)
    (by decide)

/-- Explicit factor-four relation between the unhalved-action third cumulant
and the quadratic covariance. -/
theorem finiteGaussianThirdCumulant_oneCoordinateSquare_eq_four_covariance :
    finiteGaussianThirdCumulant 1
        (finiteGaussianRowSquare 1 oneCoordinateRow)
        (finiteGaussianRowSquare 1 oneCoordinateRow)
        (finiteGaussianRowSquare 1 oneCoordinateRow) ≈
      4 * finiteGaussianCovariance 1
        (finiteGaussianRowSquare 1 oneCoordinateRow)
        (finiteGaussianRowSquare 1 oneCoordinateRow) := by
  exact Q'.eqv_trans _ 8 _
    finiteGaussianThirdCumulant_oneCoordinateSquare_action
    (Q'.eqv_symm
      (Q'.eqv_trans _ (4 * 2) _
        (Q'.mul_eqv_congr_left 4 _ _
          finiteGaussianCovariance_oneCoordinateSquare_action)
        (by decide)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.combGaugeHeatFreeHistoryPrecision_strictlyPositive
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.combGaugeHeatFreeHistoryCovariance_inverse_check
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.combGaugeHeatFreeHistoryHeronTransform
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.combGaugeHeatFreeHistoryCovariance_heronFactor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.combGaugeHeatFreeHistoryHeronCoordinate_pair_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.combGaugeHeatFreeHistoryHeronObservable_pair_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.finiteProductGaussian_oneCoordinateSquare_mean
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.finiteGaussianCovariance_oneCoordinateSquare_action
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.finiteGaussianCovariance_oneCoordinateSquare_eq_two_mean
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.finiteGaussianThirdCumulant_oneCoordinateSquare_action
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite.finiteGaussianThirdCumulant_oneCoordinateSquare_eq_four_covariance
