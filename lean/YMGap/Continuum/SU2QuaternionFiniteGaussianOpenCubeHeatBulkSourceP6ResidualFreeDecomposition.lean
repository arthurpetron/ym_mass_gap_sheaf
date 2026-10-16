/-
# Complete corrected P6 split after common-action residual removal

This file separates the literal negative-quadratic density contribution from
the complete corrected OLD-centered `P6`.  The remaining exact finite term is
named explicitly through the connected `R6`, the two fourth-OWN residuals and
the retained OLD cubic square.  Replacing only the negative-quadratic piece by
its residual-free value then approximates the complete `P6` with exactly the
same fixed-cutoff geometric tail.

This is an exact finite decomposition and a Heron-stage approximation.  No
sign of the retained expression, ORIGINAL-law center identification,
higher-remainder estimate, continuum Hamiltonian, or Clay mass gap is proved.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatConnectedR6
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage
open YMGap.Continuum.RegularLinearGeometricModulus

local infix:50 " ≈ " => Q'.eqv

private theorem subtract_remainder_eq_error
    (whole component remainder retained : Q')
    (hsplit : whole - component ≈ remainder) :
    whole - (remainder + retained) ≈ component - retained := by
  have hwhole : whole ≈ remainder + component :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.var 0)
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
        (by decide) (fun
          | 0 => whole
          | _ => component))
      (Q'.add_eqv_congr' hsplit (Q'.eqv_refl component))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hwhole
      (Q'.eqv_refl (-(remainder + retained)))) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.add (.var 0) (.var 1))
      (.neg (.add (.var 0) (.var 2))))
    (.add (.var 1) (.neg (.var 2)))
    (by decide) (fun
      | 0 => remainder
      | 1 => component
      | _ => retained)

/-- Connected corrected `R6` with the literal negative-quadratic density
cumulant removed. -/
def openCubeHeatCayleyTraceConnectedR6WithoutNegativeQuadratic
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let left := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let densityQuadratic := polySmul (-1)
    (completeOpenCubeHeatActionQuadraticPolynomial
      timeBonds (bulkSourceWidth side) stage)
  openCubeHeatCayleyTraceConnectedR6WickSum
      timeBonds side sidePositive stage leftTime rightTime -
    finiteGaussianThirdCumulant
      noiseCount left right densityQuadratic

/-- One corrected fourth OWN-minus-OLD residual with the literal
negative-quadratic density covariance removed. -/
def openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let source := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage time
  let densityQuadratic := polySmul (-1)
    (completeOpenCubeHeatActionQuadraticPolynomial
      timeBonds (bulkSourceWidth side) stage)
  (openCubeHeatCayleyTraceOwnA4Mean
      timeBonds side sidePositive stage time - oldCenter.c4) -
    finiteGaussianCovariance noiseCount source densityQuadratic

/-- Exact non-common remainder after deleting the literal
negative-quadratic contribution from parity-normalized corrected `P6`. -/
def openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let leftA2Residual := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime - oldCenter.c2
  let rightA2Residual := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime - oldCenter.c2
  let leftA4Residual :=
    openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
      timeBonds side sidePositive stage leftTime oldCenter
  let rightA4Residual :=
    openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
      timeBonds side sidePositive stage rightTime oldCenter
  ((openCubeHeatCayleyTraceConnectedR6WithoutNegativeQuadratic
        timeBonds side sidePositive stage leftTime rightTime +
      leftA2Residual * rightA4Residual) +
    (-oldCenter.c3) * (-oldCenter.c3)) +
  leftA4Residual * rightA2Residual

/-- Exact complete corrected `P6` split into the literal
negative-quadratic density contribution and its non-common remainder. -/
theorem openCubeHeatCayleyTraceP6_sub_negativeQuadratic_eqv_withoutNegativeQuadratic
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6
          timeBonds side sidePositive stage leftTime rightTime oldCenter -
        openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
          timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
        timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let left := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let densityQuadratic := polySmul (-1)
    (completeOpenCubeHeatActionQuadraticPolynomial
      timeBonds (bulkSourceWidth side) stage)
  let connected := openCubeHeatCayleyTraceConnectedR6WickSum
    timeBonds side sidePositive stage leftTime rightTime
  let connectedQuadratic := finiteGaussianThirdCumulant
    noiseCount left right densityQuadratic
  let leftA2Residual := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime - oldCenter.c2
  let rightA2Residual := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime - oldCenter.c2
  let leftA4Residual := openCubeHeatCayleyTraceOwnA4Mean
    timeBonds side sidePositive stage leftTime - oldCenter.c4
  let rightA4Residual := openCubeHeatCayleyTraceOwnA4Mean
    timeBonds side sidePositive stage rightTime - oldCenter.c4
  let leftQuadratic := finiteGaussianCovariance
    noiseCount left densityQuadratic
  let rightQuadratic := finiteGaussianCovariance
    noiseCount right densityQuadratic
  let cubicResidual := (-oldCenter.c3) * (-oldCenter.c3)
  have hp6 := openCubeHeatCayleyTraceP6_parity
    timeBonds side sidePositive stage leftTime rightTime oldCenter
  change openCubeHeatCayleyTraceP6
      timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
    ((connected + leftA2Residual * rightA4Residual) + cubicResidual) +
      leftA4Residual * rightA2Residual at hp6
  unfold openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
    openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
    openCubeHeatCayleyTraceConnectedR6WithoutNegativeQuadratic
    openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
  dsimp only
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hp6
      (Q'.eqv_refl
        (-((connectedQuadratic + leftA2Residual * rightQuadratic) +
          leftQuadratic * rightA2Residual)))) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.add
        (.add
          (.add (.var 0) (.mul (.var 2) (.var 5)))
          (.var 8))
        (.mul (.var 4) (.var 3)))
      (.neg
        (.add
          (.add (.var 1) (.mul (.var 2) (.var 7)))
          (.mul (.var 6) (.var 3)))))
    (.add
      (.add
        (.add
          (.add (.var 0) (.neg (.var 1)))
          (.mul (.var 2) (.add (.var 5) (.neg (.var 7)))))
        (.var 8))
      (.mul (.add (.var 4) (.neg (.var 6))) (.var 3)))
    (by decide) (fun
      | 0 => connected
      | 1 => connectedQuadratic
      | 2 => leftA2Residual
      | 3 => rightA2Residual
      | 4 => leftA4Residual
      | 5 => rightA4Residual
      | 6 => leftQuadratic
      | 7 => rightQuadratic
      | _ => cubicResidual)

/-- Complete corrected `P6` value after deleting only the common-action
scaling residual from its negative-quadratic component. -/
def openCubeHeatCayleyTraceP6ResidualFreeValue
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
      timeBonds side sidePositive stage leftTime rightTime oldCenter +
    openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue
      timeBonds side sidePositive stage leftTime rightTime oldCenter

/-- The complete corrected `P6` approximation error is exactly the already
controlled negative-quadratic approximation error. -/
theorem openCubeHeatCayleyTraceP6_sub_residualFree_eqv_negativeQuadratic_error
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6
          timeBonds side sidePositive stage leftTime rightTime oldCenter -
        openCubeHeatCayleyTraceP6ResidualFreeValue
          timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
          timeBonds side sidePositive stage leftTime rightTime oldCenter -
        openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue
          timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  unfold openCubeHeatCayleyTraceP6ResidualFreeValue
  exact subtract_remainder_eq_error
    (openCubeHeatCayleyTraceP6
      timeBonds side sidePositive stage leftTime rightTime oldCenter)
    (openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
      timeBonds side sidePositive stage leftTime rightTime oldCenter)
    (openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
      timeBonds side sidePositive stage leftTime rightTime oldCenter)
    (openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue
      timeBonds side sidePositive stage leftTime rightTime oldCenter)
    (openCubeHeatCayleyTraceP6_sub_negativeQuadratic_eqv_withoutNegativeQuadratic
      timeBonds side sidePositive stage leftTime rightTime oldCenter)

/-- At every stage, the complete corrected `P6` differs from its
common-action-residual-free value by the same scaled aggregate tail. -/
theorem openCubeHeatCayleyTraceP6_sub_residualFree_abs_le_geoTail
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    Q'.abs
        (openCubeHeatCayleyTraceP6
            timeBonds side sidePositive stage leftTime rightTime oldCenter -
          openCubeHeatCayleyTraceP6ResidualFreeValue
            timeBonds side sidePositive stage leftTime rightTime oldCenter) ≤
      geoTail
        (bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
          timeBonds side sidePositive leftTime rightTime oldCenter)
        stage := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceP6_sub_residualFree_eqv_negativeQuadratic_error
          timeBonds side sidePositive stage leftTime rightTime oldCenter))) ?_
  exact
    openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_sub_residualFree_abs_le_geoTail
      timeBonds side sidePositive stage leftTime rightTime oldCenter

/-- At every later stage selected by the existing negative-quadratic modulus,
the complete corrected `P6` is within the supplied tolerance of its exact
non-common remainder plus the retained common-action expression. -/
theorem openCubeHeatCayleyTraceP6_sub_residualFree_abs_le_epsilon
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatNegativeQuadraticP6AdaptiveStage
        timeBonds side sidePositive leftTime rightTime oldCenter epsilon ≤
      stage) :
    Q'.abs
        (openCubeHeatCayleyTraceP6
            timeBonds side sidePositive stage leftTime rightTime oldCenter -
          openCubeHeatCayleyTraceP6ResidualFreeValue
            timeBonds side sidePositive stage leftTime rightTime oldCenter) ≤
      epsilon := by
  refine Q'.le_trans' _ _ _
    (openCubeHeatCayleyTraceP6_sub_residualFree_abs_le_geoTail
      timeBonds side sidePositive stage leftTime rightTime oldCenter) ?_
  exact geoTail_le_of_modulus
    (bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
      timeBonds side sidePositive leftTime rightTime oldCenter)
    (bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient_nonnegative
      timeBonds side sidePositive leftTime rightTime oldCenter)
    epsilon hepsilon stage hstage

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition.openCubeHeatCayleyTraceP6_sub_negativeQuadratic_eqv_withoutNegativeQuadratic
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition.openCubeHeatCayleyTraceP6_sub_residualFree_eqv_negativeQuadratic_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition.openCubeHeatCayleyTraceP6_sub_residualFree_abs_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition.openCubeHeatCayleyTraceP6_sub_residualFree_abs_le_epsilon
