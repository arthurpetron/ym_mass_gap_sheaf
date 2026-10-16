/-
# Adaptive removal of the negative-quadratic P6 scaling residual

The corrected negative-quadratic `P6` contribution splits exactly into a
residual-free retained expression and `2/3` times the complete OLD-centered
common-action scaling residual.  The preceding fixed-cutoff modulus therefore
gives one constructive stage at which the literal contribution approximates
that retained expression to any positive rational tolerance.

The retained expression is still stage-dependent and contains `P4`, both OWN
quadratic means and the supplied OLD quadratic center.  No neighboring-time
sign, ORIGINAL-law center identification, higher-remainder estimate,
continuum Hamiltonian, or Clay mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage
open YMGap.Continuum.RegularLinearGeometricModulus

local infix:50 " ≈ " => Q'.eqv

/-- The retained same-stage expression after deleting the complete corrected
common-action scaling residual from the negative-quadratic `P6` piece. -/
def openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  heatActionFourThird *
      openCubeHeatCayleyTraceP4
        timeBonds side sidePositive stage leftTime rightTime oldCenter +
    (heatActionTwoThird * oldCenter.c2) *
      ((openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2) +
        (openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c2))

/-- Exact difference from the retained expression: only `2/3` times the
complete corrected OLD-centered scaling residual remains. -/
theorem openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_sub_residualFree_eqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
          timeBonds side sidePositive stage leftTime rightTime oldCenter -
        openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue
          timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      heatActionTwoThird *
        openCubeHeatCayleyTraceP6ScalingResidual
          timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  let retained :=
    openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue
      timeBonds side sidePositive stage leftTime rightTime oldCenter
  let residual := openCubeHeatCayleyTraceP6ScalingResidual
    timeBonds side sidePositive stage leftTime rightTime oldCenter
  have hdecomposition :=
    openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_decomposition
      timeBonds side sidePositive stage leftTime rightTime oldCenter
  unfold openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue at hdecomposition
  change openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
      timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
    retained + heatActionTwoThird * residual at hdecomposition
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      hdecomposition
      (Q'.eqv_refl
        (-retained))) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.add (.var 0) (.mul (.var 1) (.var 2)))
      (.neg (.var 0)))
    (.mul (.var 1) (.var 2))
    (by decide) (fun
      | 0 => retained
      | 1 => heatActionTwoThird
      | _ => residual)

/-- Tail coefficient for deleting the scaled residual from the literal
negative-quadratic `P6` contribution. -/
def bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  heatActionTwoThird *
    bulkSourceHeatP6ScalingTotalCoefficient
      timeBonds side sidePositive leftTime rightTime oldCenter

theorem bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient_nonnegative
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) (oldCenter : CayleyTraceOldCenter) :
    (0 : Q') ≤
      bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
        timeBonds side sidePositive leftTime rightTime oldCenter := by
  unfold bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
    heatActionTwoThird
  exact Q'.mul_nonneg _ _ (by decide)
    (bulkSourceHeatP6ScalingTotalCoefficient_nonnegative
      timeBonds side sidePositive leftTime rightTime oldCenter)

/-- One constructive stage for deleting the complete scaled residual from the
literal negative-quadratic `P6` contribution at a fixed finite cutoff. -/
def bulkSourceHeatNegativeQuadraticP6AdaptiveStage
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) (oldCenter : CayleyTraceOldCenter)
    (epsilon : Q') : Nat :=
  geoOuterModulus
    (bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
      timeBonds side sidePositive leftTime rightTime oldCenter)
    epsilon

private theorem heatActionTwoThird_mul_geoTail_eqv
    (coefficient : Q') (stage : Nat) :
    heatActionTwoThird * geoTail coefficient stage ≈
      geoTail (heatActionTwoThird * coefficient) stage := by
  unfold heatActionTwoThird geoTail
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
    (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 2))
    (by decide) (fun
      | 0 => Q'.mkPos 2 3 (by decide)
      | 1 => coefficient
      | _ => HalfPow.half ^ stage)

/-- At every stage, the literal negative-quadratic `P6` contribution differs
from its retained same-stage expression by at most the scaled aggregate tail. -/
theorem openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_sub_residualFree_abs_le_geoTail
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    Q'.abs
        (openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
            timeBonds side sidePositive stage leftTime rightTime oldCenter -
          openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue
            timeBonds side sidePositive stage leftTime rightTime oldCenter) ≤
      geoTail
        (bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
          timeBonds side sidePositive leftTime rightTime oldCenter)
        stage := by
  let coefficient := bulkSourceHeatP6ScalingTotalCoefficient
    timeBonds side sidePositive leftTime rightTime oldCenter
  let residual := openCubeHeatCayleyTraceP6ScalingResidual
    timeBonds side sidePositive stage leftTime rightTime oldCenter
  have hresidual : Q'.abs residual ≤ geoTail coefficient stage :=
    openCubeHeatCayleyTraceP6ScalingResidual_abs_le_geoTail
      timeBonds side sidePositive stage leftTime rightTime oldCenter
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_sub_residualFree_eqv
          timeBonds side sidePositive stage leftTime rightTime oldCenter))) ?_
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le heatActionTwoThird residual) ?_
  rw [ExpNeg.abs_of_nonneg
    (by
      unfold heatActionTwoThird
      decide : (0 : Q') ≤ heatActionTwoThird)]
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hresidual
      (by
        unfold heatActionTwoThird
        decide)) ?_
  unfold bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
  exact Q'.le_of_eqv
    (heatActionTwoThird_mul_geoTail_eqv coefficient stage)

/-- At every later stage, deleting the complete scaled residual from the
literal negative-quadratic `P6` contribution costs at most the supplied
positive rational tolerance. -/
theorem openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_sub_residualFree_abs_le_epsilon
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatNegativeQuadraticP6AdaptiveStage
        timeBonds side sidePositive leftTime rightTime oldCenter epsilon ≤
      stage) :
    Q'.abs
        (openCubeHeatCayleyTraceNegativeQuadraticP6Contribution
            timeBonds side sidePositive stage leftTime rightTime oldCenter -
          openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue
            timeBonds side sidePositive stage leftTime rightTime oldCenter) ≤
      epsilon := by
  refine Q'.le_trans' _ _ _
    (openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_sub_residualFree_abs_le_geoTail
      timeBonds side sidePositive stage leftTime rightTime oldCenter) ?_
  exact geoTail_le_of_modulus
    (bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
      timeBonds side sidePositive leftTime rightTime oldCenter)
    (bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient_nonnegative
      timeBonds side sidePositive leftTime rightTime oldCenter)
    epsilon hepsilon stage hstage

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage.openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_sub_residualFree_eqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage.bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage.openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_sub_residualFree_abs_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage.openCubeHeatCayleyTraceNegativeQuadraticP6Contribution_sub_residualFree_abs_le_epsilon
