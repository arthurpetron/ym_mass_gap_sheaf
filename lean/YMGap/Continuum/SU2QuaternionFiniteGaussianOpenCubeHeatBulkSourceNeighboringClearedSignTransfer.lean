/-
# Sign transfer for the actual neighboring cleared P6/P4 numerator

The actual cleared neighboring numerator is within an explicit tolerance of
the residual-free frontier after the aggregate Heron stage.  Therefore a
strict residual-free margin that exceeds this tolerance transfers directly to
the actual numerator.  This file states that exact consumer.

The required residual-free signed margin is not proved here.  Nor are
corrected `P4` positivity, denominator nonvanishing, a ratio inequality,
ORIGINAL-law matching, higher-remainder control, a continuum Hamiltonian, or
the Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringClearedSignTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6AdaptiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier

local infix:50 " ≈ " => Q'.eqv

private theorem value_le_reference_add_error
    (value reference error : Q')
    (herror : Q'.abs (value - reference) ≤ error) :
    value ≤ reference + error := by
  have hdifference : value - reference ≤ error :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self (value - reference)) herror
  have hadd := Q'.add_le_add
    (Q'.le_refl' reference) hdifference
  have hrewrite : value ≈ reference + (value - reference) :=
    poly_identity_of_normal_eq
      (.var 0)
      (.add (.var 1)
        (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun
        | 0 => value
        | _ => reference)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite) hadd

/-- Actual cleared numerator for neighboring lags `(base,base+lag)` and
`(base,base+(lag+1))`. -/
def openCubeHeatCayleyTraceP6NeighboringClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP6ClearedComparison
    timeBonds side sidePositive stage
    baseTime (baseTime + lag)
    baseTime (baseTime + (lag + 1)) oldCenter

/-- Aggregate adaptive stage specialized to the intended neighboring-time
comparison. -/
def bulkSourceHeatP6NeighboringClearedAdaptiveStage
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (epsilon : Q') : Nat :=
  bulkSourceHeatP6ClearedAdaptiveStage
    timeBonds side sidePositive
    baseTime (baseTime + lag)
    baseTime (baseTime + (lag + 1)) oldCenter epsilon

/-- A strict residual-free margin larger than the chosen Heron tolerance
forces the actual neighboring cleared numerator to be strictly negative. -/
theorem openCubeHeatCayleyTraceP6NeighboringClearedComparison_lt_zero_of_residualFree_margin
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatP6NeighboringClearedAdaptiveStage
        timeBonds side sidePositive baseTime lag oldCenter epsilon ≤ stage)
    (hmargin :
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        epsilon < 0) :
    openCubeHeatCayleyTraceP6NeighboringClearedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter < 0 := by
  have herror :
      Q'.abs
          (openCubeHeatCayleyTraceP6NeighboringClearedComparison
              timeBonds side sidePositive stage baseTime lag oldCenter -
            openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
              timeBonds side sidePositive stage baseTime lag oldCenter) ≤
        epsilon := by
    exact
      openCubeHeatCayleyTraceP6ClearedComparison_sub_residualFree_abs_le_epsilon
        timeBonds side sidePositive stage
        baseTime (baseTime + lag)
        baseTime (baseTime + (lag + 1)) oldCenter
        epsilon hepsilon hstage
  have hupper := value_le_reference_add_error
    (openCubeHeatCayleyTraceP6NeighboringClearedComparison
      timeBonds side sidePositive stage baseTime lag oldCenter)
    (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter)
    epsilon herror
  exact Q'.lt_of_le_of_lt hupper hmargin

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringClearedSignTransfer

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringClearedSignTransfer.openCubeHeatCayleyTraceP6NeighboringClearedComparison_lt_zero_of_residualFree_margin
