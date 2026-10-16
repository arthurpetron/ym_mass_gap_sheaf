/-
# Neighboring-time residual-free corrected P6 frontier

The intended neighboring comparison shares one source time and compares the
lags `(base, base + lag)` and `(base, base + (lag + 1))`.  In this
specialization the retained supplied-OLD-`c2` term has one further exact
cancellation.  Expanding each corrected `P4` cancels the mixed cubic product
of the three centered one-point means.  The surviving OLD term consists of
the two connected `R4` factors plus the square of the shared centered mean
times the neighboring one-point difference.

This is exact finite algebra.  It proves no sign for the reduced expression,
no `P4` positivity, no denominator nonvanishing, no ORIGINAL-law center
identification, no cutoff-uniform estimate, no continuum Hamiltonian, and no
Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6AdaptiveStage

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier

local infix:50 " ≈ " => Q'.eqv

/-- Residual-free cleared comparison for the neighboring lags
`(base, base + lag)` and `(base, base + (lag + 1))`. -/
def openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP6ResidualFreeClearedComparison
    timeBonds side sidePositive stage
    baseTime (baseTime + lag)
    baseTime (baseTime + (lag + 1)) oldCenter

/-- Non-common part of the residual-free neighboring comparison. -/
def openCubeHeatCayleyTraceP6NeighboringNonCommonClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP6NonCommonClearedComparison
    timeBonds side sidePositive stage
    baseTime (baseTime + lag)
    baseTime (baseTime + (lag + 1)) oldCenter

/-- Retained supplied-OLD-`c2` part before the shared-time cancellation. -/
def openCubeHeatCayleyTraceP6NeighboringOldQuadraticClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP6OldQuadraticClearedComparison
    timeBonds side sidePositive stage
    baseTime (baseTime + lag)
    baseTime (baseTime + (lag + 1)) oldCenter

/-- Reduced supplied-OLD-`c2` neighboring term after cancellation of the
mixed cubic product of the three centered one-point means. -/
def openCubeHeatCayleyTraceP6NeighboringOldQuadraticReducedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  let baseCentered :=
    openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage baseTime - oldCenter.c2
  let lagCentered :=
    openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + lag) - oldCenter.c2
  let nextCentered :=
    openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + (lag + 1)) - oldCenter.c2
  let firstConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + lag)
  let secondConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + (lag + 1))
  (heatActionTwoThird * oldCenter.c2) *
    ((secondConnected * (baseCentered + lagCentered) -
        firstConnected * (baseCentered + nextCentered)) +
      (baseCentered * baseCentered) * (nextCentered - lagCentered))

/-- Exact shared-time cancellation in the supplied-OLD-`c2` neighboring
frontier. -/
theorem openCubeHeatCayleyTraceP6NeighboringOldQuadraticClearedComparison_reduction
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticClearedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      openCubeHeatCayleyTraceP6NeighboringOldQuadraticReducedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  let baseCentered :=
    openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage baseTime - oldCenter.c2
  let lagCentered :=
    openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + lag) - oldCenter.c2
  let nextCentered :=
    openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + (lag + 1)) - oldCenter.c2
  let firstConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + lag)
  let secondConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + (lag + 1))
  let oldScale := heatActionTwoThird * oldCenter.c2
  unfold openCubeHeatCayleyTraceP6NeighboringOldQuadraticClearedComparison
    openCubeHeatCayleyTraceP6OldQuadraticClearedComparison
    openCubeHeatCayleyTraceP6OldQuadraticSourceSum
    openCubeHeatCayleyTraceP4
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticReducedComparison
  change
    oldScale *
        ((secondConnected + baseCentered * nextCentered) *
            (baseCentered + lagCentered) -
          (firstConnected + baseCentered * lagCentered) *
            (baseCentered + nextCentered)) ≈
      oldScale *
        ((secondConnected * (baseCentered + lagCentered) -
            firstConnected * (baseCentered + nextCentered)) +
          (baseCentered * baseCentered) *
            (nextCentered - lagCentered))
  exact poly_identity_of_normal_eq
    (.mul (.var 0)
      (.add
        (.mul (.add (.var 1) (.mul (.var 2) (.var 4)))
          (.add (.var 2) (.var 3)))
        (.neg
          (.mul (.add (.var 5) (.mul (.var 2) (.var 3)))
            (.add (.var 2) (.var 4))))))
    (.mul (.var 0)
      (.add
        (.add
          (.mul (.var 1) (.add (.var 2) (.var 3)))
          (.neg (.mul (.var 5) (.add (.var 2) (.var 4)))))
        (.mul (.mul (.var 2) (.var 2))
          (.add (.var 4) (.neg (.var 3))))))
    (by decide) (fun
      | 0 => oldScale
      | 1 => secondConnected
      | 2 => baseCentered
      | 3 => lagCentered
      | 4 => nextCentered
      | _ => firstConnected)

/-- The residual-free neighboring frontier is exactly its non-common part
plus the reduced supplied-OLD-`c2` term. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_decomposition
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      openCubeHeatCayleyTraceP6NeighboringNonCommonClearedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        openCubeHeatCayleyTraceP6NeighboringOldQuadraticReducedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter := by
  refine Q'.eqv_trans _ _ _
    (openCubeHeatCayleyTraceP6ResidualFreeClearedComparison_decomposition
      timeBonds side sidePositive stage
      baseTime (baseTime + lag)
      baseTime (baseTime + (lag + 1)) oldCenter) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _)
    (openCubeHeatCayleyTraceP6NeighboringOldQuadraticClearedComparison_reduction
      timeBonds side sidePositive stage baseTime lag oldCenter)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier.openCubeHeatCayleyTraceP6NeighboringOldQuadraticClearedComparison_reduction
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_decomposition
