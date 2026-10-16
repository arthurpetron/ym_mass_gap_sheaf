/-
# Denominator-cleared corrected P6 neighboring-response frontier

For two response slots, the signed `P6/P4` difference has numerator

  P4(second) * P6(first) - P4(first) * P6(second).

This file inserts the complete common-action-residual-free `P6`
decomposition.  The universal `(4/3)P4` term cancels exactly.  The remaining
frontier is the cleared difference of the named non-common remainders plus
the retained supplied-OLD-`c2` expression.  The actual-minus-residual-free
cleared error is also identified exactly.

No denominator positivity, neighboring-time sign, ORIGINAL-law center
identification, higher-remainder estimate, continuum Hamiltonian, or Clay
mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition

local infix:50 " ≈ " => Q'.eqv

/-- The OLD-quadratic source sum retained after common-action scaling removal
in one response slot. -/
def openCubeHeatCayleyTraceP6OldQuadraticSourceSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  (openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage leftTime - oldCenter.c2) +
    (openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage rightTime - oldCenter.c2)

/-- Actual denominator-cleared signed `P6/P4` numerator between two response
slots.  `first` and `second` each consist of a pair of history times. -/
def openCubeHeatCayleyTraceP6ClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter *
    openCubeHeatCayleyTraceP6
      timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter -
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter *
    openCubeHeatCayleyTraceP6
      timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter

/-- The same cleared numerator after deleting only the complete
common-action scaling residual from each corrected `P6`. -/
def openCubeHeatCayleyTraceP6ResidualFreeClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter *
    openCubeHeatCayleyTraceP6ResidualFreeValue
      timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter -
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter *
    openCubeHeatCayleyTraceP6ResidualFreeValue
      timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter

/-- Cleared signed difference carried by the two exact non-common corrected
`P6` remainders. -/
def openCubeHeatCayleyTraceP6NonCommonClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter *
    openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
      timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter -
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter *
    openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
      timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter

/-- Cleared supplied-OLD-`c2` term retained after the universal common-action
piece cancels. -/
def openCubeHeatCayleyTraceP6OldQuadraticClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  (heatActionTwoThird * oldCenter.c2) *
    (openCubeHeatCayleyTraceP4
        timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter *
      openCubeHeatCayleyTraceP6OldQuadraticSourceSum
        timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter -
    openCubeHeatCayleyTraceP4
        timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter *
      openCubeHeatCayleyTraceP6OldQuadraticSourceSum
        timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter)

/-- Exact signed frontier after common-action scaling removal.  The universal
`(4/3)P4` contribution cancels from the denominator-cleared comparison. -/
theorem openCubeHeatCayleyTraceP6ResidualFreeClearedComparison_decomposition
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6ResidualFreeClearedComparison
        timeBonds side sidePositive stage
        firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter ≈
      openCubeHeatCayleyTraceP6NonCommonClearedComparison
          timeBonds side sidePositive stage
          firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter +
        openCubeHeatCayleyTraceP6OldQuadraticClearedComparison
          timeBonds side sidePositive stage
          firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter := by
  let firstP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
  let secondP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter
  let firstRemainder := openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
    timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
  let secondRemainder := openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
    timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter
  let firstSourceSum := openCubeHeatCayleyTraceP6OldQuadraticSourceSum
    timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
  let secondSourceSum := openCubeHeatCayleyTraceP6OldQuadraticSourceSum
    timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter
  let oldScale := heatActionTwoThird * oldCenter.c2
  unfold openCubeHeatCayleyTraceP6ResidualFreeClearedComparison
    openCubeHeatCayleyTraceP6ResidualFreeValue
    openCubeHeatCayleyTraceNegativeQuadraticP6ResidualFreeValue
    openCubeHeatCayleyTraceP6NonCommonClearedComparison
    openCubeHeatCayleyTraceP6OldQuadraticClearedComparison
    openCubeHeatCayleyTraceP6OldQuadraticSourceSum
  change
    secondP4 *
          (firstRemainder +
            (heatActionFourThird * firstP4 + oldScale * firstSourceSum)) -
        firstP4 *
          (secondRemainder +
            (heatActionFourThird * secondP4 + oldScale * secondSourceSum)) ≈
      (secondP4 * firstRemainder - firstP4 * secondRemainder) +
        oldScale *
          (secondP4 * firstSourceSum - firstP4 * secondSourceSum)
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.var 1)
        (.add (.var 2)
          (.add (.mul (.var 6) (.var 0)) (.mul (.var 7) (.var 4)))))
      (.neg
        (.mul (.var 0)
          (.add (.var 3)
            (.add (.mul (.var 6) (.var 1)) (.mul (.var 7) (.var 5)))))))
    (.add
      (.add (.mul (.var 1) (.var 2))
        (.neg (.mul (.var 0) (.var 3))))
      (.mul (.var 7)
        (.add (.mul (.var 1) (.var 4))
          (.neg (.mul (.var 0) (.var 5))))))
    (by decide) (fun
      | 0 => firstP4
      | 1 => secondP4
      | 2 => firstRemainder
      | 3 => secondRemainder
      | 4 => firstSourceSum
      | 5 => secondSourceSum
      | 6 => heatActionFourThird
      | _ => oldScale)

/-- The actual-minus-residual-free cleared comparison is exactly the two
`P4`-weighted complete `P6` approximation errors. -/
theorem openCubeHeatCayleyTraceP6ClearedComparison_sub_residualFree_eqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6ClearedComparison
          timeBonds side sidePositive stage
          firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter -
        openCubeHeatCayleyTraceP6ResidualFreeClearedComparison
          timeBonds side sidePositive stage
          firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter ≈
      openCubeHeatCayleyTraceP4
          timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter *
        (openCubeHeatCayleyTraceP6
            timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter -
          openCubeHeatCayleyTraceP6ResidualFreeValue
            timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter) -
      openCubeHeatCayleyTraceP4
          timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter *
        (openCubeHeatCayleyTraceP6
            timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter -
          openCubeHeatCayleyTraceP6ResidualFreeValue
            timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter) := by
  unfold openCubeHeatCayleyTraceP6ClearedComparison
    openCubeHeatCayleyTraceP6ResidualFreeClearedComparison
  exact poly_identity_of_normal_eq
    (.add
      (.add (.mul (.var 1) (.var 2))
        (.neg (.mul (.var 0) (.var 3))))
      (.neg
        (.add (.mul (.var 1) (.var 4))
          (.neg (.mul (.var 0) (.var 5))))))
    (.add
      (.mul (.var 1) (.add (.var 2) (.neg (.var 4))))
      (.neg
        (.mul (.var 0) (.add (.var 3) (.neg (.var 5))))))
    (by decide) (fun
      | 0 => openCubeHeatCayleyTraceP4
          timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
      | 1 => openCubeHeatCayleyTraceP4
          timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter
      | 2 => openCubeHeatCayleyTraceP6
          timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
      | 3 => openCubeHeatCayleyTraceP6
          timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter
      | 4 => openCubeHeatCayleyTraceP6ResidualFreeValue
          timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
      | _ => openCubeHeatCayleyTraceP6ResidualFreeValue
          timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier.openCubeHeatCayleyTraceP6ResidualFreeClearedComparison_decomposition
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier.openCubeHeatCayleyTraceP6ClearedComparison_sub_residualFree_eqv
