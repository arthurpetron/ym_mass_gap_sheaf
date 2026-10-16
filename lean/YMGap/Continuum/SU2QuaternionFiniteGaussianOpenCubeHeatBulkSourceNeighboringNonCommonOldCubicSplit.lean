/-
# OLD cubic-square split in the neighboring non-common P6 frontier

The non-common corrected `P6` remainder retains the response-independent OLD
cubic square `(-c3)^2`.  In the shared-left-time neighboring cleared
comparison this constant multiplies the difference of the two corrected
`P4` values.  Expanding those `P4` values reduces that difference to the
connected `R4` difference plus the shared centered mean times the neighboring
centered-mean increment.

This exact finite split proves no sign for either time-dependent factor, no
`P4` positivity, no denominator nonvanishing, no ORIGINAL-law center
identification, no cutoff-uniform estimate, no continuum Hamiltonian, and no
Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier

local infix:50 " ≈ " => Q'.eqv

private theorem cleared_common_remainder_split
    (firstP4 secondP4 firstFull secondFull firstRemainder secondRemainder
      common : Q')
    (hfirst : firstFull ≈ firstRemainder + common)
    (hsecond : secondFull ≈ secondRemainder + common) :
    secondP4 * firstFull - firstP4 * secondFull ≈
      (secondP4 * firstRemainder - firstP4 * secondRemainder) +
        common * (secondP4 - firstP4) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left secondP4 _ _ hfirst)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left firstP4 _ _ hsecond))) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.var 1) (.add (.var 2) (.var 4)))
      (.neg (.mul (.var 0) (.add (.var 3) (.var 4)))))
    (.add
      (.add (.mul (.var 1) (.var 2))
        (.neg (.mul (.var 0) (.var 3))))
      (.mul (.var 4)
        (.add (.var 1) (.neg (.var 0)))))
    (by decide) (fun
      | 0 => firstP4
      | 1 => secondP4
      | 2 => firstRemainder
      | 3 => secondRemainder
      | _ => common)

private theorem neighboringP4_difference_reduction
    (firstP4 secondP4 firstConnected secondConnected
      baseCentered lagCentered nextCentered : Q')
    (hfirst : firstP4 ≈ firstConnected + baseCentered * lagCentered)
    (hsecond : secondP4 ≈ secondConnected + baseCentered * nextCentered) :
    secondP4 - firstP4 ≈
      (secondConnected - firstConnected) +
        baseCentered * (nextCentered - lagCentered) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hsecond (Q'.neg_eqv_congr _ _ hfirst)) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.add (.var 1) (.mul (.var 2) (.var 4)))
      (.neg (.add (.var 0) (.mul (.var 2) (.var 3)))))
    (.add
      (.add (.var 1) (.neg (.var 0)))
      (.mul (.var 2) (.add (.var 4) (.neg (.var 3)))))
    (by decide) (fun
      | 0 => firstConnected
      | 1 => secondConnected
      | 2 => baseCentered
      | 3 => lagCentered
      | _ => nextCentered)

/-- Non-common corrected `P6` remainder after deleting both the literal
negative-quadratic component and the response-independent OLD cubic square. -/
def openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
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
  (openCubeHeatCayleyTraceConnectedR6WithoutNegativeQuadratic
      timeBonds side sidePositive stage leftTime rightTime +
    leftA2Residual * rightA4Residual) +
  leftA4Residual * rightA2Residual

theorem openCubeHeatCayleyTraceP6WithoutNegativeQuadratic_split_oldCubicSquare
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
          timeBonds side sidePositive stage leftTime rightTime oldCenter +
        (-oldCenter.c3) * (-oldCenter.c3) := by
  unfold openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
  dsimp only
  exact poly_identity_of_normal_eq
    (.add
      (.add
        (.add (.var 0) (.mul (.var 1) (.var 2)))
        (.var 5))
      (.mul (.var 3) (.var 4)))
    (.add
      (.add
        (.add (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 3) (.var 4)))
      (.var 5))
    (by decide) (fun
      | 0 => openCubeHeatCayleyTraceConnectedR6WithoutNegativeQuadratic
          timeBonds side sidePositive stage leftTime rightTime
      | 1 => openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2
      | 2 => openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
          timeBonds side sidePositive stage rightTime oldCenter
      | 3 => openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
          timeBonds side sidePositive stage leftTime oldCenter
      | 4 => openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c2
      | _ => (-oldCenter.c3) * (-oldCenter.c3))

theorem oldCubicSquare_nonnegative (oldCenter : CayleyTraceOldCenter) :
    (0 : Q') ≤ (-oldCenter.c3) * (-oldCenter.c3) :=
  SumOfSquares.q_mul_self_nonneg (-oldCenter.c3)

/-- Neighboring cleared comparison after deleting the constant OLD cubic
square from both non-common `P6` response slots. -/
def openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter *
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter -
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter *
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter

/-- Reduced neighboring contribution of the response-independent OLD cubic
square. -/
def openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
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
  ((-oldCenter.c3) * (-oldCenter.c3)) *
    ((secondConnected - firstConnected) +
      baseCentered * (nextCentered - lagCentered))

/-- Exact split of the neighboring non-common frontier into its
time-dependent no-OLD-cubic-square part and the reduced constant OLD cubic
residue. -/
theorem openCubeHeatCayleyTraceP6NeighboringNonCommonClearedComparison_split_oldCubic
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringNonCommonClearedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
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
  let firstP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage
    baseTime (baseTime + lag) oldCenter
  let secondP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage
    baseTime (baseTime + (lag + 1)) oldCenter
  let firstFull := openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
    timeBonds side sidePositive stage
    baseTime (baseTime + lag) oldCenter
  let secondFull := openCubeHeatCayleyTraceP6WithoutNegativeQuadratic
    timeBonds side sidePositive stage
    baseTime (baseTime + (lag + 1)) oldCenter
  let firstRemainder :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter
  let secondRemainder :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter
  let cubicSquare := (-oldCenter.c3) * (-oldCenter.c3)
  have hfirstSplit : firstFull ≈ firstRemainder + cubicSquare :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadratic_split_oldCubicSquare
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter
  have hsecondSplit : secondFull ≈ secondRemainder + cubicSquare :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadratic_split_oldCubicSquare
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter
  have hfirstP4 : firstP4 ≈
      firstConnected + baseCentered * lagCentered := by
    unfold firstP4 firstConnected baseCentered lagCentered
    unfold openCubeHeatCayleyTraceP4
    exact Q'.eqv_refl _
  have hsecondP4 : secondP4 ≈
      secondConnected + baseCentered * nextCentered := by
    unfold secondP4 secondConnected baseCentered nextCentered
    unfold openCubeHeatCayleyTraceP4
    exact Q'.eqv_refl _
  have hcleared := cleared_common_remainder_split
    firstP4 secondP4 firstFull secondFull
    firstRemainder secondRemainder cubicSquare
    hfirstSplit hsecondSplit
  have hp4Difference := neighboringP4_difference_reduction
    firstP4 secondP4 firstConnected secondConnected
    baseCentered lagCentered nextCentered hfirstP4 hsecondP4
  unfold openCubeHeatCayleyTraceP6NeighboringNonCommonClearedComparison
    openCubeHeatCayleyTraceP6NonCommonClearedComparison
    openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison
    openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
  dsimp only
  change
    secondP4 * firstFull - firstP4 * secondFull ≈
      (secondP4 * firstRemainder - firstP4 * secondRemainder) +
        cubicSquare *
          ((secondConnected - firstConnected) +
            baseCentered * (nextCentered - lagCentered))
  refine Q'.eqv_trans _ _ _ hcleared ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_left cubicSquare _ _ hp4Difference)

/-- Final exact neighboring residual-free frontier: the genuinely
time-dependent no-OLD-cubic-square comparison, the reduced OLD cubic-square
residue, and the reduced OLD quadratic residue. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_final_decomposition
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      (openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter) +
      openCubeHeatCayleyTraceP6NeighboringOldQuadraticReducedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  refine Q'.eqv_trans _ _ _
    (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_decomposition
      timeBonds side sidePositive stage baseTime lag oldCenter) ?_
  exact Q'.add_eqv_congr'
    (openCubeHeatCayleyTraceP6NeighboringNonCommonClearedComparison_split_oldCubic
      timeBonds side sidePositive stage baseTime lag oldCenter)
    (Q'.eqv_refl _)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit.openCubeHeatCayleyTraceP6WithoutNegativeQuadratic_split_oldCubicSquare
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit.oldCubicSquare_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit.openCubeHeatCayleyTraceP6NeighboringNonCommonClearedComparison_split_oldCubic
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_final_decomposition
