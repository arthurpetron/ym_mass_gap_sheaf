/-
# Remaining OLD quadratic-center split in the neighboring P6 remainder

After removing the OLD cubic square and quartic center, the non-common `P6`
remainder still contains `c2` in its two quadratic OWN residuals.  Removing
that center leaves an OLD-center-free `P6` remainder and a new cleared bracket
built from the c4-free fourth OWN responses.  Unlike the previously combined
OLD-even bracket, this fourth-response bracket is genuinely new.

This exact finite split proves no sign for any surviving bracket, no `P4`
positivity, no denominator nonvanishing, no ORIGINAL-law center
identification, no cutoff-uniform estimate, no continuum Hamiltonian, and no
Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit

local infix:50 " ≈ " => Q'.eqv

private theorem quadratic_residual_products_split
    (connected leftA2 rightA2 leftA4 rightA4 c2 : Q') :
    (connected + (leftA2 - c2) * rightA4) +
        leftA4 * (rightA2 - c2) ≈
      ((connected + leftA2 * rightA4) + leftA4 * rightA2) +
        (-c2) * (leftA4 + rightA4) := by
  exact poly_identity_of_normal_eq
    (.add
      (.add (.var 0)
        (.mul (.add (.var 1) (.neg (.var 5))) (.var 4)))
      (.mul (.var 3) (.add (.var 2) (.neg (.var 5)))))
    (.add
      (.add
        (.add (.var 0) (.mul (.var 1) (.var 4)))
        (.mul (.var 3) (.var 2)))
      (.mul (.neg (.var 5)) (.add (.var 3) (.var 4))))
    (by decide) (fun
      | 0 => connected
      | 1 => leftA2
      | 2 => rightA2
      | 3 => leftA4
      | 4 => rightA4
      | _ => c2)

private theorem cleared_varying_residue_split
    (firstP4 secondP4 firstFull secondFull firstRemainder secondRemainder
      firstFourthSum secondFourthSum c2 : Q')
    (hfirst : firstFull ≈ firstRemainder + (-c2) * firstFourthSum)
    (hsecond : secondFull ≈ secondRemainder + (-c2) * secondFourthSum) :
    secondP4 * firstFull - firstP4 * secondFull ≈
      (secondP4 * firstRemainder - firstP4 * secondRemainder) +
        (-c2) *
          (secondP4 * firstFourthSum - firstP4 * secondFourthSum) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left secondP4 _ _ hfirst)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left firstP4 _ _ hsecond))) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.var 1)
        (.add (.var 2) (.mul (.neg (.var 6)) (.var 4))))
      (.neg
        (.mul (.var 0)
          (.add (.var 3) (.mul (.neg (.var 6)) (.var 5))))))
    (.add
      (.add (.mul (.var 1) (.var 2))
        (.neg (.mul (.var 0) (.var 3))))
      (.mul (.neg (.var 6))
        (.add (.mul (.var 1) (.var 4))
          (.neg (.mul (.var 0) (.var 5))))))
    (by decide) (fun
      | 0 => firstP4
      | 1 => secondP4
      | 2 => firstRemainder
      | 3 => secondRemainder
      | 4 => firstFourthSum
      | 5 => secondFourthSum
      | _ => c2)

/-- Non-common `P6` remainder after deleting the negative-quadratic piece and
all three supplied OLD center fields from the `P6` slot itself. -/
def openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let leftA2 := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime
  let rightA2 := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime
  let leftA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage leftTime
  let rightA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage rightTime
  (openCubeHeatCayleyTraceConnectedR6WithoutNegativeQuadratic
      timeBonds side sidePositive stage leftTime rightTime +
    leftA2 * rightA4) +
  leftA4 * rightA2

theorem openCubeHeatCayleyTraceP6WithoutOldCubicOrQuartic_split_c2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
          timeBonds side sidePositive stage leftTime rightTime +
        (-oldCenter.c2) *
          (openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
                timeBonds side sidePositive stage leftTime +
            openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
              timeBonds side sidePositive stage rightTime) := by
  unfold openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
    openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
  dsimp only
  exact quadratic_residual_products_split
    (openCubeHeatCayleyTraceConnectedR6WithoutNegativeQuadratic
      timeBonds side sidePositive stage leftTime rightTime)
    (openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage rightTime)
    (openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage rightTime)
    oldCenter.c2

/-- Raw neighboring bracket carried by the remaining OLD quadratic center in
the two c4-free fourth-response products. -/
def openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthClearedBracket
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  let baseA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage baseTime
  let lagA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage (baseTime + lag)
  let nextA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage (baseTime + (lag + 1))
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter *
      (baseA4 + lagA4) -
    openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter *
      (baseA4 + nextA4)

/-- Shared-time reduction of the new fourth-response neighboring bracket. -/
def openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
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
  let baseA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage baseTime
  let lagA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage (baseTime + lag)
  let nextA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage (baseTime + (lag + 1))
  let firstConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + lag)
  let secondConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + (lag + 1))
  (secondConnected * (baseA4 + lagA4) -
      firstConnected * (baseA4 + nextA4)) +
    baseCentered *
      (((nextCentered - lagCentered) * baseA4 +
          nextCentered * lagA4) -
        lagCentered * nextA4)

theorem openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthClearedBracket_reduction
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthClearedBracket
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
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
  let baseA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage baseTime
  let lagA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage (baseTime + lag)
  let nextA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage (baseTime + (lag + 1))
  let firstConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + lag)
  let secondConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + (lag + 1))
  unfold openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthClearedBracket
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
    openCubeHeatCayleyTraceP4
  dsimp only
  change
    (secondConnected + baseCentered * nextCentered) * (baseA4 + lagA4) -
        (firstConnected + baseCentered * lagCentered) *
          (baseA4 + nextA4) ≈
      (secondConnected * (baseA4 + lagA4) -
          firstConnected * (baseA4 + nextA4)) +
        baseCentered *
          (((nextCentered - lagCentered) * baseA4 +
              nextCentered * lagA4) -
            lagCentered * nextA4)
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.add (.var 0) (.mul (.var 1) (.var 3)))
        (.add (.var 4) (.var 5)))
      (.neg
        (.mul (.add (.var 2) (.mul (.var 1) (.var 6)))
          (.add (.var 4) (.var 7)))))
    (.add
      (.add
        (.mul (.var 0) (.add (.var 4) (.var 5)))
        (.neg (.mul (.var 2) (.add (.var 4) (.var 7)))))
      (.mul (.var 1)
        (.add
          (.add
            (.mul (.add (.var 3) (.neg (.var 6))) (.var 4))
            (.mul (.var 3) (.var 5)))
          (.neg (.mul (.var 6) (.var 7))))))
    (by decide) (fun
      | 0 => secondConnected
      | 1 => baseCentered
      | 2 => firstConnected
      | 3 => nextCentered
      | 4 => baseA4
      | 5 => lagA4
      | 6 => lagCentered
      | _ => nextA4)

/-- Neighboring cleared comparison whose `P6` slot remainder contains none
of the supplied OLD center fields.  The corrected `P4` weights remain the
actual OLD-centered denominator coefficients. -/
def openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter *
    openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
      timeBonds side sidePositive stage baseTime (baseTime + lag) -
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter *
    openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
      timeBonds side sidePositive stage baseTime (baseTime + (lag + 1))

theorem openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison_split_c2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        (-oldCenter.c2) *
          openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
            timeBonds side sidePositive stage baseTime lag oldCenter := by
  let firstP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage
    baseTime (baseTime + lag) oldCenter
  let secondP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage
    baseTime (baseTime + (lag + 1)) oldCenter
  let firstFull :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter
  let secondFull :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter
  let firstRemainder := openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
    timeBonds side sidePositive stage baseTime (baseTime + lag)
  let secondRemainder := openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
    timeBonds side sidePositive stage baseTime (baseTime + (lag + 1))
  let baseA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage baseTime
  let lagA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage (baseTime + lag)
  let nextA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage (baseTime + (lag + 1))
  let firstFourthSum := baseA4 + lagA4
  let secondFourthSum := baseA4 + nextA4
  have hfirst : firstFull ≈ firstRemainder + (-oldCenter.c2) * firstFourthSum :=
    openCubeHeatCayleyTraceP6WithoutOldCubicOrQuartic_split_c2
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter
  have hsecond : secondFull ≈ secondRemainder + (-oldCenter.c2) * secondFourthSum :=
    openCubeHeatCayleyTraceP6WithoutOldCubicOrQuartic_split_c2
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter
  have hcleared := cleared_varying_residue_split
    firstP4 secondP4 firstFull secondFull firstRemainder secondRemainder
    firstFourthSum secondFourthSum oldCenter.c2 hfirst hsecond
  have hbracket :=
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthClearedBracket_reduction
      timeBonds side sidePositive stage baseTime lag oldCenter
  unfold openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison
    openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
  change
    secondP4 * firstFull - firstP4 * secondFull ≈
      (secondP4 * firstRemainder - firstP4 * secondRemainder) +
        (-oldCenter.c2) *
          openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
            timeBonds side sidePositive stage baseTime lag oldCenter
  refine Q'.eqv_trans _ _ _ hcleared ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_left (-oldCenter.c2) _ _ hbracket)

/-- Final exact residual-free neighboring frontier after extracting every
supplied OLD field from the `P6` slot remainder. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_oldCenter_decomposition
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      ((openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
            timeBonds side sidePositive stage baseTime lag oldCenter +
          (-oldCenter.c2) *
            openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
              timeBonds side sidePositive stage baseTime lag oldCenter) +
        openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter) +
      openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  refine Q'.eqv_trans _ _ _
    (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_evenCenter_decomposition
      timeBonds side sidePositive stage baseTime lag oldCenter) ?_
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison_split_c2
        timeBonds side sidePositive stage baseTime lag oldCenter)
      (Q'.eqv_refl _))
    (Q'.eqv_refl _)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit.openCubeHeatCayleyTraceP6WithoutOldCubicOrQuartic_split_c2
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit.openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthClearedBracket_reduction
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit.openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison_split_c2
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_oldCenter_decomposition
