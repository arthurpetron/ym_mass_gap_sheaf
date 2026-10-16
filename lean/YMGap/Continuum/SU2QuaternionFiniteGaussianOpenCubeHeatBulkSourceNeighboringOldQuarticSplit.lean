/-
# OLD quartic-center split in the neighboring residual-free P6 frontier

After deleting the response-independent OLD cubic square, the two fourth OWN
residuals still contain the same supplied OLD quartic center `c4`.  Removing
that center from each residual produces one common neighboring cleared
bracket.  It is exactly the bracket already multiplied by `(2/3)c2` in the
retained common-action term, so the two OLD-even residues combine with scalar
coefficient `(2/3)c2 - c4`.

This is exact finite algebra.  It proves no sign for the combined bracket or
the remaining no-OLD-quartic cleared term, no `P4` positivity, no denominator
nonvanishing, no ORIGINAL-law center identification, no cutoff-uniform
estimate, no continuum Hamiltonian, and no Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit

local infix:50 " ≈ " => Q'.eqv

private theorem fourth_residue_products_split
    (connected leftA2 rightA2 leftOld rightOld leftNoOld rightNoOld c4 : Q')
    (hleft : leftOld ≈ leftNoOld + (-c4))
    (hright : rightOld ≈ rightNoOld + (-c4)) :
    (connected + leftA2 * rightOld) + leftOld * rightA2 ≈
      ((connected + leftA2 * rightNoOld) + leftNoOld * rightA2) +
        (-c4) * (leftA2 + rightA2) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.mul_eqv_congr_left leftA2 _ _ hright))
      (Q'.mul_eqv_congr_right _ _ rightA2 hleft)) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.add (.var 0)
        (.mul (.var 1) (.add (.var 6) (.neg (.var 7)))))
      (.mul (.add (.var 5) (.neg (.var 7))) (.var 2)))
    (.add
      (.add
        (.add (.var 0) (.mul (.var 1) (.var 6)))
        (.mul (.var 5) (.var 2)))
      (.mul (.neg (.var 7)) (.add (.var 1) (.var 2))))
    (by decide) (fun
      | 0 => connected
      | 1 => leftA2
      | 2 => rightA2
      | 5 => leftNoOld
      | 6 => rightNoOld
      | _ => c4)

private theorem cleared_varying_residue_split
    (firstP4 secondP4 firstFull secondFull firstRemainder secondRemainder
      firstSourceSum secondSourceSum c4 : Q')
    (hfirst : firstFull ≈ firstRemainder + (-c4) * firstSourceSum)
    (hsecond : secondFull ≈ secondRemainder + (-c4) * secondSourceSum) :
    secondP4 * firstFull - firstP4 * secondFull ≈
      (secondP4 * firstRemainder - firstP4 * secondRemainder) +
        (-c4) *
          (secondP4 * firstSourceSum - firstP4 * secondSourceSum) := by
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
      | 4 => firstSourceSum
      | 5 => secondSourceSum
      | _ => c4)

/-- Fourth OWN response with the literal negative-quadratic covariance
removed and with no supplied OLD quartic center subtracted. -/
def openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let source := openCubeHeatBulkCayleyTraceA2
    timeBonds side sidePositive stage time
  let densityQuadratic := polySmul (-1)
    (completeOpenCubeHeatActionQuadraticPolynomial
      timeBonds (bulkSourceWidth side) stage)
  openCubeHeatCayleyTraceOwnA4Mean
      timeBonds side sidePositive stage time -
    finiteGaussianCovariance noiseCount source densityQuadratic

theorem openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic_split_c4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
        timeBonds side sidePositive stage time oldCenter ≈
      openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
          timeBonds side sidePositive stage time +
        (-oldCenter.c4) := by
  unfold openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
  dsimp only
  exact poly_identity_of_normal_eq
    (.add
      (.add (.var 0) (.neg (.var 1)))
      (.neg (.var 2)))
    (.add
      (.add (.var 0) (.neg (.var 2)))
      (.neg (.var 1)))
    (by decide) (fun
      | 0 => openCubeHeatCayleyTraceOwnA4Mean
          timeBonds side sidePositive stage time
      | 1 => oldCenter.c4
      | _ => finiteGaussianCovariance
          (bulkSourceNoiseCount timeBonds side)
          (openCubeHeatBulkCayleyTraceA2
            timeBonds side sidePositive stage time)
          (polySmul (-1)
            (completeOpenCubeHeatActionQuadraticPolynomial
              timeBonds (bulkSourceWidth side) stage)))

/-- Non-common corrected `P6` remainder after deleting the negative-quadratic
piece, OLD cubic square, and supplied OLD quartic center.  The OLD quadratic
center remains in the two `A2` residuals. -/
def openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let leftA2Residual := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime - oldCenter.c2
  let rightA2Residual := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime - oldCenter.c2
  let leftA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage leftTime
  let rightA4 :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage rightTime
  (openCubeHeatCayleyTraceConnectedR6WithoutNegativeQuadratic
      timeBonds side sidePositive stage leftTime rightTime +
    leftA2Residual * rightA4) +
  leftA4 * rightA2Residual

theorem openCubeHeatCayleyTraceP6WithoutOldCubic_split_c4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
          timeBonds side sidePositive stage leftTime rightTime oldCenter +
        (-oldCenter.c4) *
          ((openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage leftTime - oldCenter.c2) +
            (openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage rightTime - oldCenter.c2)) := by
  let connected := openCubeHeatCayleyTraceConnectedR6WithoutNegativeQuadratic
    timeBonds side sidePositive stage leftTime rightTime
  let leftA2 := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime - oldCenter.c2
  let rightA2 := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime - oldCenter.c2
  let leftOld :=
    openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
      timeBonds side sidePositive stage leftTime oldCenter
  let rightOld :=
    openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic
      timeBonds side sidePositive stage rightTime oldCenter
  let leftNoOld :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage leftTime
  let rightNoOld :=
    openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
      timeBonds side sidePositive stage rightTime
  have hleft : leftOld ≈ leftNoOld + (-oldCenter.c4) :=
    openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic_split_c4
      timeBonds side sidePositive stage leftTime oldCenter
  have hright : rightOld ≈ rightNoOld + (-oldCenter.c4) :=
    openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic_split_c4
      timeBonds side sidePositive stage rightTime oldCenter
  unfold openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
  dsimp only
  exact fourth_residue_products_split
    connected leftA2 rightA2 leftOld rightOld leftNoOld rightNoOld
    oldCenter.c4 hleft hright

/-- Raw neighboring OLD-even-center bracket before shared-time reduction. -/
def openCubeHeatCayleyTraceP6NeighboringOldEvenCenterClearedBracket
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter *
    openCubeHeatCayleyTraceP6OldQuadraticSourceSum
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter -
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter *
    openCubeHeatCayleyTraceP6OldQuadraticSourceSum
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter

/-- Shared-time reduction of the neighboring OLD-even-center bracket. -/
def openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
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
  (secondConnected * (baseCentered + lagCentered) -
      firstConnected * (baseCentered + nextCentered)) +
    (baseCentered * baseCentered) * (nextCentered - lagCentered)

theorem openCubeHeatCayleyTraceP6NeighboringOldEvenCenterClearedBracket_reduction
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterClearedBracket
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
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
  unfold openCubeHeatCayleyTraceP6NeighboringOldEvenCenterClearedBracket
    openCubeHeatCayleyTraceP6OldQuadraticSourceSum
    openCubeHeatCayleyTraceP4
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
  change
    (secondConnected + baseCentered * nextCentered) *
          (baseCentered + lagCentered) -
        (firstConnected + baseCentered * lagCentered) *
          (baseCentered + nextCentered) ≈
      (secondConnected * (baseCentered + lagCentered) -
          firstConnected * (baseCentered + nextCentered)) +
        (baseCentered * baseCentered) *
          (nextCentered - lagCentered)
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.add (.var 0) (.mul (.var 1) (.var 3)))
        (.add (.var 1) (.var 2)))
      (.neg
        (.mul (.add (.var 4) (.mul (.var 1) (.var 2)))
          (.add (.var 1) (.var 3)))))
    (.add
      (.add
        (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.neg (.mul (.var 4) (.add (.var 1) (.var 3)))))
      (.mul (.mul (.var 1) (.var 1))
        (.add (.var 3) (.neg (.var 2)))))
    (by decide) (fun
      | 0 => secondConnected
      | 1 => baseCentered
      | 2 => lagCentered
      | 3 => nextCentered
      | _ => firstConnected)

/-- Neighboring cleared comparison after deleting the OLD cubic square and
the supplied OLD quartic center from both response slots. -/
def openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter *
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter -
  openCubeHeatCayleyTraceP4
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter *
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter

theorem openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison_split_c4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        (-oldCenter.c4) *
          openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
            timeBonds side sidePositive stage baseTime lag oldCenter := by
  let firstP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage
    baseTime (baseTime + lag) oldCenter
  let secondP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage
    baseTime (baseTime + (lag + 1)) oldCenter
  let firstFull :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter
  let secondFull :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticAndOldCubicSquare
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter
  let firstRemainder :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter
  let secondRemainder :=
    openCubeHeatCayleyTraceP6WithoutNegativeQuadraticOldCubicOrQuartic
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter
  let firstSourceSum := openCubeHeatCayleyTraceP6OldQuadraticSourceSum
    timeBonds side sidePositive stage
    baseTime (baseTime + lag) oldCenter
  let secondSourceSum := openCubeHeatCayleyTraceP6OldQuadraticSourceSum
    timeBonds side sidePositive stage
    baseTime (baseTime + (lag + 1)) oldCenter
  have hfirst : firstFull ≈ firstRemainder + (-oldCenter.c4) * firstSourceSum :=
    openCubeHeatCayleyTraceP6WithoutOldCubic_split_c4
      timeBonds side sidePositive stage
      baseTime (baseTime + lag) oldCenter
  have hsecond : secondFull ≈ secondRemainder + (-oldCenter.c4) * secondSourceSum :=
    openCubeHeatCayleyTraceP6WithoutOldCubic_split_c4
      timeBonds side sidePositive stage
      baseTime (baseTime + (lag + 1)) oldCenter
  have hcleared := cleared_varying_residue_split
    firstP4 secondP4 firstFull secondFull firstRemainder secondRemainder
    firstSourceSum secondSourceSum oldCenter.c4 hfirst hsecond
  have hbracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterClearedBracket_reduction
      timeBonds side sidePositive stage baseTime lag oldCenter
  unfold openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison
    openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison
  change
    secondP4 * firstFull - firstP4 * secondFull ≈
      (secondP4 * firstRemainder - firstP4 * secondRemainder) +
        (-oldCenter.c4) *
          openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
            timeBonds side sidePositive stage baseTime lag oldCenter
  refine Q'.eqv_trans _ _ _ hcleared ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_left (-oldCenter.c4) _ _ hbracket)

/-- Combined OLD-even-center contribution after exact neighboring
simplification. -/
def openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  (heatActionTwoThird * oldCenter.c2 - oldCenter.c4) *
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter

/-- Final exact neighboring residual-free frontier after combining the
supplied OLD quadratic and quartic centers. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_evenCenter_decomposition
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag oldCenter ≈
      (openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter) +
      openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  let noCubic := openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison
    timeBonds side sidePositive stage baseTime lag oldCenter
  let noCubicOrQuartic :=
    openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicOrQuarticClearedComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let cubic := openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
    timeBonds side sidePositive stage baseTime lag oldCenter
  let bracket := openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
    timeBonds side sidePositive stage baseTime lag oldCenter
  have hfrontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_final_decomposition
      timeBonds side sidePositive stage baseTime lag oldCenter
  have hquartic :=
    openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison_split_c4
      timeBonds side sidePositive stage baseTime lag oldCenter
  have hquadratic :
      openCubeHeatCayleyTraceP6NeighboringOldQuadraticReducedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter ≈
        (heatActionTwoThird * oldCenter.c2) * bracket := by
    unfold bracket
    unfold openCubeHeatCayleyTraceP6NeighboringOldQuadraticReducedComparison
      openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ hfrontier ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hquartic (Q'.eqv_refl cubic))
      hquadratic) ?_
  unfold openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
  change
    ((noCubicOrQuartic + (-oldCenter.c4) * bracket) + cubic) +
        (heatActionTwoThird * oldCenter.c2) * bracket ≈
      (noCubicOrQuartic + cubic) +
        (heatActionTwoThird * oldCenter.c2 - oldCenter.c4) * bracket
  exact poly_identity_of_normal_eq
    (.add
      (.add
        (.add (.var 0) (.mul (.neg (.var 3)) (.var 2)))
        (.var 1))
      (.mul (.var 4) (.var 2)))
    (.add
      (.add (.var 0) (.var 1))
      (.mul (.add (.var 4) (.neg (.var 3))) (.var 2)))
    (by decide) (fun
      | 0 => noCubicOrQuartic
      | 1 => cubic
      | 2 => bracket
      | 3 => oldCenter.c4
      | _ => heatActionTwoThird * oldCenter.c2)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit.openCubeHeatCayleyTraceOwnA4OldResidualWithoutNegativeQuadratic_split_c4
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit.openCubeHeatCayleyTraceP6WithoutOldCubic_split_c4
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit.openCubeHeatCayleyTraceP6NeighboringOldEvenCenterClearedBracket_reduction
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit.openCubeHeatCayleyTraceP6NeighboringWithoutOldCubicClearedComparison_split_c4
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_evenCenter_decomposition
