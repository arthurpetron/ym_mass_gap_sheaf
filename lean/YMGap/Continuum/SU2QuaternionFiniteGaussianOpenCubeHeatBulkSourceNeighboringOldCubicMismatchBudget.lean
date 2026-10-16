/-
# Quantitative OLD cubic-center mismatch budget

Changing only the supplied OLD cubic coefficient by `delta` changes its
response-independent square by

  `(c3 + delta)^2 - c3^2 = 2*c3*delta + delta^2`.

In the neighboring residual-free frontier this scalar multiplies exactly the
already-reduced difference of the two corrected `P4` coefficients.  This leaf
proves that identity, its canonical absolute payment, and the corresponding
actual-cleared sign transfer after paying the Heron approximation tolerance.

This is an exact consumer for a future ORIGINAL-to-reference `c3` comparison.
It supplies no such comparison, no bound on the neighboring bracket, no
strict margin, no ORIGINAL-law coefficient extraction, no continuum
Hamiltonian, and no Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticMismatchBudget
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringFiniteOwnCenterPin

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldCubicMismatchBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringClearedSignTransfer
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringFiniteOwnCenterPin

local infix:50 " ≈ " => Q'.eqv

/-- Change only the supplied OLD cubic center. -/
def shiftOldCubicCenter
    (oldCenter : CayleyTraceOldCenter) (delta : Q') : CayleyTraceOldCenter :=
  { c2 := oldCenter.c2
    c3 := oldCenter.c3 + delta
    c4 := oldCenter.c4 }

/-- Scalar change in the OLD cubic square under `c3 ↦ c3 + delta`. -/
def oldCubicSquareShiftCoefficient
    (oldCenter : CayleyTraceOldCenter) (delta : Q') : Q' :=
  (2 * oldCenter.c3) * delta + delta * delta

/-- At a parity-even reference center, the cubic-square mismatch is exactly
quadratic in the center error. -/
theorem oldCubicSquareShiftCoefficient_eqv_square_of_c3_zero
    (oldCenter : CayleyTraceOldCenter) (delta : Q')
    (hc3 : oldCenter.c3 ≈ 0) :
    oldCubicSquareShiftCoefficient oldCenter delta ≈ delta * delta := by
  have hscaled : 2 * oldCenter.c3 ≈ 2 * 0 :=
    Q'.mul_eqv_congr_left 2 _ _ hc3
  have hlinear : (2 * oldCenter.c3) * delta ≈ (2 * 0) * delta :=
    Q'.mul_eqv_congr_right _ _ delta hscaled
  unfold oldCubicSquareShiftCoefficient
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hlinear (Q'.eqv_refl (delta * delta))) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.mul (.const 2) (.const 0)) (.var 0))
      (.mul (.var 0) (.var 0)))
    (.mul (.var 0) (.var 0))
    (by decide) (fun _ => delta)

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

private theorem oldFreeComparison_shift_invariant
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldCubicCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  exact Q'.eqv_refl _

private theorem oldQuadraticFourthBracket_shift_invariant
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
        timeBonds side sidePositive stage baseTime lag
        (shiftOldCubicCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  exact Q'.eqv_refl _

private theorem combinedOldEvenComparison_shift_invariant
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldCubicCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  exact Q'.eqv_refl _

/-- The isolated OLD cubic-square contribution changes by the elementary
quadratic increment times the neighboring corrected-`P4` difference. -/
theorem openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison_shift_c3
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldCubicCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        oldCubicSquareShiftCoefficient oldCenter delta *
          ((openCubeHeatCayleyTraceConnectedR4
                timeBonds side sidePositive stage
                baseTime (baseTime + (lag + 1)) -
              openCubeHeatCayleyTraceConnectedR4
                timeBonds side sidePositive stage
                baseTime (baseTime + lag)) +
            (openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage baseTime - oldCenter.c2) *
              ((openCubeHeatCayleyTraceOwnA2Mean
                    timeBonds side sidePositive stage
                    (baseTime + (lag + 1)) - oldCenter.c2) -
                (openCubeHeatCayleyTraceOwnA2Mean
                    timeBonds side sidePositive stage
                    (baseTime + lag) - oldCenter.c2))) := by
  let bracket :=
    ((openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage
          baseTime (baseTime + (lag + 1)) -
        openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage
          baseTime (baseTime + lag)) +
      (openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage baseTime - oldCenter.c2) *
        ((openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage
              (baseTime + (lag + 1)) - oldCenter.c2) -
          (openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage
              (baseTime + lag) - oldCenter.c2)))
  unfold openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
    shiftOldCubicCenter oldCubicSquareShiftCoefficient
  dsimp only
  change
    ((-(oldCenter.c3 + delta)) * (-(oldCenter.c3 + delta))) * bracket ≈
      ((-oldCenter.c3) * (-oldCenter.c3)) * bracket +
        (((2 * oldCenter.c3) * delta + delta * delta) * bracket)
  exact poly_identity_of_normal_eq
    (.mul
      (.mul
        (.neg (.add (.var 0) (.var 1)))
        (.neg (.add (.var 0) (.var 1))))
      (.var 2))
    (.add
      (.mul (.mul (.neg (.var 0)) (.neg (.var 0))) (.var 2))
      (.mul
        (.add
          (.mul (.mul (.const 2) (.var 0)) (.var 1))
          (.mul (.var 1) (.var 1)))
        (.var 2)))
    (by decide) (fun
      | 0 => oldCenter.c3
      | 1 => delta
      | _ => bracket)

/-- Exact sensitivity of the complete residual-free neighboring frontier to
the supplied OLD cubic center. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c3
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldCubicCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        oldCubicSquareShiftCoefficient oldCenter delta *
          ((openCubeHeatCayleyTraceConnectedR4
                timeBonds side sidePositive stage
                baseTime (baseTime + (lag + 1)) -
              openCubeHeatCayleyTraceConnectedR4
                timeBonds side sidePositive stage
                baseTime (baseTime + lag)) +
            (openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage baseTime - oldCenter.c2) *
              ((openCubeHeatCayleyTraceOwnA2Mean
                    timeBonds side sidePositive stage
                    (baseTime + (lag + 1)) - oldCenter.c2) -
                (openCubeHeatCayleyTraceOwnA2Mean
                    timeBonds side sidePositive stage
                    (baseTime + lag) - oldCenter.c2))) := by
  let shifted := shiftOldCubicCenter oldCenter delta
  let oldFree :=
    openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let fourthBracket :=
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  let cubic := openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
    timeBonds side sidePositive stage baseTime lag oldCenter
  let even := openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
    timeBonds side sidePositive stage baseTime lag oldCenter
  let coefficient := oldCubicSquareShiftCoefficient oldCenter delta
  let bracket :=
    ((openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage
          baseTime (baseTime + (lag + 1)) -
        openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage
          baseTime (baseTime + lag)) +
      (openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage baseTime - oldCenter.c2) *
        ((openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage
              (baseTime + (lag + 1)) - oldCenter.c2) -
          (openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage
              (baseTime + lag) - oldCenter.c2)))
  have hshift :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_oldCenter_decomposition
      timeBonds side sidePositive stage baseTime lag shifted
  have hold :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_oldCenter_decomposition
      timeBonds side sidePositive stage baseTime lag oldCenter
  have holdFree := oldFreeComparison_shift_invariant
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  have hfourth := oldQuadraticFourthBracket_shift_invariant
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  have hcubic :=
    openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison_shift_c3
      timeBonds side sidePositive stage baseTime lag oldCenter delta
  have heven := combinedOldEvenComparison_shift_invariant
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  change
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag shifted ≈
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        coefficient * bracket
  refine Q'.eqv_trans _ _ _ hshift ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          holdFree
          (Q'.mul_eqv_congr_left (-oldCenter.c2) _ _ hfourth))
        hcubic)
      heven) ?_
  refine Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add
        (.add
          (.add
            (.var 0)
            (.mul (.neg (.var 1)) (.var 2)))
          (.add (.var 3) (.mul (.var 5) (.var 6))))
        (.var 4))
      (.add
        (.add
          (.add
            (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
            (.var 3))
          (.var 4))
        (.mul (.var 5) (.var 6)))
      (by decide) (fun
        | 0 => oldFree
        | 1 => oldCenter.c2
        | 2 => fourthBracket
        | 3 => cubic
        | 4 => even
        | 5 => coefficient
        | _ => bracket)) ?_
  exact Q'.add_eqv_congr_right _ _ (coefficient * bracket)
    (Q'.eqv_symm hold)

/-- Exact difference caused by changing only the supplied OLD cubic
coefficient. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c3_sub
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag
          (shiftOldCubicCenter oldCenter delta) -
        openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter ≈
      oldCubicSquareShiftCoefficient oldCenter delta *
        ((openCubeHeatCayleyTraceConnectedR4
              timeBonds side sidePositive stage
              baseTime (baseTime + (lag + 1)) -
            openCubeHeatCayleyTraceConnectedR4
              timeBonds side sidePositive stage
              baseTime (baseTime + lag)) +
          (openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage baseTime - oldCenter.c2) *
            ((openCubeHeatCayleyTraceOwnA2Mean
                  timeBonds side sidePositive stage
                  (baseTime + (lag + 1)) - oldCenter.c2) -
              (openCubeHeatCayleyTraceOwnA2Mean
                  timeBonds side sidePositive stage
                  (baseTime + lag) - oldCenter.c2))) := by
  let frontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let payment :=
    oldCubicSquareShiftCoefficient oldCenter delta *
      ((openCubeHeatCayleyTraceConnectedR4
            timeBonds side sidePositive stage
            baseTime (baseTime + (lag + 1)) -
          openCubeHeatCayleyTraceConnectedR4
            timeBonds side sidePositive stage
            baseTime (baseTime + lag)) +
        (openCubeHeatCayleyTraceOwnA2Mean
            timeBonds side sidePositive stage baseTime - oldCenter.c2) *
          ((openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage
                (baseTime + (lag + 1)) - oldCenter.c2) -
            (openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage
                (baseTime + lag) - oldCenter.c2)))
  have hsensitivity :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c3
      timeBonds side sidePositive stage baseTime lag oldCenter delta
  change
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag
          (shiftOldCubicCenter oldCenter delta) - frontier ≈ payment
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hsensitivity (Q'.eqv_refl (-frontier))) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
    (.var 1) (by decide) (fun
      | 0 => frontier
      | _ => payment)

/-- Canonical absolute payment for the OLD cubic-center mismatch. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c3_abs_le
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    Q'.abs
        (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
              timeBonds side sidePositive stage baseTime lag
              (shiftOldCubicCenter oldCenter delta) -
          openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
            timeBonds side sidePositive stage baseTime lag oldCenter) ≤
      Q'.abs (oldCubicSquareShiftCoefficient oldCenter delta) *
        Q'.abs
          ((openCubeHeatCayleyTraceConnectedR4
                timeBonds side sidePositive stage
                baseTime (baseTime + (lag + 1)) -
              openCubeHeatCayleyTraceConnectedR4
                timeBonds side sidePositive stage
                baseTime (baseTime + lag)) +
            (openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage baseTime - oldCenter.c2) *
              ((openCubeHeatCayleyTraceOwnA2Mean
                    timeBonds side sidePositive stage
                    (baseTime + (lag + 1)) - oldCenter.c2) -
                (openCubeHeatCayleyTraceOwnA2Mean
                    timeBonds side sidePositive stage
                    (baseTime + lag) - oldCenter.c2))) := by
  let bracket :=
    ((openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage
          baseTime (baseTime + (lag + 1)) -
        openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage
          baseTime (baseTime + lag)) +
      (openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage baseTime - oldCenter.c2) *
        ((openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage
              (baseTime + (lag + 1)) - oldCenter.c2) -
          (openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage
              (baseTime + lag) - oldCenter.c2)))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c3_sub
          timeBonds side sidePositive stage baseTime lag oldCenter delta))) ?_
  exact ExpNeg.abs_mul_le
    (oldCubicSquareShiftCoefficient oldCenter delta) bracket

/-- For the checked finite FREE-own center, parity makes the cubic mismatch
payment exactly quadratic in `delta`. -/
theorem openCubeHeatCayleyTraceP6NeighboringFiniteOwnCenter_shift_c3_abs_le
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (centerStage centerTime stage baseTime lag : Nat) (delta : Q') :
    Q'.abs
        (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
              timeBonds side sidePositive stage baseTime lag
              (shiftOldCubicCenter
                (openCubeHeatCayleyTraceFiniteOwnCenter
                  timeBonds side sidePositive centerStage centerTime)
                delta) -
          openCubeHeatCayleyTraceP6NeighboringFiniteOwnCenteredResidualFreeComparison
            timeBonds side sidePositive centerStage centerTime
            stage baseTime lag) ≤
      Q'.abs (delta * delta) *
        Q'.abs
          ((openCubeHeatCayleyTraceConnectedR4
                timeBonds side sidePositive stage
                baseTime (baseTime + (lag + 1)) -
              openCubeHeatCayleyTraceConnectedR4
                timeBonds side sidePositive stage
                baseTime (baseTime + lag)) +
            (openCubeHeatCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage baseTime -
              (openCubeHeatCayleyTraceFiniteOwnCenter
                timeBonds side sidePositive centerStage centerTime).c2) *
              ((openCubeHeatCayleyTraceOwnA2Mean
                    timeBonds side sidePositive stage
                    (baseTime + (lag + 1)) -
                  (openCubeHeatCayleyTraceFiniteOwnCenter
                    timeBonds side sidePositive centerStage centerTime).c2) -
                (openCubeHeatCayleyTraceOwnA2Mean
                    timeBonds side sidePositive stage
                    (baseTime + lag) -
                  (openCubeHeatCayleyTraceFiniteOwnCenter
                    timeBonds side sidePositive centerStage centerTime).c2))) := by
  let ownCenter := openCubeHeatCayleyTraceFiniteOwnCenter
    timeBonds side sidePositive centerStage centerTime
  let bracket :=
    ((openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage
          baseTime (baseTime + (lag + 1)) -
        openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage
          baseTime (baseTime + lag)) +
      (openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage baseTime - ownCenter.c2) *
        ((openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage
              (baseTime + (lag + 1)) - ownCenter.c2) -
          (openCubeHeatCayleyTraceOwnA2Mean
              timeBonds side sidePositive stage
              (baseTime + lag) - ownCenter.c2)))
  have hgeneral :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c3_abs_le
      timeBonds side sidePositive stage baseTime lag ownCenter delta
  have hcoefficient :
      oldCubicSquareShiftCoefficient ownCenter delta ≈ delta * delta :=
    oldCubicSquareShiftCoefficient_eqv_square_of_c3_zero ownCenter delta
      (openCubeHeatCayleyTraceFiniteOwnCenter_c3_zero
        timeBonds side sidePositive centerStage centerTime)
  change
    Q'.abs
        (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
              timeBonds side sidePositive stage baseTime lag
              (shiftOldCubicCenter ownCenter delta) -
          openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
            timeBonds side sidePositive stage baseTime lag ownCenter) ≤
      Q'.abs (delta * delta) * Q'.abs bracket
  exact Q'.le_trans' _ _ _ hgeneral
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.abs_eqv_congr hcoefficient)))

/-- A base-center margin which pays both the cubic-center mismatch and the
Heron approximation tail transfers to the actual shifted-center numerator. -/
theorem openCubeHeatCayleyTraceP6NeighboringClearedComparison_shift_c3_lt_zero_of_margin
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta centerError epsilon : Q')
    (hepsilon : (0 : Q') < epsilon)
    (hcenter :
      Q'.abs (oldCubicSquareShiftCoefficient oldCenter delta) *
          Q'.abs
            ((openCubeHeatCayleyTraceConnectedR4
                  timeBonds side sidePositive stage
                  baseTime (baseTime + (lag + 1)) -
                openCubeHeatCayleyTraceConnectedR4
                  timeBonds side sidePositive stage
                  baseTime (baseTime + lag)) +
              (openCubeHeatCayleyTraceOwnA2Mean
                  timeBonds side sidePositive stage baseTime - oldCenter.c2) *
                ((openCubeHeatCayleyTraceOwnA2Mean
                      timeBonds side sidePositive stage
                      (baseTime + (lag + 1)) - oldCenter.c2) -
                  (openCubeHeatCayleyTraceOwnA2Mean
                      timeBonds side sidePositive stage
                      (baseTime + lag) - oldCenter.c2))) ≤
        centerError)
    (hstage :
      bulkSourceHeatP6NeighboringClearedAdaptiveStage
          timeBonds side sidePositive baseTime lag
          (shiftOldCubicCenter oldCenter delta) epsilon ≤ stage)
    (hmargin :
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
            timeBonds side sidePositive stage baseTime lag oldCenter +
          (centerError + epsilon) < 0) :
    openCubeHeatCayleyTraceP6NeighboringClearedComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldCubicCenter oldCenter delta) < 0 := by
  let baseFrontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let shiftedFrontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag
      (shiftOldCubicCenter oldCenter delta)
  have habsolute : Q'.abs (shiftedFrontier - baseFrontier) ≤ centerError :=
    Q'.le_trans' _ _ _
      (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c3_abs_le
        timeBonds side sidePositive stage baseTime lag oldCenter delta)
      hcenter
  have hfrontier : shiftedFrontier ≤ baseFrontier + centerError :=
    value_le_reference_add_error shiftedFrontier baseFrontier centerError habsolute
  have hadd : shiftedFrontier + epsilon ≤
      (baseFrontier + centerError) + epsilon :=
    Q'.add_le_add_right _ _ epsilon hfrontier
  have hreassociate :
      (baseFrontier + centerError) + epsilon ≈
        baseFrontier + (centerError + epsilon) :=
    Q'.add_assoc_eqv baseFrontier centerError epsilon
  have hshiftedMargin : shiftedFrontier + epsilon < 0 :=
    Q'.lt_of_le_of_lt
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreassociate)) hmargin
  exact
    openCubeHeatCayleyTraceP6NeighboringClearedComparison_lt_zero_of_residualFree_margin
      timeBonds side sidePositive stage baseTime lag
      (shiftOldCubicCenter oldCenter delta)
      epsilon hepsilon hstage hshiftedMargin

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldCubicMismatchBudget

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldCubicMismatchBudget.openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison_shift_c3
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldCubicMismatchBudget.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c3
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldCubicMismatchBudget.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c3_abs_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldCubicMismatchBudget.openCubeHeatCayleyTraceP6NeighboringFiniteOwnCenter_shift_c3_abs_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldCubicMismatchBudget.openCubeHeatCayleyTraceP6NeighboringClearedComparison_shift_c3_lt_zero_of_margin
