/-
# Quantitative OLD quadratic-center mismatch budget

The supplied OLD quadratic coefficient enters every centered second response,
both corrected `P4` weights, the c4-free fourth-response bracket, the retained
OLD cubic-square bracket, and the combined `(2/3)c2-c4` bracket.  Consequently
its neighboring-frontier sensitivity is cubic rather than affine.

This leaf keeps those four effects separate and proves the exact factorization

  `frontier(c2 + delta) - frontier(c2) = delta * c2ShiftResponse`.

It then gives the canonical absolute payment and composes it with the existing
Heron-tail sign transfer.  This is an exact consumer for a future
ORIGINAL-to-reference `c2` comparison.  It supplies no such comparison, no
bound on the response coefficient, no strict margin, no ORIGINAL-law
coefficient extraction, no continuum Hamiltonian, and no Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldCubicMismatchBudget

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringClearedSignTransfer

local infix:50 " ≈ " => Q'.eqv

/-- Change only the supplied OLD quadratic center. -/
def shiftOldQuadraticCenter
    (oldCenter : CayleyTraceOldCenter) (delta : Q') : CayleyTraceOldCenter :=
  { c2 := oldCenter.c2 + delta
    c3 := oldCenter.c3
    c4 := oldCenter.c4 }

/-- Coefficient of `delta` in the shift of the denominator-weighted,
OLD-free `P6` remainder. -/
def oldFreeC2ShiftCoefficient
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') : Q' :=
  let baseCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage baseTime - oldCenter.c2
  let lagCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage (baseTime + lag) - oldCenter.c2
  let nextCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage (baseTime + (lag + 1)) - oldCenter.c2
  let firstRemainder := openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
    timeBonds side sidePositive stage baseTime (baseTime + lag)
  let secondRemainder := openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
    timeBonds side sidePositive stage baseTime (baseTime + (lag + 1))
  (-(baseCentered + nextCentered) + delta) * firstRemainder -
    (-(baseCentered + lagCentered) + delta) * secondRemainder

/-- Coefficient of `delta` in the c4-free fourth-response bracket. -/
def oldQuadraticFourthBracketC2ShiftCoefficient
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') : Q' :=
  let baseCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage baseTime - oldCenter.c2
  let lagCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage (baseTime + lag) - oldCenter.c2
  let nextCentered := openCubeHeatCayleyTraceOwnA2Mean
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
  let inner :=
    ((nextCentered - lagCentered) * baseA4 + nextCentered * lagA4) -
      lagCentered * nextA4
  baseCentered * (nextA4 - lagA4) - inner -
    delta * (nextA4 - lagA4)

/-- Coefficient of `delta` in the retained OLD cubic-square contribution. -/
def oldCubicC2ShiftCoefficient
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  let lagCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage (baseTime + lag) - oldCenter.c2
  let nextCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage (baseTime + (lag + 1)) - oldCenter.c2
  ((-oldCenter.c3) * (-oldCenter.c3)) * (-(nextCentered - lagCentered))

/-- Coefficient of `delta` in the reduced OLD-even bracket. -/
def oldEvenBracketC2ShiftCoefficient
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') : Q' :=
  let baseCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage baseTime - oldCenter.c2
  let lagCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage (baseTime + lag) - oldCenter.c2
  let nextCentered := openCubeHeatCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage (baseTime + (lag + 1)) - oldCenter.c2
  let firstConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + lag)
  let secondConnected := openCubeHeatCayleyTraceConnectedR4
    timeBonds side sidePositive stage baseTime (baseTime + (lag + 1))
  (-2) * secondConnected + 2 * firstConnected +
    ((-2) * baseCentered + delta) * (nextCentered - lagCentered)

/-- Full coefficient after factoring one `delta` from the quadratic-center
change of the residual-free neighboring frontier. -/
def oldQuadraticCenterShiftResponse
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') : Q' :=
  let fourthBracket :=
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  let evenBracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  let fourthShift := oldQuadraticFourthBracketC2ShiftCoefficient
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  let evenShift := oldEvenBracketC2ShiftCoefficient
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  ((oldFreeC2ShiftCoefficient
        timeBonds side sidePositive stage baseTime lag oldCenter delta +
      ((-fourthBracket) +
        (-(oldCenter.c2 + delta)) * fourthShift)) +
    oldCubicC2ShiftCoefficient
      timeBonds side sidePositive stage baseTime lag oldCenter) +
  (heatActionTwoThird * evenBracket +
    (heatActionTwoThird * (oldCenter.c2 + delta) - oldCenter.c4) * evenShift)

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

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem sub_add_center_eqv
    (value center delta : Q') :
    value - (center + delta) ≈ (value - center) - delta := by
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.neg (.add (.var 1) (.var 2))))
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
    (by decide) (fun
      | 0 => value
      | 1 => center
      | _ => delta)

private theorem oldFree_c2_shift_scalar
    (firstConnected secondConnected baseCentered lagCentered nextCentered
      firstRemainder secondRemainder delta : Q') :
    (secondConnected + (baseCentered - delta) * (nextCentered - delta)) *
          firstRemainder -
        (firstConnected + (baseCentered - delta) * (lagCentered - delta)) *
          secondRemainder ≈
      ((secondConnected + baseCentered * nextCentered) * firstRemainder -
          (firstConnected + baseCentered * lagCentered) * secondRemainder) +
        delta *
          ((-(baseCentered + nextCentered) + delta) * firstRemainder -
            (-(baseCentered + lagCentered) + delta) * secondRemainder) := by
  exact poly_identity_of_normal_eq
    (.add
      (.mul
        (.add (.var 0)
          (.mul
            (.add (.var 1) (.neg (.var 7)))
            (.add (.var 3) (.neg (.var 7)))))
        (.var 4))
      (.neg
        (.mul
          (.add (.var 2)
            (.mul
              (.add (.var 1) (.neg (.var 7)))
              (.add (.var 5) (.neg (.var 7)))))
          (.var 6))))
    (.add
      (.add
        (.mul (.add (.var 0) (.mul (.var 1) (.var 3))) (.var 4))
        (.neg
          (.mul (.add (.var 2) (.mul (.var 1) (.var 5))) (.var 6))))
      (.mul (.var 7)
        (.add
          (.mul
            (.add (.neg (.add (.var 1) (.var 3))) (.var 7))
            (.var 4))
          (.neg
            (.mul
              (.add (.neg (.add (.var 1) (.var 5))) (.var 7))
              (.var 6))))))
    (by decide) (fun
      | 0 => secondConnected
      | 1 => baseCentered
      | 2 => firstConnected
      | 3 => nextCentered
      | 4 => firstRemainder
      | 5 => lagCentered
      | 6 => secondRemainder
      | _ => delta)

private theorem oldFree_c2_shift_raw
    (firstConnected secondConnected baseMean lagMean nextMean center
      firstRemainder secondRemainder delta : Q') :
    (secondConnected +
          (baseMean - (center + delta)) * (nextMean - (center + delta))) *
          firstRemainder -
        (firstConnected +
          (baseMean - (center + delta)) * (lagMean - (center + delta))) *
          secondRemainder ≈
      ((secondConnected + (baseMean - center) * (nextMean - center)) *
          firstRemainder -
        (firstConnected + (baseMean - center) * (lagMean - center)) *
          secondRemainder) +
      delta *
        ((-((baseMean - center) + (nextMean - center)) + delta) *
            firstRemainder -
          (-((baseMean - center) + (lagMean - center)) + delta) *
            secondRemainder) := by
  have hbase := sub_add_center_eqv baseMean center delta
  have hlag := sub_add_center_eqv lagMean center delta
  have hnext := sub_add_center_eqv nextMean center delta
  have hfirstP4 :
      firstConnected +
          (baseMean - (center + delta)) * (lagMean - (center + delta)) ≈
        firstConnected +
          ((baseMean - center) - delta) * ((lagMean - center) - delta) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _) (mul_congr hbase hlag)
  have hsecondP4 :
      secondConnected +
          (baseMean - (center + delta)) * (nextMean - (center + delta)) ≈
        secondConnected +
          ((baseMean - center) - delta) * ((nextMean - center) - delta) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _) (mul_congr hbase hnext)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ firstRemainder hsecondP4)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ secondRemainder hfirstP4))) ?_
  exact oldFree_c2_shift_scalar
    firstConnected secondConnected
    (baseMean - center) (lagMean - center) (nextMean - center)
    firstRemainder secondRemainder delta

private theorem fourthBracket_c2_shift_scalar
    (constantPart baseCentered nextCentered lagCentered baseA4 lagA4 nextA4
      delta : Q') :
    constantPart +
        (baseCentered - delta) *
          ((((nextCentered - delta) - (lagCentered - delta)) * baseA4 +
              (nextCentered - delta) * lagA4) -
            (lagCentered - delta) * nextA4) ≈
      (constantPart +
          baseCentered *
            (((nextCentered - lagCentered) * baseA4 + nextCentered * lagA4) -
              lagCentered * nextA4)) +
        delta *
          (baseCentered * (nextA4 - lagA4) -
            (((nextCentered - lagCentered) * baseA4 + nextCentered * lagA4) -
              lagCentered * nextA4) -
            delta * (nextA4 - lagA4)) := by
  exact poly_identity_of_normal_eq
    (.add (.var 0)
      (.mul (.add (.var 1) (.neg (.var 7)))
        (.add
          (.add
            (.mul
              (.add
                (.add (.var 2) (.neg (.var 7)))
                (.neg (.add (.var 3) (.neg (.var 7)))))
              (.var 4))
            (.mul (.add (.var 2) (.neg (.var 7))) (.var 5)))
          (.neg
            (.mul (.add (.var 3) (.neg (.var 7))) (.var 6))))))
    (.add
      (.add (.var 0) (.mul (.var 1)
        (.add
          (.add
            (.mul (.add (.var 2) (.neg (.var 3))) (.var 4))
            (.mul (.var 2) (.var 5)))
          (.neg (.mul (.var 3) (.var 6))))))
      (.mul (.var 7)
        (.add
          (.add
            (.mul (.var 1) (.add (.var 6) (.neg (.var 5))))
            (.neg
              (.add
                (.add
                  (.mul (.add (.var 2) (.neg (.var 3))) (.var 4))
                  (.mul (.var 2) (.var 5)))
                (.neg (.mul (.var 3) (.var 6))))))
          (.neg
            (.mul (.var 7) (.add (.var 6) (.neg (.var 5))))))))
    (by decide) (fun
      | 0 => constantPart
      | 1 => baseCentered
      | 2 => nextCentered
      | 3 => lagCentered
      | 4 => baseA4
      | 5 => lagA4
      | 6 => nextA4
      | _ => delta)

private theorem fourthBracket_c2_shift_raw
    (constantPart baseMean nextMean lagMean center baseA4 lagA4 nextA4
      delta : Q') :
    constantPart +
        (baseMean - (center + delta)) *
          ((((nextMean - (center + delta)) -
                (lagMean - (center + delta))) * baseA4 +
              (nextMean - (center + delta)) * lagA4) -
            (lagMean - (center + delta)) * nextA4) ≈
      (constantPart +
          (baseMean - center) *
            ((((nextMean - center) - (lagMean - center)) * baseA4 +
                (nextMean - center) * lagA4) -
              (lagMean - center) * nextA4)) +
        delta *
          ((baseMean - center) * (nextA4 - lagA4) -
            ((((nextMean - center) - (lagMean - center)) * baseA4 +
                (nextMean - center) * lagA4) -
              (lagMean - center) * nextA4) -
            delta * (nextA4 - lagA4)) := by
  have hbase := sub_add_center_eqv baseMean center delta
  have hlag := sub_add_center_eqv lagMean center delta
  have hnext := sub_add_center_eqv nextMean center delta
  have hdifference :
      (nextMean - (center + delta)) - (lagMean - (center + delta)) ≈
        ((nextMean - center) - delta) - ((lagMean - center) - delta) :=
    Q'.add_eqv_congr' hnext (Q'.neg_eqv_congr _ _ hlag)
  have hinner :
      (((nextMean - (center + delta)) -
              (lagMean - (center + delta))) * baseA4 +
            (nextMean - (center + delta)) * lagA4) -
          (lagMean - (center + delta)) * nextA4 ≈
        ((((nextMean - center) - delta) - ((lagMean - center) - delta)) *
              baseA4 +
            ((nextMean - center) - delta) * lagA4) -
          ((lagMean - center) - delta) * nextA4 :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ baseA4 hdifference)
        (Q'.mul_eqv_congr_right _ _ lagA4 hnext))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ nextA4 hlag))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (mul_congr hbase hinner)) ?_
  exact fourthBracket_c2_shift_scalar
    constantPart (baseMean - center) (nextMean - center) (lagMean - center)
    baseA4 lagA4 nextA4 delta

private theorem oldCubic_c2_shift_scalar
    (cubicSquare connectedDifference baseCentered nextCentered lagCentered
      delta : Q') :
    cubicSquare *
        (connectedDifference +
          (baseCentered - delta) *
            ((nextCentered - delta) - (lagCentered - delta))) ≈
      cubicSquare *
          (connectedDifference +
            baseCentered * (nextCentered - lagCentered)) +
        delta * (cubicSquare * (-(nextCentered - lagCentered))) := by
  exact poly_identity_of_normal_eq
    (.mul (.var 0)
      (.add (.var 1)
        (.mul (.add (.var 2) (.neg (.var 5)))
          (.add
            (.add (.var 3) (.neg (.var 5)))
            (.neg (.add (.var 4) (.neg (.var 5))))))))
    (.add
      (.mul (.var 0)
        (.add (.var 1)
          (.mul (.var 2) (.add (.var 3) (.neg (.var 4))))))
      (.mul (.var 5)
        (.mul (.var 0) (.neg (.add (.var 3) (.neg (.var 4)))))))
    (by decide) (fun
      | 0 => cubicSquare
      | 1 => connectedDifference
      | 2 => baseCentered
      | 3 => nextCentered
      | 4 => lagCentered
      | _ => delta)

private theorem oldCubic_c2_shift_raw
    (cubicSquare connectedDifference baseMean nextMean lagMean center delta : Q') :
    cubicSquare *
        (connectedDifference +
          (baseMean - (center + delta)) *
            ((nextMean - (center + delta)) -
              (lagMean - (center + delta)))) ≈
      cubicSquare *
          (connectedDifference +
            (baseMean - center) *
              ((nextMean - center) - (lagMean - center))) +
        delta *
          (cubicSquare *
            (-((nextMean - center) - (lagMean - center)))) := by
  have hbase := sub_add_center_eqv baseMean center delta
  have hlag := sub_add_center_eqv lagMean center delta
  have hnext := sub_add_center_eqv nextMean center delta
  have hdifference :
      (nextMean - (center + delta)) - (lagMean - (center + delta)) ≈
        ((nextMean - center) - delta) - ((lagMean - center) - delta) :=
    Q'.add_eqv_congr' hnext (Q'.neg_eqv_congr _ _ hlag)
  have hproduct :
      (baseMean - (center + delta)) *
          ((nextMean - (center + delta)) -
            (lagMean - (center + delta))) ≈
        ((baseMean - center) - delta) *
          (((nextMean - center) - delta) - ((lagMean - center) - delta)) :=
    mul_congr hbase hdifference
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left cubicSquare _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hproduct)) ?_
  exact oldCubic_c2_shift_scalar cubicSquare connectedDifference
    (baseMean - center) (nextMean - center) (lagMean - center) delta

private theorem oldEvenBracket_c2_shift_scalar
    (secondConnected baseCentered lagCentered firstConnected nextCentered
      delta : Q') :
    (secondConnected *
          ((baseCentered - delta) + (lagCentered - delta)) -
        firstConnected *
          ((baseCentered - delta) + (nextCentered - delta))) +
      ((baseCentered - delta) * (baseCentered - delta)) *
        ((nextCentered - delta) - (lagCentered - delta)) ≈
      ((secondConnected * (baseCentered + lagCentered) -
          firstConnected * (baseCentered + nextCentered)) +
        (baseCentered * baseCentered) * (nextCentered - lagCentered)) +
      delta *
        (((-2) * secondConnected + 2 * firstConnected) +
          ((-2) * baseCentered + delta) *
            (nextCentered - lagCentered)) := by
  exact poly_identity_of_normal_eq
    (.add
      (.add
        (.mul (.var 0)
          (.add
            (.add (.var 1) (.neg (.var 5)))
            (.add (.var 2) (.neg (.var 5)))))
        (.neg
          (.mul (.var 3)
            (.add
              (.add (.var 1) (.neg (.var 5)))
              (.add (.var 4) (.neg (.var 5)))))))
      (.mul
        (.mul
          (.add (.var 1) (.neg (.var 5)))
          (.add (.var 1) (.neg (.var 5))))
        (.add
          (.add (.var 4) (.neg (.var 5)))
          (.neg (.add (.var 2) (.neg (.var 5)))))))
    (.add
      (.add
        (.add
          (.mul (.var 0) (.add (.var 1) (.var 2)))
          (.neg (.mul (.var 3) (.add (.var 1) (.var 4)))))
        (.mul (.mul (.var 1) (.var 1))
          (.add (.var 4) (.neg (.var 2)))))
      (.mul (.var 5)
        (.add
          (.add
            (.mul (.const (-2)) (.var 0))
            (.mul (.const 2) (.var 3)))
          (.mul
            (.add (.mul (.const (-2)) (.var 1)) (.var 5))
            (.add (.var 4) (.neg (.var 2)))))))
    (by decide) (fun
      | 0 => secondConnected
      | 1 => baseCentered
      | 2 => lagCentered
      | 3 => firstConnected
      | 4 => nextCentered
      | _ => delta)

private theorem oldEvenBracket_c2_shift_raw
    (secondConnected baseMean lagMean firstConnected nextMean center delta : Q') :
    (secondConnected *
          ((baseMean - (center + delta)) + (lagMean - (center + delta))) -
        firstConnected *
          ((baseMean - (center + delta)) + (nextMean - (center + delta)))) +
      ((baseMean - (center + delta)) * (baseMean - (center + delta))) *
        ((nextMean - (center + delta)) -
          (lagMean - (center + delta))) ≈
      ((secondConnected * ((baseMean - center) + (lagMean - center)) -
          firstConnected * ((baseMean - center) + (nextMean - center))) +
        ((baseMean - center) * (baseMean - center)) *
          ((nextMean - center) - (lagMean - center))) +
      delta *
        (((-2) * secondConnected + 2 * firstConnected) +
          ((-2) * (baseMean - center) + delta) *
            ((nextMean - center) - (lagMean - center))) := by
  have hbase := sub_add_center_eqv baseMean center delta
  have hlag := sub_add_center_eqv lagMean center delta
  have hnext := sub_add_center_eqv nextMean center delta
  have hbaseLag :
      (baseMean - (center + delta)) + (lagMean - (center + delta)) ≈
        ((baseMean - center) - delta) + ((lagMean - center) - delta) :=
    Q'.add_eqv_congr' hbase hlag
  have hbaseNext :
      (baseMean - (center + delta)) + (nextMean - (center + delta)) ≈
        ((baseMean - center) - delta) + ((nextMean - center) - delta) :=
    Q'.add_eqv_congr' hbase hnext
  have hdifference :
      (nextMean - (center + delta)) - (lagMean - (center + delta)) ≈
        ((nextMean - center) - delta) - ((lagMean - center) - delta) :=
    Q'.add_eqv_congr' hnext (Q'.neg_eqv_congr _ _ hlag)
  have hsquare :
      (baseMean - (center + delta)) * (baseMean - (center + delta)) ≈
        ((baseMean - center) - delta) * ((baseMean - center) - delta) :=
    mul_congr hbase hbase
  have hleft :
      (secondConnected *
            ((baseMean - (center + delta)) + (lagMean - (center + delta))) -
          firstConnected *
            ((baseMean - (center + delta)) + (nextMean - (center + delta)))) +
        ((baseMean - (center + delta)) * (baseMean - (center + delta))) *
          ((nextMean - (center + delta)) -
            (lagMean - (center + delta))) ≈
      (secondConnected *
            (((baseMean - center) - delta) + ((lagMean - center) - delta)) -
          firstConnected *
            (((baseMean - center) - delta) + ((nextMean - center) - delta))) +
        (((baseMean - center) - delta) * ((baseMean - center) - delta)) *
          (((nextMean - center) - delta) - ((lagMean - center) - delta)) :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left secondConnected _ _ hbaseLag)
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left firstConnected _ _ hbaseNext)))
      (mul_congr hsquare hdifference)
  refine Q'.eqv_trans _ _ _ hleft ?_
  exact oldEvenBracket_c2_shift_scalar secondConnected (baseMean - center)
    (lagMean - center) firstConnected (nextMean - center) delta

/-- Exact shift of the denominator-weighted OLD-free `P6` remainder. -/
theorem openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison_shift_c2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuadraticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        delta * oldFreeC2ShiftCoefficient
          timeBonds side sidePositive stage baseTime lag oldCenter delta := by
  simpa only [
      openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison,
      openCubeHeatCayleyTraceP4, shiftOldQuadraticCenter,
      oldFreeC2ShiftCoefficient]
    using oldFree_c2_shift_raw
      (openCubeHeatCayleyTraceConnectedR4
        timeBonds side sidePositive stage baseTime (baseTime + lag))
      (openCubeHeatCayleyTraceConnectedR4
        timeBonds side sidePositive stage baseTime (baseTime + (lag + 1)))
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage baseTime)
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + lag))
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + (lag + 1)))
      oldCenter.c2
      (openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
        timeBonds side sidePositive stage baseTime (baseTime + lag))
      (openCubeHeatCayleyTraceP6NonCommonWithoutOldCenters
        timeBonds side sidePositive stage baseTime (baseTime + (lag + 1)))
      delta

/-- Exact shift of the c4-free fourth-response bracket. -/
theorem openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket_shift_c2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuadraticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
          timeBonds side sidePositive stage baseTime lag oldCenter +
        delta * oldQuadraticFourthBracketC2ShiftCoefficient
          timeBonds side sidePositive stage baseTime lag oldCenter delta := by
  simpa only [
      openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket,
      shiftOldQuadraticCenter,
      oldQuadraticFourthBracketC2ShiftCoefficient]
    using fourthBracket_c2_shift_raw
      (openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage baseTime (baseTime + (lag + 1)) *
          (openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
              timeBonds side sidePositive stage baseTime +
            openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
              timeBonds side sidePositive stage (baseTime + lag)) -
        openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage baseTime (baseTime + lag) *
          (openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
              timeBonds side sidePositive stage baseTime +
            openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
              timeBonds side sidePositive stage (baseTime + (lag + 1))))
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage baseTime)
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + (lag + 1)))
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + lag))
      oldCenter.c2
      (openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
        timeBonds side sidePositive stage baseTime)
      (openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
        timeBonds side sidePositive stage (baseTime + lag))
      (openCubeHeatCayleyTraceOwnA4ResidualWithoutNegativeQuadraticAndOldCenter
        timeBonds side sidePositive stage (baseTime + (lag + 1)))
      delta

/-- Exact shift of the retained OLD cubic-square contribution under a
quadratic-center change. -/
theorem openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison_shift_c2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuadraticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        delta * oldCubicC2ShiftCoefficient
          timeBonds side sidePositive stage baseTime lag oldCenter := by
  simpa only [openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison,
      shiftOldQuadraticCenter, oldCubicC2ShiftCoefficient]
    using oldCubic_c2_shift_raw
      ((-oldCenter.c3) * (-oldCenter.c3))
      (openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage baseTime (baseTime + (lag + 1)) -
        openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive stage baseTime (baseTime + lag))
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage baseTime)
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + (lag + 1)))
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + lag))
      oldCenter.c2
      delta

/-- Exact shift of the reduced OLD-even bracket. -/
theorem openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket_shift_c2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuadraticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
          timeBonds side sidePositive stage baseTime lag oldCenter +
        delta * oldEvenBracketC2ShiftCoefficient
          timeBonds side sidePositive stage baseTime lag oldCenter delta := by
  simpa only [openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket,
      shiftOldQuadraticCenter, oldEvenBracketC2ShiftCoefficient]
    using oldEvenBracket_c2_shift_raw
      (openCubeHeatCayleyTraceConnectedR4
        timeBonds side sidePositive stage baseTime (baseTime + (lag + 1)))
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage baseTime)
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + lag))
      (openCubeHeatCayleyTraceConnectedR4
        timeBonds side sidePositive stage baseTime (baseTime + lag))
      (openCubeHeatCayleyTraceOwnA2Mean
        timeBonds side sidePositive stage (baseTime + (lag + 1)))
      oldCenter.c2
      delta

private theorem oldQuadraticFourthContribution_shift_c2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    (-(oldCenter.c2 + delta)) *
        openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
          timeBonds side sidePositive stage baseTime lag
          (shiftOldQuadraticCenter oldCenter delta) ≈
      (-oldCenter.c2) *
          openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
            timeBonds side sidePositive stage baseTime lag oldCenter +
        delta *
          ((-openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
              timeBonds side sidePositive stage baseTime lag oldCenter) +
            (-(oldCenter.c2 + delta)) *
              oldQuadraticFourthBracketC2ShiftCoefficient
                timeBonds side sidePositive stage baseTime lag oldCenter delta) := by
  let bracket :=
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  let shiftCoefficient := oldQuadraticFourthBracketC2ShiftCoefficient
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  have hbracket :=
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket_shift_c2
      timeBonds side sidePositive stage baseTime lag oldCenter delta
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (-(oldCenter.c2 + delta)) _ _ hbracket) ?_
  exact poly_identity_of_normal_eq
    (.mul
      (.neg (.add (.var 0) (.var 1)))
      (.add (.var 2) (.mul (.var 1) (.var 3))))
    (.add
      (.mul (.neg (.var 0)) (.var 2))
      (.mul (.var 1)
        (.add (.neg (.var 2))
          (.mul (.neg (.add (.var 0) (.var 1))) (.var 3)))))
    (by decide) (fun
      | 0 => oldCenter.c2
      | 1 => delta
      | 2 => bracket
      | _ => shiftCoefficient)

/-- Exact shift of the combined `(2/3)c2-c4` OLD-even contribution. -/
theorem openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison_shift_c2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuadraticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        delta *
          (heatActionTwoThird *
              openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
                timeBonds side sidePositive stage baseTime lag oldCenter +
            (heatActionTwoThird * (oldCenter.c2 + delta) - oldCenter.c4) *
              oldEvenBracketC2ShiftCoefficient
                timeBonds side sidePositive stage baseTime lag oldCenter delta) := by
  let bracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  let shiftCoefficient := oldEvenBracketC2ShiftCoefficient
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  have hbracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket_shift_c2
      timeBonds side sidePositive stage baseTime lag oldCenter delta
  unfold openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
    shiftOldQuadraticCenter
  dsimp only
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (heatActionTwoThird * (oldCenter.c2 + delta) - oldCenter.c4)
      _ _ hbracket) ?_
  exact poly_identity_of_normal_eq
    (.mul
      (.add
        (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.neg (.var 3)))
      (.add (.var 4) (.mul (.var 2) (.var 5))))
    (.add
      (.mul
        (.add (.mul (.var 0) (.var 1)) (.neg (.var 3)))
        (.var 4))
      (.mul (.var 2)
        (.add
          (.mul (.var 0) (.var 4))
          (.mul
            (.add
              (.mul (.var 0) (.add (.var 1) (.var 2)))
              (.neg (.var 3)))
            (.var 5)))))
    (by decide) (fun
      | 0 => heatActionTwoThird
      | 1 => oldCenter.c2
      | 2 => delta
      | 3 => oldCenter.c4
      | 4 => bracket
      | _ => shiftCoefficient)

/-- Exact cubic sensitivity of the residual-free neighboring frontier to the
supplied OLD quadratic center, factored by one copy of `delta`. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuadraticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        delta * oldQuadraticCenterShiftResponse
          timeBonds side sidePositive stage baseTime lag oldCenter delta := by
  let shifted := shiftOldQuadraticCenter oldCenter delta
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
  let oldFreeShift := oldFreeC2ShiftCoefficient
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  let fourthShift := oldQuadraticFourthBracketC2ShiftCoefficient
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  let cubicShift := oldCubicC2ShiftCoefficient
    timeBonds side sidePositive stage baseTime lag oldCenter
  let evenBracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  let evenShift := oldEvenBracketC2ShiftCoefficient
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  let evenContributionShift :=
    heatActionTwoThird * evenBracket +
      (heatActionTwoThird * (oldCenter.c2 + delta) - oldCenter.c4) * evenShift
  let fourthContributionShift :=
    (-fourthBracket) + (-(oldCenter.c2 + delta)) * fourthShift
  have hshift :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_oldCenter_decomposition
      timeBonds side sidePositive stage baseTime lag shifted
  have hold :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_oldCenter_decomposition
      timeBonds side sidePositive stage baseTime lag oldCenter
  have holdFree :=
    openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison_shift_c2
      timeBonds side sidePositive stage baseTime lag oldCenter delta
  have hfourth := oldQuadraticFourthContribution_shift_c2
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  have hcubic :=
    openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison_shift_c2
      timeBonds side sidePositive stage baseTime lag oldCenter delta
  have heven :=
    openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison_shift_c2
      timeBonds side sidePositive stage baseTime lag oldCenter delta
  unfold oldQuadraticCenterShiftResponse
  dsimp only
  change
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag shifted ≈
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        delta *
          (((oldFreeShift + fourthContributionShift) + cubicShift) +
            evenContributionShift)
  refine Q'.eqv_trans _ _ _ hshift ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          holdFree
          hfourth)
        hcubic)
      heven) ?_
  refine Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add
        (.add
          (.add
            (.add (.var 0) (.mul (.var 6) (.var 1)))
            (.add (.var 2) (.mul (.var 6) (.var 3))))
          (.add (.var 4) (.mul (.var 6) (.var 5))))
        (.add (.var 7) (.mul (.var 6) (.var 8))))
      (.add
        (.add
          (.add (.add (.var 0) (.var 2)) (.var 4))
          (.var 7))
        (.mul (.var 6)
          (.add
            (.add (.add (.var 1) (.var 3)) (.var 5))
            (.var 8))))
      (by decide) (fun
        | 0 => oldFree
        | 1 => oldFreeShift
        | 2 => (-oldCenter.c2) * fourthBracket
        | 3 => fourthContributionShift
        | 4 => cubic
        | 5 => cubicShift
        | 6 => delta
        | 7 => even
        | _ => evenContributionShift)) ?_
  exact Q'.add_eqv_congr_right _ _
    (delta * (((oldFreeShift + fourthContributionShift) + cubicShift) +
      evenContributionShift))
    (Q'.eqv_symm hold)

/-- Exact difference caused by changing only the supplied OLD quadratic
coefficient. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c2_sub
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag
          (shiftOldQuadraticCenter oldCenter delta) -
        openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter ≈
      delta * oldQuadraticCenterShiftResponse
        timeBonds side sidePositive stage baseTime lag oldCenter delta := by
  let frontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let payment := delta * oldQuadraticCenterShiftResponse
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  have hsensitivity :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c2
      timeBonds side sidePositive stage baseTime lag oldCenter delta
  change
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag
          (shiftOldQuadraticCenter oldCenter delta) - frontier ≈ payment
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hsensitivity (Q'.eqv_refl (-frontier))) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
    (.var 1) (by decide) (fun
      | 0 => frontier
      | _ => payment)

/-- Canonical absolute payment for the OLD quadratic-center mismatch. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c2_abs_le
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    Q'.abs
        (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
              timeBonds side sidePositive stage baseTime lag
              (shiftOldQuadraticCenter oldCenter delta) -
          openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
            timeBonds side sidePositive stage baseTime lag oldCenter) ≤
      Q'.abs delta *
        Q'.abs
          (oldQuadraticCenterShiftResponse
            timeBonds side sidePositive stage baseTime lag oldCenter delta) := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c2_sub
          timeBonds side sidePositive stage baseTime lag oldCenter delta))) ?_
  exact ExpNeg.abs_mul_le delta
    (oldQuadraticCenterShiftResponse
      timeBonds side sidePositive stage baseTime lag oldCenter delta)

/-- A base-center margin which pays both the quadratic-center mismatch and
the Heron approximation tail transfers to the actual shifted-center
numerator. -/
theorem openCubeHeatCayleyTraceP6NeighboringClearedComparison_shift_c2_lt_zero_of_margin
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta centerError epsilon : Q')
    (hepsilon : (0 : Q') < epsilon)
    (hcenter :
      Q'.abs delta *
          Q'.abs
            (oldQuadraticCenterShiftResponse
              timeBonds side sidePositive stage baseTime lag oldCenter delta) ≤
        centerError)
    (hstage :
      bulkSourceHeatP6NeighboringClearedAdaptiveStage
          timeBonds side sidePositive baseTime lag
          (shiftOldQuadraticCenter oldCenter delta) epsilon ≤ stage)
    (hmargin :
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
            timeBonds side sidePositive stage baseTime lag oldCenter +
          (centerError + epsilon) < 0) :
    openCubeHeatCayleyTraceP6NeighboringClearedComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuadraticCenter oldCenter delta) < 0 := by
  let baseFrontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let shiftedFrontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag
      (shiftOldQuadraticCenter oldCenter delta)
  have habsolute : Q'.abs (shiftedFrontier - baseFrontier) ≤ centerError :=
    Q'.le_trans' _ _ _
      (openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c2_abs_le
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
      (shiftOldQuadraticCenter oldCenter delta)
      epsilon hepsilon hstage hshiftedMargin

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison_shift_c2
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket_shift_c2
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison_shift_c2
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket_shift_c2
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison_shift_c2
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c2
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c2_abs_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticMismatchBudget.openCubeHeatCayleyTraceP6NeighboringClearedComparison_shift_c2_lt_zero_of_margin
