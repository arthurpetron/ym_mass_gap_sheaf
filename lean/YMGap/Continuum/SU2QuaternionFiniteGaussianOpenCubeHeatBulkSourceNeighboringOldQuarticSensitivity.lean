/-
# Neighboring residual-free sensitivity to the supplied OLD quartic center

The supplied OLD center is still arbitrary.  This leaf makes the resulting
obstruction to an unconditional neighboring sign theorem exact: changing only
`c4` by `delta` changes the residual-free cleared frontier by exactly

  `(-delta) * oldEvenBracket`.

If that bracket is strictly positive or strictly negative, an explicit
rational change of `c4` makes the residual-free frontier strictly positive.
Thus a negative margin cannot hold uniformly over every supplied OLD center
unless the quartic center is first identified or the bracket vanishes.  This
does not identify the ORIGINAL-law center, prove a sign for the bracket,
control higher remainders, construct a continuum Hamiltonian, or prove the
Clay mass gap.
-/

import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSensitivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringNonCommonOldCubicSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSplit
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuadraticRemainderSplit

local infix:50 " ≈ " => Q'.eqv

/-- Change only the supplied OLD quartic center. -/
def shiftOldQuarticCenter
    (oldCenter : CayleyTraceOldCenter) (delta : Q') : CayleyTraceOldCenter :=
  { c2 := oldCenter.c2
    c3 := oldCenter.c3
    c4 := oldCenter.c4 + delta }

private theorem lt_of_lt_of_le_local {a b c : Q'}
    (hab : a < b) (hbc : b ≤ c) : a < c := by
  have first : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have second : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := hbc
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have stepOne :
      (a.num * (c.den : Int)) * (b.den : Int) <
        (b.num * (a.den : Int)) * (c.den : Int) := by
    have scaled := Int.mul_lt_mul_of_pos_right first
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have reorder :
        (a.num * (b.den : Int)) * (c.den : Int) =
          (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [reorder] at scaled
  have stepTwo :
      (b.num * (a.den : Int)) * (c.den : Int) ≤
        (c.num * (a.den : Int)) * (b.den : Int) := by
    have scaled := Int.mul_le_mul_of_nonneg_right second
      (by exact_mod_cast Nat.le_of_lt a.den_pos : (0 : Int) ≤ (a.den : Int))
    have reorderLeft :
        (b.num * (c.den : Int)) * (a.den : Int) =
          (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (c.den : Int) (a.den : Int)]
    have reorderRight :
        (c.num * (b.den : Int)) * (a.den : Int) =
          (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [reorderLeft, reorderRight] at scaled
    exact scaled
  have strictScaled :
      (a.num * (c.den : Int)) * (b.den : Int) <
        (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le stepOne stepTwo
  exact Int.lt_of_mul_lt_mul_right strictScaled
    (by exact_mod_cast Nat.le_of_lt b.den_pos : (0 : Int) ≤ (b.den : Int))

private theorem neg_pos_of_neg_local {value : Q'}
    (hvalue : value < (0 : Q')) : (0 : Q') < -value := by
  have hnum : value.num < 0 := by
    have hcross : value.num * (1 : Int) <
        (0 : Int) * (value.den : Int) := hvalue
    omega
  show (0 : Int) * ((-value).den : Int) < (-value).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  change (0 : Int) < -value.num
  omega

private theorem value_add_abs_add_one_pos (value : Q') :
    (0 : Q') < value + (Q'.abs value + 1) := by
  have hnonnegative : (0 : Q') ≤ value + Q'.abs value := by
    have hsum :
        (-Q'.abs value) + Q'.abs value ≤
          value + Q'.abs value :=
      Q'.add_le_add_right _ _ _ (ExpNeg.neg_abs_le value)
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_add_self_eqv (Q'.abs value))) hsum
  have hpositive :
      (0 : Q') < 1 + (value + Q'.abs value) :=
    Q'.pos_add_nonneg (by decide) hnonnegative
  refine lt_of_lt_of_le_local hpositive (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq
    (.add (.const 1) (.add (.var 0) (.var 1)))
    (.add (.var 0) (.add (.var 1) (.const 1)))
    (by decide) (fun
      | 0 => value
      | _ => Q'.abs value)

private theorem oldFreeComparison_shift_invariant
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuarticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  exact Q'.eqv_refl _

private theorem oldQuadraticFourthBracket_shift_invariant
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuarticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  exact Q'.eqv_refl _

private theorem oldCubicComparison_shift_invariant
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuarticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  exact Q'.eqv_refl _

private theorem oldEvenBracket_shift_invariant
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuarticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
        timeBonds side sidePositive stage baseTime lag oldCenter := by
  exact Q'.eqv_refl _

private theorem combinedOldEvenComparison_shift
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuarticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        (-delta) *
          openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
            timeBonds side sidePositive stage baseTime lag oldCenter := by
  let bracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  unfold openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
    shiftOldQuarticCenter
  change
    (heatActionTwoThird * oldCenter.c2 - (oldCenter.c4 + delta)) * bracket ≈
      (heatActionTwoThird * oldCenter.c2 - oldCenter.c4) * bracket +
        (-delta) * bracket
  exact poly_identity_of_normal_eq
    (.mul
      (.add (.mul (.var 0) (.var 1))
        (.neg (.add (.var 2) (.var 3))))
      (.var 4))
    (.add
      (.mul
        (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))
        (.var 4))
      (.mul (.neg (.var 3)) (.var 4)))
    (by decide) (fun
      | 0 => heatActionTwoThird
      | 1 => oldCenter.c2
      | 2 => oldCenter.c4
      | 3 => delta
      | _ => bracket)

/-- Exact affine sensitivity of the residual-free neighboring frontier to the
still-arbitrary supplied OLD quartic center. -/
theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (delta : Q') :
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag
        (shiftOldQuarticCenter oldCenter delta) ≈
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        (-delta) *
          openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
            timeBonds side sidePositive stage baseTime lag oldCenter := by
  let shifted := shiftOldQuarticCenter oldCenter delta
  let oldFree :=
    openCubeHeatCayleyTraceP6NeighboringWithOldFreeP6RemainderClearedComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let fourthBracket :=
    openCubeHeatCayleyTraceP6NeighboringOldQuadraticFourthReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  let cubic := openCubeHeatCayleyTraceP6NeighboringOldCubicReducedComparison
    timeBonds side sidePositive stage baseTime lag oldCenter
  let evenBracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  let combined :=
    openCubeHeatCayleyTraceP6NeighboringCombinedOldEvenCenterComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
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
  have hcubic := oldCubicComparison_shift_invariant
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  have hcombined := combinedOldEvenComparison_shift
    timeBonds side sidePositive stage baseTime lag oldCenter delta
  change
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag shifted ≈
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag oldCenter +
        (-delta) * evenBracket
  refine Q'.eqv_trans _ _ _ hshift ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          holdFree
          (Q'.mul_eqv_congr_left (-oldCenter.c2) _ _ hfourth))
        hcubic)
      hcombined) ?_
  refine Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add
        (.add
          (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
          (.var 3))
        (.add (.var 4) (.mul (.neg (.var 5)) (.var 6))))
      (.add
        (.add
          (.add
            (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
            (.var 3))
          (.var 4))
        (.mul (.neg (.var 5)) (.var 6)))
      (by decide) (fun
        | 0 => oldFree
        | 1 => oldCenter.c2
        | 2 => fourthBracket
        | 3 => cubic
        | 4 => combined
        | 5 => delta
        | _ => evenBracket)) ?_
  exact Q'.add_eqv_congr_right _ _ ((-delta) * evenBracket)
    (Q'.eqv_symm hold)

/-- Explicit change of the arbitrary OLD quartic center which forces a
positive residual-free frontier when the OLD-even bracket is positive. -/
def positiveFrontierQuarticCenterOfPositiveBracket
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (hbracket : (0 : Q') <
      openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
        timeBonds side sidePositive stage baseTime lag oldCenter) :
    CayleyTraceOldCenter :=
  let frontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let bracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  shiftOldQuarticCenter oldCenter
    (-Q'.divPos (Q'.abs frontier + 1) bracket hbracket)

theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_positive_of_positiveOldEvenBracket
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (hbracket : (0 : Q') <
      openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
        timeBonds side sidePositive stage baseTime lag oldCenter) :
    (0 : Q') <
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag
        (positiveFrontierQuarticCenterOfPositiveBracket
          timeBonds side sidePositive stage baseTime lag oldCenter hbracket) := by
  let frontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let bracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  let quotient := Q'.divPos (Q'.abs frontier + 1) bracket hbracket
  have hsensitivity :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4
      timeBonds side sidePositive stage baseTime lag oldCenter (-quotient)
  have hvalue :
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag
          (shiftOldQuarticCenter oldCenter (-quotient)) ≈
        frontier + (Q'.abs frontier + 1) := by
    refine Q'.eqv_trans _ _ _ hsensitivity ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left frontier _ _
        (poly_identity_of_normal_eq
          (.mul (.neg (.neg (.var 0))) (.var 1))
          (.mul (.var 0) (.var 1))
          (by decide) (fun
            | 0 => quotient
            | _ => bracket))) ?_
    exact Q'.add_eqv_congr_left frontier _ _
      (Q'.divPos_mul_eqv (Q'.abs frontier + 1) bracket hbracket)
  unfold positiveFrontierQuarticCenterOfPositiveBracket
  change (0 : Q') <
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag
      (shiftOldQuarticCenter oldCenter (-quotient))
  exact lt_of_lt_of_le_local (value_add_abs_add_one_pos frontier)
    (Q'.ge_of_eqv hvalue)

/-- Explicit change of the arbitrary OLD quartic center which forces a
positive residual-free frontier when the OLD-even bracket is negative. -/
def positiveFrontierQuarticCenterOfNegativeBracket
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (hbracket :
      openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
        timeBonds side sidePositive stage baseTime lag oldCenter < 0) :
    CayleyTraceOldCenter :=
  let frontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let bracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  shiftOldQuarticCenter oldCenter
    (Q'.divPos (Q'.abs frontier + 1) (-bracket)
      (neg_pos_of_neg_local hbracket))

theorem openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_positive_of_negativeOldEvenBracket
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage baseTime lag : Nat) (oldCenter : CayleyTraceOldCenter)
    (hbracket :
      openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
        timeBonds side sidePositive stage baseTime lag oldCenter < 0) :
    (0 : Q') <
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
        timeBonds side sidePositive stage baseTime lag
        (positiveFrontierQuarticCenterOfNegativeBracket
          timeBonds side sidePositive stage baseTime lag oldCenter hbracket) := by
  let frontier :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag oldCenter
  let bracket :=
    openCubeHeatCayleyTraceP6NeighboringOldEvenCenterReducedBracket
      timeBonds side sidePositive stage baseTime lag oldCenter
  have hnegative : (0 : Q') < -bracket := neg_pos_of_neg_local hbracket
  let quotient := Q'.divPos (Q'.abs frontier + 1) (-bracket) hnegative
  have hsensitivity :=
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4
      timeBonds side sidePositive stage baseTime lag oldCenter quotient
  have hvalue :
      openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
          timeBonds side sidePositive stage baseTime lag
          (shiftOldQuarticCenter oldCenter quotient) ≈
        frontier + (Q'.abs frontier + 1) := by
    refine Q'.eqv_trans _ _ _ hsensitivity ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left frontier _ _
        (poly_identity_of_normal_eq
          (.mul (.neg (.var 0)) (.var 1))
          (.mul (.var 0) (.neg (.var 1)))
          (by decide) (fun
            | 0 => quotient
            | _ => bracket))) ?_
    exact Q'.add_eqv_congr_left frontier _ _
      (Q'.divPos_mul_eqv (Q'.abs frontier + 1) (-bracket) hnegative)
  unfold positiveFrontierQuarticCenterOfNegativeBracket
  change (0 : Q') <
    openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
      timeBonds side sidePositive stage baseTime lag
      (shiftOldQuarticCenter oldCenter quotient)
  exact lt_of_lt_of_le_local (value_add_abs_add_one_pos frontier)
    (Q'.ge_of_eqv hvalue)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSensitivity

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSensitivity.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_shift_c4
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSensitivity.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_positive_of_positiveOldEvenBracket
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringOldQuarticSensitivity.openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison_positive_of_negativeOldEvenBracket
