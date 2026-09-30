/-
Algebraic and contractive laws for the constructed positive-time action on
the original all-nome Wilson completion. These laws use its witnessed
dyadic rows, not a legacy transfer carrier or a new analytic assumption.
-/

import YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
import YMGap.Continuum.BF4WilsonAllNomeLogOperator
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeLogOperator (pairing_limits_eq)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "F" => positiveAction hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

variable (time : PositiveRealDyadicTimeData.PositiveTime)

/-- Symmetry is the represented limit of the actual dyadic symmetries. -/
theorem positiveAction_symmetric (x y : V) :
    B (F time x) y = B x (F time y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := pairing_limits_eq hw0 hw1
    (timeRows hw0 hw1 time X) (constantRows hw0 hw1 Y)
    (constantRows hw0 hw1 X) (timeRows hw0 hw1 time Y) (fun n => by
      rw [timeRows_pin, constantRows_point, constantRows_point, timeRows_pin]
      exact BF4WilsonAllNomeDyadicSemigroup.action_symmetric hw0 hw1
        (NonnegativeDyadicTime.embed (PositiveRealDyadicTimeData.approximation time n))
        (Class X) (Class Y))
  rw [limit_constantRows, limit_constantRows] at h
  rw [positiveAction_pin hw0 hw1 time X, positiveAction_pin hw0 hw1 time Y]
  exact h

/-- Positive finite dyadic forms pass to the same represented limit. -/
theorem positiveAction_nonnegative (x : V) : RCnonneg (B x (F time x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [positiveAction_pin hw0 hw1 time X]
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let R := constantRows hw0 hw1 X
  let S := timeRows hw0 hw1 time X
  let n := pairingModulus hw0 hw1 R S epsilon
  have h := (row_pairing_bound hw0 hw1 R S epsilon he n (Nat.le_refl n)).1
  change RCle (B (rowPoint hw0 hw1 (constantRows hw0 hw1 X) n)
    (rowPoint hw0 hw1 (timeRows hw0 hw1 time X) n))
      (RCadd (B (limit hw0 hw1 (constantRows hw0 hw1 X))
        (limit hw0 hw1 (timeRows hw0 hw1 time X))) (Rq epsilon)) at h
  rw [constantRows_point, timeRows_pin, limit_constantRows] at h
  have hp := BF4WilsonAllNomeDyadicSemigroup.action_nonnegative hw0 hw1
    (NonnegativeDyadicTime.embed (PositiveRealDyadicTimeData.approximation time n))
    (Class X)
  rw [completedInner_symm hw0 hw1
    (BF4WilsonAllNomeDyadicSemigroup.action hw0 hw1
      (NonnegativeDyadicTime.embed (PositiveRealDyadicTimeData.approximation time n))
      (Class X)) (Class X)] at hp
  exact RCle_trans hp h

/-- The original norm remains a uniform bound for every positive time. -/
theorem positiveAction_norm_bound (x : V) :
    RCle (B (F time x) (F time x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [positiveAction_pin hw0 hw1 time X]
  apply rowLimit_norm_bound hw0 hw1
  intro n
  rw [timeRows_pin]
  exact BF4WilsonAllNomeDyadicSemigroup.action_norm_bound hw0 hw1
    (NonnegativeDyadicTime.embed (PositiveRealDyadicTimeData.approximation time n))
    (Class X)

theorem positiveAction_add (x y : V) :
    F time (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (F time x) (F time y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [positiveAction_symmetric, completedInner_add_left, completedInner_add_left,
    positiveAction_symmetric, positiveAction_symmetric]

theorem positiveAction_smul (c : Q') (x : V) :
    F time (completedSmul hw0 hw1 c x) =
      completedSmul hw0 hw1 c (F time x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [positiveAction_symmetric, completedInner_smul_left, completedInner_smul_left,
    positiveAction_symmetric]

theorem positiveAction_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    F time (completedRealSmul hw0 hw1 s cs x) =
      completedRealSmul hw0 hw1 s cs (F time x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [positiveAction_symmetric, completedInner_realSmul_left,
    completedInner_realSmul_left, positiveAction_symmetric]

theorem positiveAction_sub (x y : V) :
    F time (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1 (F time x) (F time y) := by
  unfold completedSub completedNeg
  rw [positiveAction_add, positiveAction_smul]

theorem positiveAction_distance_bound (x y : V) :
    RCle (completedDist hw0 hw1 (F time x) (F time y))
      (completedDist hw0 hw1 x y) := by
  unfold completedDist
  rw [← positiveAction_sub]
  exact positiveAction_norm_bound hw0 hw1 time (completedSub hw0 hw1 x y)

#print axioms positiveAction_symmetric
#print axioms positiveAction_nonnegative
#print axioms positiveAction_norm_bound
#print axioms positiveAction_add
#print axioms positiveAction_smul
#print axioms positiveAction_realSmul
#print axioms positiveAction_sub
#print axioms positiveAction_distance_bound

end YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
