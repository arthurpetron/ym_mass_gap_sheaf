/-
# Positivity of the regularized logarithm on the original positive-time range

Each finite regularized term paired with the actual one-step time image is
a positive mixed moment.  Quantitative represented-row pairing continuity
passes that sign to the existing regularized-log limit on the SAME
all-nome Wilson completion.  This does not define an unbounded generator
or discard the original boundary kernel.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogOperator

namespace YMGap.Continuum.BF4WilsonAllNomeLogRangePositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
open YMGap.Continuum.BF4WilsonAllNomeLogPartial
open YMGap.Continuum.BF4WilsonAllNomeLogSeries
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "M" => mixedMoment hw0 hw1
local notation "term" => logTerm hw0 hw1
local notation "tail" => logTail hw0 hw1
local notation "partial" => logPartial hw0 hw1
local notation "F" => regularizedLog hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "Rq" => fun q : Q' => Quotient.mk crealSetoid (ofQ' q)

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro a'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.zero_add' (a'.approx n))))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro a'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    QPoly.q_add_zero_eqv (a'.approx n)))

private theorem rc_le_add_nonnegative (a b : RC) (hb : RCnonneg b) :
    RCle a (RCadd a b) := by
  have h := RCadd_le_add (RCle_refl a) hb
  rwa [rc_add_zero] at h

private theorem rc_add_nonnegative {a b : RC}
    (ha : RCnonneg a) (hb : RCnonneg b) : RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  rw [rc_zero_add] at h
  exact h

private theorem rc_scale_nonnegative {c : Q'} (hc : (0 : Q') ≤ c)
    {a : RC} (ha : RCnonneg a) : RCnonneg (RCscale c a) := by
  have h := RCscale_mono hc ha
  rw [RCscale_RCzero] at h
  exact h

private theorem logTerm_time_pairing_pin (k : Nat) (x : V) :
    B (T 1 x) (term k x) = RCscale (Q'.invSucc k) (M x 2 (k+1)) := by
  unfold logTerm positiveTimeTail mixedMoment
  rw [completedInner_smul_right]
  apply congrArg (RCscale (Q'.invSucc k))
  calc
    B (T 1 x) (defectPower hw0 hw1 (k+1) (T 1 x)) =
        B x (T 1 (defectPower hw0 hw1 (k+1) (T 1 x))) :=
      completedInner_time_balance hw0 hw1 1 x _
    _ = B x (defectPower hw0 hw1 (k+1) (T 1 (T 1 x))) :=
      congrArg (B x) (time_defectPower hw0 hw1 (k+1) 1 (T 1 x))
    _ = B x (defectPower hw0 hw1 (k+1) (T 2 x)) := by
      rw [completedTime_add hw0 hw1 1 1 x]
    _ = B x (T 2 (defectPower hw0 hw1 (k+1) x)) :=
      congrArg (B x) (time_defectPower hw0 hw1 (k+1) 2 x).symm

private theorem logTerm_time_nonnegative (k : Nat) (x : V) :
    RCnonneg (B (T 1 x) (term k x)) := by
  rw [logTerm_time_pairing_pin]
  exact rc_scale_nonnegative (Q'.invSucc_nonneg k)
    (mixedMoment_nonnegative hw0 hw1 x 2 (k+1))

private theorem logTail_time_nonnegative (start len : Nat) (x : V) :
    RCnonneg (B (T 1 x) (tail start len x)) := by
  induction len generalizing start with
  | zero =>
      change RCnonneg (B (T 1 x) Z)
      rw [completedInner_zero_right]
      exact RCle_refl RCzero
  | succ len ih =>
      change RCnonneg
        (B (T 1 x) (A (term start x) (tail (start+1) len x)))
      rw [completedInner_add_right]
      exact rc_add_nonnegative (logTerm_time_nonnegative hw0 hw1 start x)
        (ih (start+1))

/-- Every finite regularized-log sum has positive pairing with the actual
one-step image of its input. -/
theorem logPartial_time_nonnegative (len : Nat) (x : V) :
    RCnonneg (B (T 1 x) (partial len x)) := by
  unfold logPartial
  exact logTail_time_nonnegative hw0 hw1 0 len x

/-- The first finite log summand is the one-step defect of the time image;
all subsequent mixed-moment pairings are nonnegative. -/
theorem logPartial_time_firstTerm_le (len : Nat) (x : V) :
    RCle (B (T 1 x) (defect hw0 hw1 (T 1 x)))
      (B (T 1 x) (partial (len+1) x)) := by
  change RCle _ (B (T 1 x) (A (term 0 x) (tail 1 len x)))
  rw [completedInner_add_right]
  have hhead : B (T 1 x) (term 0 x) =
      B (T 1 x) (defect hw0 hw1 (T 1 x)) := by
    unfold logTerm positiveTimeTail
    rw [completedInner_smul_right]
    change RCscale (Q'.invSucc 0)
      (B (T 1 x) (defect hw0 hw1 (T 1 x))) = _
    rw [RCSignedPairBudget.scale_congr
      (by decide : Q'.eqv (Q'.invSucc 0) 1), RCscale_one]
  rw [hhead]
  exact rc_le_add_nonnegative _ _ (logTail_time_nonnegative hw0 hw1 1 len x)

/-- The actual computed regularized-log limit remains positive on the
original one-step time image. This is the quadratic form needed for a
witnessed range graph, not a full-carrier generator construction. -/
theorem regularizedLog_time_nonnegative (x : V) :
    RCnonneg (B (T 1 x) (F x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  let TX := (timeNonexpansive hw0 hw1 1).mapCauchy X
  let R := constantRows hw0 hw1 TX
  let S := logRows hw0 hw1 X
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := pairingModulus hw0 hw1 R S epsilon
  have h := (row_pairing_bound hw0 hw1 R S epsilon he n (Nat.le_refl n)).1
  change RCle (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n))
    (RCadd (B (limit hw0 hw1 R) (limit hw0 hw1 S)) (Rq epsilon)) at h
  rw [constantRows_point, logRows_point, limit_constantRows] at h
  have hp := logPartial_time_nonnegative hw0 hw1 n (Class X)
  exact RCle_trans hp h

/-- The original positive-time range retains its first defect pairing in
the represented regularized-log limit. The boundary kernel is untouched. -/
theorem regularizedLog_time_firstTerm_le (x : V) :
    RCle (B (T 1 x) (defect hw0 hw1 (T 1 x))) (B (T 1 x) (F x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  let TX := (timeNonexpansive hw0 hw1 1).mapCauchy X
  let R := constantRows hw0 hw1 TX
  let S := logRows hw0 hw1 X
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let m := pairingModulus hw0 hw1 R S epsilon
  let n := m+1
  have h := (row_pairing_bound hw0 hw1 R S epsilon he n
    (Nat.le_add_right m 1)).1
  change RCle (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n))
    (RCadd (B (limit hw0 hw1 R) (limit hw0 hw1 S)) (Rq epsilon)) at h
  rw [constantRows_point, logRows_point, limit_constantRows] at h
  have hp := logPartial_time_firstTerm_le hw0 hw1 m (Class X)
  change RCle (B (T 1 (Class X)) (defect hw0 hw1 (T 1 (Class X))))
    (B (T 1 (Class X)) (logPartial hw0 hw1 n (Class X))) at hp
  exact RCle_trans hp h

#print axioms logPartial_time_nonnegative
#print axioms regularizedLog_time_nonnegative
#print axioms logPartial_time_firstTerm_le
#print axioms regularizedLog_time_firstTerm_le

end YMGap.Continuum.BF4WilsonAllNomeLogRangePositive
