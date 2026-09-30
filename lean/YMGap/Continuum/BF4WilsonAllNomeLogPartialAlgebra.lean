/-
# Symmetry and positivity of finite regularized-log sums

Each finite logarithmic term is a nonnegative scalar multiple of a positive
time-defect power.  The mixed-moment identities make each term symmetric and
give a nonnegative quadratic form; finite addition preserves both properties
on the same all-nome Wilson completion.  No limit or generator is introduced.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogPartial

namespace YMGap.Continuum.BF4WilsonAllNomeLogPartialAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
open YMGap.Continuum.BF4WilsonAllNomeLogPartial

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "M" => mixedMoment hw0 hw1
local notation "v" => positiveTimeTail hw0 hw1
local notation "term" => logTerm hw0 hw1
local notation "tail" => logTail hw0 hw1
local notation "partial" => logPartial hw0 hw1

private theorem positiveTimeTail_symmetric (m : Nat) (x y : V) :
    B (v m x) y = B x (v m y) := by
  unfold positiveTimeTail
  calc
    B (defectPower hw0 hw1 m (T 1 x)) y =
        B (T 1 x) (defectPower hw0 hw1 m y) :=
      defectPower_symmetric hw0 hw1 m (T 1 x) y
    _ = B x (T 1 (defectPower hw0 hw1 m y)) :=
      completedInner_time_balance hw0 hw1 1 x (defectPower hw0 hw1 m y)
    _ = B x (defectPower hw0 hw1 m (T 1 y)) :=
      congrArg (B x) (time_defectPower hw0 hw1 m 1 y)

private theorem logTerm_symmetric (k : Nat) (x y : V) :
    B (term k x) y = B x (term k y) := by
  unfold logTerm
  rw [completedInner_smul_left, completedInner_smul_right]
  exact congrArg (RCscale (Q'.invSucc k))
    (positiveTimeTail_symmetric hw0 hw1 (k+1) x y)

private theorem logTerm_pairing_pin (k : Nat) (x : V) :
    B (term k x) x = RCscale (Q'.invSucc k) (M x 1 (k+1)) := by
  unfold logTerm
  rw [completedInner_smul_left, completedInner_symm]
  unfold positiveTimeTail mixedMoment
  exact congrArg (RCscale (Q'.invSucc k))
    (congrArg (B x) (time_defectPower hw0 hw1 (k+1) 1 x).symm)

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.zero_add' (A'.approx n))))

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

private theorem logTerm_nonnegative_pairing (k : Nat) (x : V) :
    RCnonneg (B (term k x) x) := by
  rw [logTerm_pairing_pin]
  exact rc_scale_nonnegative (Q'.invSucc_nonneg k)
    (mixedMoment_nonnegative hw0 hw1 x 1 (k+1))

private theorem logTail_symmetric (start len : Nat) (x y : V) :
    B (tail start len x) y = B x (tail start len y) := by
  induction len generalizing start with
  | zero =>
      change B Z y = B x Z
      rw [completedInner_zero_left, completedInner_symm,
        completedInner_zero_left]
  | succ len ih =>
      change B (A (term start x) (tail (start+1) len x)) y =
        B x (A (term start y) (tail (start+1) len y))
      rw [completedInner_add_left, completedInner_add_right,
        logTerm_symmetric, ih (start+1)]

private theorem logTail_nonnegative_pairing (start len : Nat) (x : V) :
    RCnonneg (B (tail start len x) x) := by
  induction len generalizing start with
  | zero =>
      change RCnonneg (B Z x)
      rw [completedInner_zero_left]
      exact RCle_refl RCzero
  | succ len ih =>
      change RCnonneg
        (B (A (term start x) (tail (start+1) len x)) x)
      rw [completedInner_add_left]
      exact rc_add_nonnegative (logTerm_nonnegative_pairing hw0 hw1 start x)
        (ih (start+1))

/-- Finite logarithmic partial sums are symmetric for the actual completed form. -/
theorem logPartial_symmetric (len : Nat) (x y : V) :
    B (partial len x) y = B x (partial len y) := by
  unfold logPartial
  exact logTail_symmetric hw0 hw1 0 len x y

/-- The finite logarithmic partial sum has nonnegative quadratic form. -/
theorem logPartial_nonnegative (len : Nat) (x : V) :
    RCnonneg (B (partial len x) x) := by
  unfold logPartial
  exact logTail_nonnegative_pairing hw0 hw1 0 len x

#print axioms logPartial_symmetric
#print axioms logPartial_nonnegative

end YMGap.Continuum.BF4WilsonAllNomeLogPartialAlgebra
