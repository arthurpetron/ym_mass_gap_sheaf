/-
# Exact laws for finite regularized-log partial sums

The finite logarithmic polynomials commute with the original completed time
semigroup and vanish on its one-step kernel.  The unit is also annihilated.
These are algebraic statements on the same fixed-width all-nome completion;
they assert neither convergence of the logarithm nor a generator theorem.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogPartial

namespace YMGap.Continuum.BF4WilsonAllNomeLogPartialLaws

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
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "v" => positiveTimeTail hw0 hw1
local notation "term" => logTerm hw0 hw1
local notation "tail" => logTail hw0 hw1
local notation "partial" => logPartial hw0 hw1

private theorem time_one_commutes_time (n : Nat) (x : V) :
    T 1 (T n x) = T n (T 1 x) := by
  calc
    T 1 (T n x) = T (1+n) x := (completedTime_add hw0 hw1 1 n x).symm
    _ = T (n+1) x := congrArg (fun k => T k x) (by omega)
    _ = T n (T 1 x) := completedTime_add hw0 hw1 n 1 x

private theorem positiveTimeTail_commutes_time (m n : Nat) (x : V) :
    v m (T n x) = T n (v m x) := by
  unfold positiveTimeTail
  rw [time_one_commutes_time]
  exact (time_defectPower hw0 hw1 m n (T 1 x)).symm

private theorem logTerm_commutes_time (k n : Nat) (x : V) :
    term k (T n x) = T n (term k x) := by
  unfold logTerm
  rw [completedTime_smul, ← positiveTimeTail_commutes_time]

private theorem logTail_commutes_time (start len n : Nat) (x : V) :
    tail start len (T n x) = T n (tail start len x) := by
  induction len generalizing start with
  | zero =>
      exact (completedTime_zero_element hw0 hw1 n).symm
  | succ len ih =>
      change A (term start (T n x)) (tail (start+1) len (T n x)) =
        T n (A (term start x) (tail (start+1) len x))
      rw [logTerm_commutes_time, ih, completedTime_additive]

/-- Every finite regularized-log partial sum commutes with original time. -/
theorem logPartial_commutes_time (len n : Nat) (x : V) :
    partial len (T n x) = T n (partial len x) := by
  unfold logPartial
  exact logTail_commutes_time hw0 hw1 0 len n x

private theorem defect_zero : defect hw0 hw1 (Z) = Z := by
  unfold defect
  rw [completedTime_zero_element]
  exact completedSub_self hw0 hw1 Z

private theorem defectPower_zero (n : Nat) :
    defectPower hw0 hw1 n (Z) = Z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change defect hw0 hw1 (defectPower hw0 hw1 n Z) = Z
      rw [ih, defect_zero]

private theorem positiveTimeTail_zero_of_time_one_zero (m : Nat) (x : V)
    (hx : T 1 x = Z) : v m x = Z := by
  unfold positiveTimeTail
  rw [hx, defectPower_zero]

private theorem smul_zero_element (c : Q') : S c Z = Z := by
  have hc : Q'.eqv (c * 0) 0 :=
    YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
      (.mul (.var 0) (.const 0)) (.const 0) (by decide) (fun _ => c)
  calc
    S c Z = S c (S 0 Z) := congrArg (S c) (completedSmul_zero hw0 hw1 Z).symm
    _ = S (c*0) Z := completedSmul_mul hw0 hw1 c 0 Z
    _ = S 0 Z := completedSmul_congr hw0 hw1 hc Z
    _ = Z := completedSmul_zero hw0 hw1 Z

private theorem logTerm_zero_of_time_one_zero (k : Nat) (x : V)
    (hx : T 1 x = Z) : term k x = Z := by
  unfold logTerm
  rw [positiveTimeTail_zero_of_time_one_zero hw0 hw1 (k+1) x hx,
    smul_zero_element]

private theorem logTail_zero_of_time_one_zero (start len : Nat) (x : V)
    (hx : T 1 x = Z) : tail start len x = Z := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
      change A (term start x) (tail (start+1) len x) = Z
      rw [logTerm_zero_of_time_one_zero hw0 hw1 start x hx, ih (start+1),
        completedZero_add]

/-- A finite log polynomial kills vectors killed by one original time step. -/
theorem logPartial_kernel_zero (len : Nat) (x : V)
    (hx : T 1 x = Z) : partial len x = Z := by
  unfold logPartial
  exact logTail_zero_of_time_one_zero hw0 hw1 0 len x hx

private theorem defect_unit_zero :
    defect hw0 hw1 (unitState hw0 hw1 width) = Z := by
  unfold defect
  rw [completedUnit_fixed]
  exact completedSub_self hw0 hw1 (unitState hw0 hw1 width)

private theorem defectPower_succ_unit_zero (n : Nat) :
    defectPower hw0 hw1 (n+1) (unitState hw0 hw1 width) = Z := by
  induction n with
  | zero =>
      change defect hw0 hw1 (unitState hw0 hw1 width) = Z
      exact defect_unit_zero hw0 hw1
  | succ n ih =>
      change defect hw0 hw1 (defectPower hw0 hw1 (n+1)
        (unitState hw0 hw1 width)) = Z
      rw [ih, defect_zero]

private theorem positiveTimeTail_unit_zero (n : Nat) :
    v (n+1) (unitState hw0 hw1 width) = Z := by
  unfold positiveTimeTail
  rw [completedUnit_fixed]
  exact defectPower_succ_unit_zero hw0 hw1 n

private theorem logTerm_unit_zero (n : Nat) :
    term n (unitState hw0 hw1 width) = Z := by
  unfold logTerm
  rw [positiveTimeTail_unit_zero, smul_zero_element]

private theorem logTail_unit_zero (start len : Nat) :
    tail start len (unitState hw0 hw1 width) = Z := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
      change A (term start (unitState hw0 hw1 width))
        (tail (start+1) len (unitState hw0 hw1 width)) = Z
      rw [logTerm_unit_zero, ih, completedZero_add]

/-- The finite regularized logarithm annihilates the actual fixed unit. -/
theorem logPartial_unit_zero (len : Nat) :
    partial len (unitState hw0 hw1 width) = Z := by
  unfold logPartial
  exact logTail_unit_zero hw0 hw1 0 len

#print axioms logPartial_commutes_time
#print axioms logPartial_kernel_zero
#print axioms logPartial_unit_zero

end YMGap.Continuum.BF4WilsonAllNomeLogPartialLaws
