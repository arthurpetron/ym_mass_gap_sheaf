/-
# Constructive range approximation AFTER original positive time

The explicit finite polynomial u_n=sum_{j<n}(I-T)^j x satisfies
T^2 u_n + (I-T)^n T x = T x on the SAME Wilson completion.
The proved tail bound controls the squared approximation error by
||x||^2/(n+1)^2, with a supplied rational tolerance computing n.

This approximates T x by actual T^2-images without selecting a preimage,
assuming full-carrier injectivity, discarding a positive-norm state, or
identifying different spatial widths. Density in the entire carrier,
continuous-time reconstruction, and scaling survival are NOT asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
import YMGap.Continuum.BF4WilsonAllNomeLinearLaws
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime

namespace YMGap.Continuum.BF4WilsonAllNomePositiveTimeRange

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "Z" => completedZero hw0 hw1 width

/-- Finite rational polynomial in the actual transfer, with x supplied. -/
def inverseSum : Nat → V → V
  | 0, _ => Z
  | n+1, x => A (inverseSum n x) (defectPower hw0 hw1 n x)

theorem inverseSum_identity (n : Nat) (x : V) :
    A (T 1 (inverseSum hw0 hw1 n x)) (defectPower hw0 hw1 n x) = x := by
  induction n with
  | zero =>
      change A (T 1 Z) x = x
      rw [completedTime_zero_element, completedZero_add]
  | succ n ih =>
      change A (T 1 (A (inverseSum hw0 hw1 n x) (defectPower hw0 hw1 n x)))
        (defect hw0 hw1 (defectPower hw0 hw1 n x)) = x
      rw [completedTime_additive, completedAdd_assoc, time_add_defect]
      exact ih

/-- Exact original-time identity; the error is an explicit original vector. -/
theorem inverseSum_twoStep_identity (n : Nat) (x : V) :
    A (T 2 (inverseSum hw0 hw1 n x)) (positiveTimeTail hw0 hw1 n x) = T 1 x := by
  have h := congrArg (T 1) (inverseSum_identity hw0 hw1 n x)
  rw [completedTime_additive, ← completedTime_add, time_defectPower] at h
  exact h

private theorem add_sub_cancel (x y : V) : completedSub hw0 hw1 (A x y) x = y := by
  unfold completedSub
  rw [completedAdd_comm hw0 hw1 x y, completedAdd_assoc,
    completedAdd_comm hw0 hw1 x, completedNeg_add, completedAdd_zero]

theorem inverseSum_error_pin (n : Nat) (x : V) :
    completedSub hw0 hw1 (T 1 x) (T 2 (inverseSum hw0 hw1 n x)) =
      positiveTimeTail hw0 hw1 n x := by
  rw [← inverseSum_twoStep_identity hw0 hw1 n x, add_sub_cancel]

theorem inverseSum_error_bound (n : Nat) (x : V) :
    let error := completedSub hw0 hw1 (T 1 x) (T 2 (inverseSum hw0 hw1 n x))
    RCle (B error error) (RCscale (Q'.invSucc n * Q'.invSucc n) (B x x)) := by
  dsimp only
  rw [inverseSum_error_pin]
  exact positiveTimeTail_bound hw0 hw1 n x

/-- The polynomial witness is returned as data, with a relative squared-error
bound. No representative or preimage is extracted from an existential. -/
def positiveTimeRangeApproximation (epsilon : Q') (he : (0 : Q') < epsilon) (x : V) :
    {y : V //
      let error := completedSub hw0 hw1 (T 1 x) (T 2 y)
      RCle (B error error) (RCscale epsilon (B x x))} :=
  ⟨inverseSum hw0 hw1 (relativeTailModulus epsilon) x, by
    dsimp only
    rw [inverseSum_error_pin]
    exact positiveTimeTail_small hw0 hw1 epsilon he (relativeTailModulus epsilon)
      (Nat.le_refl _) x⟩

#print axioms inverseSum
#print axioms inverseSum_identity
#print axioms inverseSum_twoStep_identity
#print axioms inverseSum_error_pin
#print axioms inverseSum_error_bound
#print axioms positiveTimeRangeApproximation

end YMGap.Continuum.BF4WilsonAllNomePositiveTimeRange
