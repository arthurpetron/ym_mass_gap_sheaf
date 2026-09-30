/-
# Positive time cannot recover the original boundary fluctuation

Every strictly positive real-time action annihilates the original T(1)
kernel: its output is in the witnessed range and still in that kernel.
For the width-one centered origin plaquette, the vacuum-created centered
insertion is therefore zero at EVERY positive time, while its original
equal-time variance has the positive floor starRatio(w).

This is an exact quantitative failure of recovering that boundary source
by taking insertion time down to zero. It is not a no-go result for bulk
sources, a controlled spatial limit, or Yang--Mills reconstruction.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorExcitation
import YMGap.Continuum.BF4WilsonAllNomeSectorObservableBoundary
import YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup

namespace YMGap.Continuum.BF4WilsonAllNomeSectorEqualTimeBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedInner_zero_left)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (dist_zero_right)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws (positiveAction_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
  (realTimeAction_pin positiveAction_original)
open YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup (realTimeAction_commutes)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue dyadicTime)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure (positiveAction_range)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (kernel_zero)
open YMGap.Continuum.BF4WilsonAllNomeSectorObservableBoundary (originLoop originCentered)
open YMGap.Continuum.BF4WilsonAllNomeSectorExcitation (centeredSource)
open YMGap.Continuum.BF4WilsonAllNomeFringeTimeKernel (originPlaquette_time_one_zero)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
  (originFace originFace_mem plaquetteExcitation_norm_floor plaquetteExcitation_norm_ne_zero)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "F" => positiveAction hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "v" => originCentered hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem positiveAction_zero (time : PositiveTime) : F time Z = Z := by
  apply (BF4WilsonAllNomeGeometry.completedInner_posdef hw0 hw1 width (F time Z)).mp
  have h := positiveAction_norm_bound hw0 hw1 time Z
  rw [completedInner_zero_left] at h
  exact RCle_antisymm h (completedInner_nonnegative hw0 hw1 (F time Z))

theorem positiveAction_time_one_commutes (time : PositiveTime) (x : V) :
    F time (T 1 x) = T 1 (F time x) := by
  have h := realTimeAction_commutes hw0 hw1 (timeValue time)
    (timeValue (dyadicTime ⟨0,1⟩ (Nat.succ_pos 0))) x
  simpa only [realTimeAction_pin,positiveAction_original] using h

/-- Range membership is constructed from a supplied representative after
quotient induction into this proposition; no representative is selected. -/
theorem positiveAction_kills_time_kernel (time : PositiveTime) (x : V)
    (hx : T 1 x = Z) : F time x = Z := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro X hx
  apply kernel_zero hw0 hw1 (positiveAction_range hw0 hw1 time X)
  rw [← positiveAction_time_one_commutes, hx, positiveAction_zero]

/-- The centered vacuum-created insertion vanishes at every positive time,
not just at original integer times. -/
theorem origin_centeredSource_zero (time : PositiveTime) :
    (centeredSource hw0 hw1 time originLoop).val = completedZero hw0 hw1 1 :=
  positiveAction_kills_time_kernel hw0 hw1 time v (originPlaquette_time_one_zero hw0 hw1)

/-- The original positive equal-time variance is the exact recovery error. -/
theorem origin_recovery_error (time : PositiveTime) :
    completedDist hw0 hw1 (centeredSource hw0 hw1 time originLoop).val v = B v v := by
  rw [origin_centeredSource_zero, completedDist_symm, dist_zero_right]

theorem origin_recovery_floor (time : PositiveTime) :
    RCle (rat (starRatio w))
      (completedDist hw0 hw1 (centeredSource hw0 hw1 time originLoop).val v) := by
  rw [origin_recovery_error]
  exact plaquetteExcitation_norm_floor hw0 hw1 1 originFace (originFace_mem 0)

/-- A positive separation floor, uniform in the insertion time, returned
as rational data. The floor still depends on the original nome. -/
def originSeparationCertificate :
    Σ' floor : Q', ((0 : Q') < floor) ×'
      (∀ time : PositiveTime, RCle (rat floor)
        (completedDist hw0 hw1 (centeredSource hw0 hw1 time originLoop).val v)) :=
  ⟨starRatio w, starRatio_positive hw0 hw1, origin_recovery_floor hw0 hw1⟩

/-- No positive-time schedule can recover this equal-time state, even if
the schedule is chosen with a separate all-tail convergence modulus. -/
theorem no_origin_recovery (times : Nat → PositiveTime) (rate : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
      RCle (completedDist hw0 hw1 (centeredSource hw0 hw1 (times n) originLoop).val v)
        (rat e)) : False := by
  apply plaquetteExcitation_norm_ne_zero hw0 hw1 1 originFace (originFace_mem 0)
  apply RCle_antisymm ?_ (completedInner_nonnegative hw0 hw1 v)
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro e he
  have h := bound e he (rate e) (Nat.le_refl _)
  rw [origin_recovery_error] at h
  have hz : RCadd RCzero (rat e) = rat e :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_of_eq (Q'.zero_add' e)))
  rwa [hz]

#print axioms positiveAction_zero
#print axioms positiveAction_time_one_commutes
#print axioms positiveAction_kills_time_kernel
#print axioms origin_centeredSource_zero
#print axioms origin_recovery_error
#print axioms origin_recovery_floor
#print axioms originSeparationCertificate
#print axioms no_origin_recovery

end YMGap.Continuum.BF4WilsonAllNomeSectorEqualTimeBoundary
