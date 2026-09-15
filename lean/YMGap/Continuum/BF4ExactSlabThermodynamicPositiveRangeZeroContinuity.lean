/-
# Real-time continuity at zero on ORIGINAL positive-time ranges

The semigroup law turns a small positive increment acting on A(s)x
into A(s+t)x. The preceding local time modulus at s>0 therefore proves
A(t)A(s)x -> A(s)x as the actual real value t tends to zero, with a
computed radius and original output representative. Time one is pinned
to the PRE-EXISTING T2, giving its original range as a concrete instance.

No new state carrier or range-density premise is introduced. This does
NOT prove the positive-time ranges dense, the transfer kernel zero, or
full-space continuity at zero. Physical Hamiltonian identification,
physical-scale/continuum/Clay remain open. Fixed SU(2) nome and spacing.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_add_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction (outputRepresentative outputRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem timeValue_nonnegative (t : PositiveTimeValue) : RCnonneg (realValue t) := by
  refine Quotient.inductionOn t ?_
  intro D
  have hq : RCle RCzero (rat D.floor) := leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt D.floor_positive)
  exact RCle_trans hq (timeValue_floor D)

theorem self_le_add_nonnegative (a b : RC) (hb : RCnonneg b) : RCle a (RCadd a b) := by
  have h := RCadd_le_add (RCle_refl a) hb
  rw [rc_add_zero] at h
  exact h

theorem addTime_close (s t : PositiveTimeValue) (delta : Q') (hd : (0 : Q') ≤ delta)
    (ht : RCle (realValue t) (rat delta)) :
    RCle (realValue s) (RCadd (realValue (addTime s t)) (rat delta)) ∧
    RCle (realValue (addTime s t)) (RCadd (realValue s) (rat delta)) := by
  rw [realValue_addTime]
  have hq : RCnonneg (rat delta) := leEv_le_ofQ'_of_approx_le (fun _ => hd)
  exact ⟨RCle_trans (self_le_add_nonnegative _ _ (timeValue_nonnegative t)) (self_le_add_nonnegative _ _ hq),
    RCadd_le_add (RCle_refl _) ht⟩

theorem positive_range_zero_bound (D : PositiveTime) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (t : PositiveTimeValue)
    (ht : RCle (realValue t) (rat (localRadius D X epsilon))) :
    RCle (completedDist (realTimeAction t (realTimeAction (timeValue D) (point X)))
      (realTimeAction (timeValue D) (point X))) (rat epsilon) := by
  have htime := addTime_close (timeValue D) t _ (Q'.le_of_lt (localRadius_positive D X epsilon)) ht
  have h := realTimeAction_locally_close D (addTime (timeValue D) t) X epsilon he htime.1 htime.2
  rw [realTimeAction_addTime, realTimeAction_commutes (timeValue D) t (point X), completedDist_symm] at h
  exact h

/-- Output representative and zero-time radius on an ACTUAL original positive-time range. -/
def rangeZeroContinuityCertificate (D : PositiveTime) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' Y : seminorm.Cauchy, Σ' delta : Q',
      ((point Y) = realTimeAction (timeValue D) (point X)) ×' ((0 : Q') < delta) ×'
      (∀ t : PositiveTimeValue, RCle (realValue t) (rat delta) →
        RCle (completedDist (realTimeAction t (point Y)) (point Y)) (rat epsilon)) :=
  ⟨outputRepresentative D X, localRadius D X epsilon, outputRepresentative_pin D X,
    localRadius_positive D X epsilon, fun t ht => by
      rw [outputRepresentative_pin]
      exact positive_range_zero_bound D X epsilon he t ht⟩

def oneTimeData : PositiveTime := dyadicTime ⟨0,1⟩ (by decide)

theorem oneTime_action (x : Completion) : realTimeAction (timeValue oneTimeData) x = twoStepTransfer x :=
  (realTimeAction_dyadic ⟨0,1⟩ (by decide) x).trans (BF4ExactSlabThermodynamicDyadicSemigroup.action_one x)

theorem twoStep_range_zero_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (t : PositiveTimeValue) (ht : RCle (realValue t) (rat (localRadius oneTimeData X epsilon))) :
    RCle (completedDist (realTimeAction t (twoStepTransfer (point X))) (twoStepTransfer (point X))) (rat epsilon) := by
  have h := positive_range_zero_bound oneTimeData X epsilon he t ht
  rw [oneTime_action] at h
  exact h

def twoStepZeroContinuityCertificate (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' delta : Q', ((0 : Q') < delta) ×'
      (∀ t : PositiveTimeValue, RCle (realValue t) (rat delta) →
        RCle (completedDist (realTimeAction t (twoStepTransfer (point X))) (twoStepTransfer (point X))) (rat epsilon)) :=
  ⟨localRadius oneTimeData X epsilon, localRadius_positive oneTimeData X epsilon,
    fun t ht => twoStep_range_zero_bound X epsilon he t ht⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.timeValue_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.self_le_add_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.addTime_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.positive_range_zero_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.rangeZeroContinuityCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.oneTimeData
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.oneTime_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.twoStep_range_zero_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.twoStepZeroContinuityCertificate
