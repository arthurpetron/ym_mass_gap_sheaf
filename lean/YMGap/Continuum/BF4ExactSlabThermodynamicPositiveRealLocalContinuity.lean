/-
# Local and joint continuity of the SAME positive-time action

A supplied positive time computes a local interval floor from its
numerical positivity witness. Sufficiently close ACTUAL time values
automatically remain in that interval; no positivity-floor hypothesis
is imposed on the comparison time. The previous away-from-zero
estimate therefore gives a computed local time modulus.

Original contraction also gives a joint time/state modulus. The
comparison state and time are arbitrary existing quotient values;
no representatives are selected. Full-space continuity at time zero,
physical Hamiltonian identification, physical-scale/continuum/Clay
remain open. The SU(2) nome and spacing remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.MeanExpConvexProgress (le_of_add_le_add_right)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation (completedDist_two_segment)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup (realTimeAction_distance_contraction)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem real_add_cancel (a b c : RC) (h : RCle (RCadd a c) (RCadd b c)) : RCle a b := by
  revert h
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C h epsilon he
  obtain ⟨N,hN⟩ := h epsilon he
  refine ⟨N, fun n hn => ?_⟩
  apply le_of_add_le_add_right (c := C.approx n)
  exact Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv
    (RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => B.approx n | 1 => C.approx n | _ => epsilon)))

theorem timeRadius_le (b : Q') (hb : (0 : Q') ≤ b) (k : Nat) : timeRadius b k ≤ b := by
  have hh : HalfPow.half^k ≤ (1 : Q') := half_pow_antitone 0 k (Nat.zero_le _)
  have hp : b*HalfPow.half^k ≤ b := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hh hb) (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hp HalfPow.half_nonneg)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ b (by decide : HalfPow.half ≤ (1 : Q')) hb)
      (Q'.le_of_eqv (Q'.one_mul_eqv _)))

theorem timeValue_floor (D : PositiveTime) : RCle (rat D.floor) (realValue (timeValue D)) := by
  rw [← approximation_value_pin D]
  exact leEv_ofQ'_of_approx_ge (approximation_lower D)

def localFloor (D : PositiveTime) : Q' := quarter D.floor

theorem localFloor_positive (D : PositiveTime) : (0 : Q') < localFloor D := quarter_pos D.floor_positive

theorem localFloor_four (D : PositiveTime) :
    Q'.eqv ((localFloor D+localFloor D)+(localFloor D+localFloor D)) D.floor :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*D.floor)) (ExpNeg.two_halves (HalfPow.half*D.floor)))
    (ExpNeg.two_halves D.floor)

theorem localTime_floor (D : PositiveTime) :
    RCle (rat (localFloor D+localFloor D)) (realValue (timeValue D)) := by
  have hb := Q'.le_of_lt (localFloor_positive D)
  have h := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (Q'.zero_le_add _ _ hb hb)) (Q'.le_of_eqv (localFloor_four D))
  have hq : RCle (rat (localFloor D+localFloor D)) (rat D.floor) :=
    leEv_le_ofQ'_of_approx_le (fun _ => h)
  exact RCle_trans hq (timeValue_floor D)

theorem nearbyTime_floor (D : PositiveTime) (t : PositiveTimeValue) (delta : Q')
    (hd : delta ≤ localFloor D+localFloor D)
    (hDt : RCle (realValue (timeValue D)) (RCadd (realValue t) (rat delta))) :
    RCle (rat (localFloor D+localFloor D)) (realValue t) := by
  apply real_add_cancel _ _ (rat (localFloor D+localFloor D))
  have hq : RCle (rat ((localFloor D+localFloor D)+(localFloor D+localFloor D))) (rat D.floor) :=
    leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv (localFloor_four D))
  have hf : RCle (rat ((localFloor D+localFloor D)+(localFloor D+localFloor D)))
      (realValue (timeValue D)) := RCle_trans hq (timeValue_floor D)
  exact RCle_trans hf (RCle_trans hDt (RCadd_le_add (RCle_refl _)
    (leEv_le_ofQ'_of_approx_le (fun _ => hd))))

def localRadius (D : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q') : Q' :=
  continuityRadius (localFloor D) X epsilon

theorem localRadius_positive (D : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q') :
    (0 : Q') < localRadius D X epsilon := continuityRadius_positive _ (localFloor_positive D) X epsilon

theorem localRadius_small (D : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q') :
    localRadius D X epsilon ≤ localFloor D+localFloor D :=
  Q'.le_trans' _ _ _ (timeRadius_le _ (Q'.le_of_lt (localFloor_positive D)) _)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (localFloor_positive D)))

/-- Local continuity at every supplied positive time, with arbitrary comparison time values. -/
theorem realTimeAction_locally_close (D : PositiveTime) (t : PositiveTimeValue)
    (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hDt : RCle (realValue (timeValue D)) (RCadd (realValue t) (rat (localRadius D X epsilon))))
    (htD : RCle (realValue t) (RCadd (realValue (timeValue D)) (rat (localRadius D X epsilon)))) :
    RCle (completedDist (realTimeAction (timeValue D) (point X)) (realTimeAction t (point X))) (rat epsilon) :=
  realTimeAction_close _ _ (localFloor D) (localFloor_positive D) X epsilon he
    (localTime_floor D) (nearbyTime_floor D t _ (localRadius_small D X epsilon) hDt) hDt htD

def localTimeContinuityCertificate (D : PositiveTime) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' delta : Q', ((0 : Q') < delta) ×'
      (∀ t : PositiveTimeValue,
        RCle (realValue (timeValue D)) (RCadd (realValue t) (rat delta)) →
        RCle (realValue t) (RCadd (realValue (timeValue D)) (rat delta)) →
        RCle (completedDist (realTimeAction (timeValue D) (point X)) (realTimeAction t (point X))) (rat epsilon)) :=
  ⟨localRadius D X epsilon, localRadius_positive D X epsilon,
    fun t hDt htD => realTimeAction_locally_close D t X epsilon he hDt htD⟩

theorem realTimeAction_jointly_close (D : PositiveTime) (t : PositiveTimeValue)
    (X : seminorm.Cauchy) (y : Completion) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hDt : RCle (realValue (timeValue D)) (RCadd (realValue t) (rat (localRadius D X (quarter epsilon)))))
    (htD : RCle (realValue t) (RCadd (realValue (timeValue D)) (rat (localRadius D X (quarter epsilon)))))
    (hxy : RCle (completedDist (point X) y) (rat (quarter epsilon))) :
    RCle (completedDist (realTimeAction (timeValue D) (point X)) (realTimeAction t y)) (rat epsilon) :=
  completedDist_two_segment _ _ _ epsilon
    (realTimeAction_locally_close D t X _ (quarter_pos he) hDt htD)
    (RCle_trans (realTimeAction_distance_contraction t (point X) y) hxy)

/-- Explicit time and state radii; comparison time/state representatives are never selected. -/
def jointContinuityCertificate (D : PositiveTime) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' timeDelta : Q', Σ' stateDelta : Q',
      ((0 : Q') < timeDelta) ×' ((0 : Q') < stateDelta) ×'
      (∀ t : PositiveTimeValue, ∀ y : Completion,
        RCle (realValue (timeValue D)) (RCadd (realValue t) (rat timeDelta)) →
        RCle (realValue t) (RCadd (realValue (timeValue D)) (rat timeDelta)) →
        RCle (completedDist (point X) y) (rat stateDelta) →
        RCle (completedDist (realTimeAction (timeValue D) (point X)) (realTimeAction t y)) (rat epsilon)) :=
  ⟨localRadius D X (quarter epsilon), quarter epsilon,
    localRadius_positive D X _, quarter_pos he,
    fun t y hDt htD hxy => realTimeAction_jointly_close D t X y epsilon he hDt htD hxy⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.real_add_cancel
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.timeRadius_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.timeValue_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.localFloor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.localFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.localFloor_four
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.localTime_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.nearbyTime_floor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.localRadius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.localRadius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.localRadius_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.realTimeAction_locally_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.localTimeContinuityCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.realTimeAction_jointly_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity.jointContinuityCertificate
