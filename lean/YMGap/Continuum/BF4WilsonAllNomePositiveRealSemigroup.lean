/-
# Positive real time on the SAME original Wilson carrier

The constructed operators descend to numerical positive real time values,
compose by addition, and recover the ORIGINAL geometric integer-time action.
Only the carrier-free time quotient and its addition are reused from legacy
modules. Every operator law below concerns the original Wilson completion.

This is not a full-carrier C0 semigroup: its original boundary kernel is
retained. Zero-time continuity on the witnessed positive-time sector,
the existing log-series generator identification, physical calibration,
spatial/scaling passage and the Clay target remain separate obligations.
-/

import YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeComposition
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup

namespace YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeComposition (positiveAction_sum)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue dyadicTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup
  (addTime addTime_comm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => realTimeAction hw0 hw1

theorem realTimeAction_addTime (s t : PositiveTimeValue) (x : V) :
    S (addTime s t) x = S s (S t x) := by
  refine Quotient.inductionOn₂ s t ?_
  intro D E
  exact positiveAction_sum hw0 hw1 D E x

theorem realTimeAction_commutes (s t : PositiveTimeValue) (x : V) :
    S s (S t x) = S t (S s x) := by
  rw [← realTimeAction_addTime, ← realTimeAction_addTime, addTime_comm]

theorem realTimeAction_symmetric (t : PositiveTimeValue) (x y : V) :
    B (S t x) y = B x (S t y) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_symmetric hw0 hw1 D x y

theorem realTimeAction_mixed_moments (s t : PositiveTimeValue) (x y : V) :
    B (S (addTime s t) x) y = B (S t x) (S s y) := by
  rw [realTimeAction_addTime, realTimeAction_symmetric]

theorem realTimeAction_doubled_moments (t : PositiveTimeValue) (x y : V) :
    B (S (addTime t t) x) y = B (S t x) (S t y) :=
  realTimeAction_mixed_moments hw0 hw1 t t x y

theorem realTimeAction_nonnegative (t : PositiveTimeValue) (x : V) :
    RCnonneg (B x (S t x)) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_nonnegative hw0 hw1 D x

theorem realTimeAction_norm_bound (t : PositiveTimeValue) (x : V) :
    RCle (B (S t x) (S t x)) (B x x) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_norm_bound hw0 hw1 D x

theorem realTimeAction_add (t : PositiveTimeValue) (x y : V) :
    S t (completedAdd hw0 hw1 x y) = completedAdd hw0 hw1 (S t x) (S t y) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_add hw0 hw1 D x y

theorem realTimeAction_smul (t : PositiveTimeValue) (c : Q') (x : V) :
    S t (completedSmul hw0 hw1 c x) = completedSmul hw0 hw1 c (S t x) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_smul hw0 hw1 D c x

theorem realTimeAction_realSmul (t : PositiveTimeValue) (s : CReal)
    (cs : QCauchy s.approx) (x : V) :
    S t (completedRealSmul hw0 hw1 s cs x) = completedRealSmul hw0 hw1 s cs (S t x) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_realSmul hw0 hw1 D s cs x

theorem realTimeAction_distance_bound (t : PositiveTimeValue) (x y : V) :
    RCle (completedDist hw0 hw1 (S t x) (S t y)) (completedDist hw0 hw1 x y) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_distance_bound hw0 hw1 D x y

/-- A unit remains exactly one original geometric transfer step. -/
theorem realTimeAction_original (n : Nat) (hn : 0 < n) (x : V) :
    S (timeValue (dyadicTime ⟨0,n⟩ hn)) x = completedTime hw0 hw1 n x :=
  positiveAction_original hw0 hw1 n hn x

#print axioms realTimeAction_addTime
#print axioms realTimeAction_commutes
#print axioms realTimeAction_symmetric
#print axioms realTimeAction_mixed_moments
#print axioms realTimeAction_doubled_moments
#print axioms realTimeAction_nonnegative
#print axioms realTimeAction_norm_bound
#print axioms realTimeAction_add
#print axioms realTimeAction_smul
#print axioms realTimeAction_realSmul
#print axioms realTimeAction_distance_bound
#print axioms realTimeAction_original

end YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup
