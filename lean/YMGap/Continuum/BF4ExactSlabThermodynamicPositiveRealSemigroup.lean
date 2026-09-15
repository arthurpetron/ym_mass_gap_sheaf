/-
# The SAME positive-real-time operators form a semigroup

Constructed sum-time data descend to representation-independent time
values. Their addition is pinned to the original RC addition, with
commutativity and associativity. The PREVIOUS realTimeAction satisfies
composition, mixed/doubled moments, and all original state linear,
positive, symmetric, contractive, unit and centering laws.

This is an algebraic semigroup indexed by positive represented real
values, not yet a strongly continuous semigroup on all nonnegative
times. Full-space continuity at zero, geometric T1 identification,
Hamiltonian, physical-scale, continuum and Clay closure remain open.
Fixed SU(2) nome and spacing; no new physical input or surrogate state.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.PositiveRealDyadicTimeAddition
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (center UnitComplement center_fixed_iff)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition

theorem sumTime_congr {D D' E E' : PositiveTime} (hD : Equiv D.real D'.real) (hE : Equiv E.real E'.real) :
    Equiv (sumTime D E).real (sumTime D' E').real :=
  (sumTime_real_equiv D E).trans ((Equiv_add hD hE).trans (sumTime_real_equiv D' E').symm)

def addTime : PositiveTimeValue → PositiveTimeValue → PositiveTimeValue :=
  Quotient.lift₂ (fun D E => timeValue (sumTime D E))
    (fun _ _ _ _ hD hE => Quotient.sound (sumTime_congr hD hE))

theorem addTime_pin (D E : PositiveTime) : addTime (timeValue D) (timeValue E) = timeValue (sumTime D E) := rfl

theorem realValue_addTime (s t : PositiveTimeValue) : realValue (addTime s t) = RCadd (realValue s) (realValue t) := by
  refine Quotient.inductionOn₂ s t ?_
  intro D E
  exact sumTime_real_pin D E

theorem addTime_comm (s t : PositiveTimeValue) : addTime s t = addTime t s := by
  apply realValue_injective
  rw [realValue_addTime, realValue_addTime]
  exact BF4ExactSlabThermodynamicBernsteinWords.add_comm _ _

theorem addTime_assoc (s t u : PositiveTimeValue) : addTime (addTime s t) u = addTime s (addTime t u) := by
  apply realValue_injective
  rw [realValue_addTime, realValue_addTime, realValue_addTime, realValue_addTime]
  exact BF4ExactSlabThermodynamicBernsteinWords.add_assoc _ _ _

theorem realTimeAction_addTime (s t : PositiveTimeValue) (x : Completion) :
    realTimeAction (addTime s t) x = realTimeAction s (realTimeAction t x) := by
  refine Quotient.inductionOn₂ s t ?_
  intro D E
  exact positiveAction_sum D E x

theorem realTimeAction_commutes (s t : PositiveTimeValue) (x : Completion) :
    realTimeAction s (realTimeAction t x) = realTimeAction t (realTimeAction s x) := by
  rw [← realTimeAction_addTime, ← realTimeAction_addTime, addTime_comm]

theorem realTimeAction_mixed_moments (s t : PositiveTimeValue) (x y : Completion) :
    completedInner (realTimeAction (addTime s t) x) y =
      completedInner (realTimeAction t x) (realTimeAction s y) := by
  rw [realTimeAction_addTime, realTimeAction_symmetric]

theorem realTimeAction_doubled_moments (t : PositiveTimeValue) (x y : Completion) :
    completedInner (realTimeAction (addTime t t) x) y =
      completedInner (realTimeAction t x) (realTimeAction t y) :=
  realTimeAction_mixed_moments t t x y

theorem realTimeAction_add_state (t : PositiveTimeValue) (x y : Completion) :
    realTimeAction t (completedAdd x y) = completedAdd (realTimeAction t x) (realTimeAction t y) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_add D x y

theorem realTimeAction_smul (t : PositiveTimeValue) (c : Q') (x : Completion) :
    realTimeAction t (completedSmul c x) = completedSmul c (realTimeAction t x) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_smul D c x

theorem realTimeAction_sub (t : PositiveTimeValue) (x y : Completion) :
    realTimeAction t (completedSub x y) = completedSub (realTimeAction t x) (realTimeAction t y) := by
  unfold completedSub completedNeg
  rw [realTimeAction_add_state, realTimeAction_smul]

theorem realTimeAction_distance_contraction (t : PositiveTimeValue) (x y : Completion) :
    RCle (completedDist (realTimeAction t x) (realTimeAction t y)) (completedDist x y) := by
  unfold completedDist
  rw [← realTimeAction_sub]
  exact realTimeAction_contraction t (completedSub x y)

theorem realTimeAction_center (t : PositiveTimeValue) (x : Completion) :
    realTimeAction t (center x) = center (realTimeAction t x) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_center D x

theorem realTimeAction_complement (t : PositiveTimeValue) (x : Completion)
    (hx : completedInner x completedUnit = RCzero) :
    completedInner (realTimeAction t x) completedUnit = RCzero := by
  apply (center_fixed_iff _).mp
  rw [← realTimeAction_center, (center_fixed_iff x).mpr hx]

def complementAction (t : PositiveTimeValue) (x : UnitComplement) : UnitComplement :=
  ⟨realTimeAction t x.val, realTimeAction_complement t x.val x.property⟩

theorem complementAction_pin (t : PositiveTimeValue) (x : UnitComplement) :
    (complementAction t x).val = realTimeAction t x.val := rfl

theorem complementAction_addTime (s t : PositiveTimeValue) (x : UnitComplement) :
    complementAction (addTime s t) x = complementAction s (complementAction t x) :=
  Subtype.ext (realTimeAction_addTime s t x.val)

end YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.sumTime_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.addTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.addTime_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realValue_addTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.addTime_comm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.addTime_assoc
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_addTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_commutes
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_mixed_moments
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_doubled_moments
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_add_state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_distance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_complement
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.complementAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.complementAction_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup.complementAction_addTime
