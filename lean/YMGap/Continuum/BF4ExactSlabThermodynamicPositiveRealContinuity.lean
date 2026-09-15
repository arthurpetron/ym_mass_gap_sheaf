/-
# Quantitative continuity in ACTUAL positive real-time values

On every interval bounded away from zero, the ORIGINAL action has an
explicit time-continuity modulus. The hypotheses compare actual RC time
values, not arbitrarily chosen floors or Cauchy presentations. Eventual
rational mesh bounds follow from real order and pass through original
row limits. The time radius is computed from the interval floor and the
original state norm cap; it does not depend on time representatives.

All output rows and their Cauchy data were already constructed. Logical
eventual-order witnesses are used only to prove inequalities, never to
select output data. Full-space continuity at zero, physical Hamiltonian
identification and physical-scale/continuum/Clay closure remain open.
Fixed SU(2) nome and spacing only.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup
import YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.MeanExpConvexProgress (le_of_add_le_add_right)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowDistanceOrder (rowLimit_distance_eventual_le)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem approximation_value_pin (D : PositiveTime) :
    Quotient.mk crealSetoid (approximationReal D) = realValue (timeValue D) :=
  Quotient.sound (approximationReal_equiv D)

/-- Logical eventual bound for an already-constructed stream; no new data are extracted. -/
theorem time_lower_eventually (D : PositiveTime) (b : Q') (hb : (0 : Q') < b)
    (h : RCle (rat (b+b)) (realValue (timeValue D))) :
    ∃ N : Nat, ∀ n, N ≤ n → b ≤ value (approximation D n) := by
  rw [← approximation_value_pin D] at h
  change leEv (ofQ' (b+b)) (approximationReal D) at h
  obtain ⟨N,hN⟩ := h b hb
  exact ⟨N, fun n hn => le_of_add_le_add_right (hN n hn)⟩

theorem time_close_eventually (D E : PositiveTime) (delta : Q') (hd : (0 : Q') < delta)
    (h : RCle (realValue (timeValue D)) (RCadd (realValue (timeValue E)) (rat delta))) :
    ∃ N : Nat, ∀ n, N ≤ n →
      value (approximation D n) ≤ value (approximation E n) + (delta+delta) := by
  rw [← approximation_value_pin D, ← approximation_value_pin E] at h
  change leEv (approximationReal D) (CReal.add (approximationReal E) (ofQ' delta)) at h
  obtain ⟨N,hN⟩ := h delta hd
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _))⟩

def timeRadius (b : Q') (k : Nat) : Q' := HalfPow.half * (b * HalfPow.half^k)

theorem timeRadius_positive (b : Q') (hb : (0 : Q') < b) (k : Nat) : (0 : Q') < timeRadius b k :=
  ExpNeg.half_mul_pos _ (Q'.mul_pos hb (half_power_positive k))

theorem timeRadius_twice (b : Q') (k : Nat) : Q'.eqv (timeRadius b k + timeRadius b k) (b * HalfPow.half^k) :=
  ExpNeg.two_halves _

/-- Actual time values >=2b and actual time error <= b*half^(k+1) control the ORIGINAL norm. -/
theorem positiveAction_close_bound (D E : PositiveTime) (b : Q') (hb : (0 : Q') < b) (k : Nat)
    (hD : RCle (rat (b+b)) (realValue (timeValue D)))
    (hE : RCle (rat (b+b)) (realValue (timeValue E)))
    (hDE : RCle (realValue (timeValue D)) (RCadd (realValue (timeValue E)) (rat (timeRadius b k))))
    (hED : RCle (realValue (timeValue E)) (RCadd (realValue (timeValue D)) (rat (timeRadius b k))))
    (x : Completion) :
    RCle (completedDist (positiveAction D x) (positiveAction E x))
      (RCscale (HalfPow.half^k) (completedInner x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  obtain ⟨ND,hND⟩ := time_lower_eventually D b hb hD
  obtain ⟨NE,hNE⟩ := time_lower_eventually E b hb hE
  obtain ⟨NP,hNP⟩ := time_close_eventually D E _ (timeRadius_positive b hb k) hDE
  obtain ⟨NQ,hNQ⟩ := time_close_eventually E D _ (timeRadius_positive b hb k) hED
  let N := max (max ND NE) (max NP NQ)
  apply rowLimit_distance_eventual_le (timeRows D X) (timeRows E X) _ N
  intro n hn
  have hd := hND n (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn)
  have he := hNE n (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn)
  have hp := hNP n (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn)
  have hq := hNQ n (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn)
  have hp' := Q'.le_trans' _ _ _ hp (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (timeRadius_twice b k)))
  have hq' := Q'.le_trans' _ _ _ hq (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (timeRadius_twice b k)))
  rw [timeRows_pin, timeRows_pin]
  exact mesh_close_bound _ _ k b hd he hp' hq' (point X)

theorem realTimeAction_close_bound (s t : PositiveTimeValue) (b : Q') (hb : (0 : Q') < b) (k : Nat)
    (hs : RCle (rat (b+b)) (realValue s)) (ht : RCle (rat (b+b)) (realValue t))
    (hst : RCle (realValue s) (RCadd (realValue t) (rat (timeRadius b k))))
    (hts : RCle (realValue t) (RCadd (realValue s) (rat (timeRadius b k)))) (x : Completion) :
    RCle (completedDist (realTimeAction s x) (realTimeAction t x))
      (RCscale (HalfPow.half^k) (completedInner x x)) := by
  revert hs ht hst hts
  refine Quotient.inductionOn₂ s t ?_
  intro D E hD hE hDE hED
  exact positiveAction_close_bound D E b hb k hD hE hDE hED x

def continuityRadius (b : Q') (X : seminorm.Cauchy) (epsilon : Q') : Q' :=
  timeRadius b (rangeModulus X epsilon)

theorem continuityRadius_positive (b : Q') (hb : (0 : Q') < b) (X : seminorm.Cauchy) (epsilon : Q') :
    (0 : Q') < continuityRadius b X epsilon := timeRadius_positive b hb _

theorem realTimeAction_close (s t : PositiveTimeValue) (b : Q') (hb : (0 : Q') < b)
    (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hs : RCle (rat (b+b)) (realValue s)) (ht : RCle (rat (b+b)) (realValue t))
    (hst : RCle (realValue s) (RCadd (realValue t) (rat (continuityRadius b X epsilon))))
    (hts : RCle (realValue t) (RCadd (realValue s) (rat (continuityRadius b X epsilon)))) :
    RCle (completedDist (realTimeAction s (point X)) (realTimeAction t (point X))) (rat epsilon) :=
  RCle_trans (realTimeAction_close_bound s t b hb (rangeModulus X epsilon) hs ht hst hts (point X))
    (scaled_norm_small X epsilon he _ (Nat.le_refl _))

/-- One computed radius works for ALL actual time values >=2b, regardless of their representatives. -/
def uniformTimeContinuityCertificate (b : Q') (hb : (0 : Q') < b) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' delta : Q', ((0 : Q') < delta) ×'
      (∀ s t : PositiveTimeValue,
        RCle (rat (b+b)) (realValue s) → RCle (rat (b+b)) (realValue t) →
        RCle (realValue s) (RCadd (realValue t) (rat delta)) →
        RCle (realValue t) (RCadd (realValue s) (rat delta)) →
        RCle (completedDist (realTimeAction s (point X)) (realTimeAction t (point X))) (rat epsilon)) :=
  ⟨continuityRadius b X epsilon, continuityRadius_positive b hb X epsilon,
    fun s t hs ht hst hts => realTimeAction_close s t b hb X epsilon he hs ht hst hts⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.approximation_value_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.time_lower_eventually
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.time_close_eventually
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.timeRadius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.timeRadius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.timeRadius_twice
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.positiveAction_close_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.realTimeAction_close_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.continuityRadius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.continuityRadius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.realTimeAction_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity.uniformTimeContinuityCertificate
