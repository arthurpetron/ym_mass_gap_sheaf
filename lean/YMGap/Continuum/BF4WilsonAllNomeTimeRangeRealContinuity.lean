/-
# Exact real-time zero-continuity sector on the original Wilson carrier

A witnessed original time-range state supplies its own representative.
The existing dyadic continuity cutoff k gives the positive real radius
2^(-k-1). A real time below that radius has dyadic approximants eventually
below 2^(-k); the original norm bound passes through their represented limit.
The radius is computed from the range witness, not extracted from a
Prop-valued real inequality.

Conversely an explicit all-small-positive-real-time continuity radius,
restricted to actual dyadic roots, constructs the original range witness.
This characterizes the mathematical continuity sector in lattice time units.
It does not identify a physical OS sector or physical time, prove a scaling
estimate, delete the ambient boundary kernel, or package a self-adjoint
Hamiltonian.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeContinuitySector
import YMGap.Continuum.BF4WilsonAllNomeRowLinear
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
import YMGap.Continuum.BF4WilsonAllNomePositiveTimePins

namespace YMGap.Continuum.BF4WilsonAllNomeTimeRangeRealContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half)
open YMGap.Constructive.DyadicTimeRationals (value value_le_iff unit_value)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSub)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (RepresentedCauchy rowPoint limit)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
  (constantRows constantRows_point limit_constantRows pairingModulus row_pairing_bound)
open YMGap.Continuum.BF4WilsonAllNomeRowLinear
  (differenceRows differenceRows_pin rowLimit_difference)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeContinuitySector
  (continuityModulus smallTime rangeOfRootLimit)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction action_embed)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
  (timeRows timeRows_pin positiveAction_pin half_power_positive)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
  (realTimeAction realTimeAction_pin realTimeAction_dyadic)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue realValue dyadicTime)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => realTimeAction hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Original difference rows, with a representative computed FROM the range
witness rather than separately assumed. -/
def incrementRows {x : V} (witness : RangeLimit hw0 hw1 x) (time : PositiveTime) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  differenceRows hw0 hw1
    (timeRows hw0 hw1 time (representative hw0 hw1 witness))
    (constantRows hw0 hw1 (representative hw0 hw1 witness))

theorem incrementRows_pin {x : V} (witness : RangeLimit hw0 hw1 x)
    (time : PositiveTime) (n : Nat) :
    rowPoint hw0 hw1 (incrementRows hw0 hw1 witness time) n =
      completedSub hw0 hw1
        (meshAction hw0 hw1 (approximation time n).depth (approximation time n).steps x) x := by
  unfold incrementRows
  rw [differenceRows_pin,timeRows_pin,constantRows_point,representative_pin,action_embed]

theorem incrementRows_limit {x : V} (witness : RangeLimit hw0 hw1 x)
    (time : PositiveTime) :
    limit hw0 hw1 (incrementRows hw0 hw1 witness time) =
      completedSub hw0 hw1 (S (timeValue time) x) x := by
  unfold incrementRows
  rw [rowLimit_difference,limit_constantRows,← positiveAction_pin,representative_pin,
    realTimeAction_pin]

def realRadius {x : V} (witness : RangeLimit hw0 hw1 x) (e : Q') : Q' :=
  half * half^(continuityModulus hw0 hw1 witness e)

theorem realRadius_positive {x : V} (witness : RangeLimit hw0 hw1 x) (e : Q') :
    (0 : Q') < realRadius hw0 hw1 witness e :=
  ExpNeg.half_mul_pos _ (half_power_positive _)

/-- All sufficiently small positive REAL increments on the actual original
state, using the SAME positive-real-time operator and an explicit radius. -/
theorem real_smallTime {x : V} (witness : RangeLimit hw0 hw1 x)
    (e : Q') (he : (0 : Q') < e) (time : PositiveTime)
    (ht : RCle (realValue (timeValue time)) (rat (realRadius hw0 hw1 witness e))) :
    RCle (dist (S (timeValue time) x) x) (rat e) := by
  have htime : Quotient.mk crealSetoid (approximationReal time) =
      realValue (timeValue time) := Quotient.sound (approximationReal_equiv time)
  have hap : RCle (Quotient.mk crealSetoid (approximationReal time))
      (rat (realRadius hw0 hw1 witness e)) := by
    rw [htime]
    exact ht
  change leEv (approximationReal time) (ofQ' (realRadius hw0 hw1 witness e)) at hap
  obtain ⟨N,hN⟩ := hap (realRadius hw0 hw1 witness e) (realRadius_positive hw0 hw1 witness e)
  have hsmall (n : Nat) (hn : N ≤ n) :
      (approximation time n).steps * 2^(continuityModulus hw0 hw1 witness e) ≤
        2^(approximation time n).depth := by
    have hv : value (approximation time n) ≤ half^(continuityModulus hw0 hw1 witness e) :=
      Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv (ExpNeg.two_halves _))
    have h := (value_le_iff (approximation time n) ⟨continuityModulus hw0 hw1 witness e,1⟩).mp
      (Q'.le_trans' _ _ _ hv (Q'.ge_of_eqv (unit_value _)))
    simpa only [Nat.one_mul] using h
  let rows := incrementRows hw0 hw1 witness time
  have hlimit : RCle (B (limit hw0 hw1 rows) (limit hw0 hw1 rows)) (rat e) := by
    apply RationalScalarTwoSidedError.le_of_all_errors
    intro delta hd
    let n := max (pairingModulus hw0 hw1 rows rows delta) N
    have hp := (row_pairing_bound hw0 hw1 rows rows delta hd n (Nat.le_max_left _ _)).2
    have hs : RCle (B (rowPoint hw0 hw1 rows n) (rowPoint hw0 hw1 rows n)) (rat e) := by
      rw [show rows = incrementRows hw0 hw1 witness time from rfl,incrementRows_pin]
      exact smallTime hw0 hw1 witness e he
        (approximation time n).depth (approximation time n).steps (hsmall n (Nat.le_max_right _ _))
    exact RCle_trans hp (RCadd_le_add hs (RCle_refl _))
  rw [show rows = incrementRows hw0 hw1 witness time from rfl,incrementRows_limit] at hlimit
  exact hlimit

def realContinuityCertificate {x : V} (witness : RangeLimit hw0 hw1 x)
    (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ time : PositiveTime, RCle (realValue (timeValue time)) (rat r) →
        RCle (dist (S (timeValue time) x) x) (rat e)) :=
  ⟨realRadius hw0 hw1 witness e,realRadius_positive hw0 hw1 witness e,
    real_smallTime hw0 hw1 witness e he⟩

/-- The converse consumes the actual real-time continuity data and returns
the original sector witness. No derivative or physical interpretation is used. -/
def rangeOfRealContinuity (X : (D).Cauchy) (radius : Q' → Q')
    (positive : ∀ e : Q', (0 : Q') < e → (0 : Q') < radius e)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ time : PositiveTime,
      RCle (realValue (timeValue time)) (rat (radius e)) →
        RCle (dist (S (timeValue time) (Class X)) (Class X)) (rat e)) :
    RangeLimit hw0 hw1 (Class X) :=
  rangeOfRootLimit hw0 hw1 X (fun e => (radius e).den) (by
    intro e he k hk
    have ht : RCle (realValue (timeValue (dyadicTime ⟨k,1⟩ (Nat.succ_pos 0)))) (rat (radius e)) := by
      change RCle (rat (value ⟨k,1⟩)) (rat (radius e))
      exact leEv_le_ofQ'_of_approx_le (fun _ =>
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (unit_value k))
          (Q'.le_trans' _ _ _ (HalfPow.pow_half_le_invSucc k)
            (Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hk)
              (HalfPow.invSucc_den_le _ (positive e he)))))
    have h := bound e he (dyadicTime ⟨k,1⟩ (Nat.succ_pos 0)) ht
    rw [realTimeAction_dyadic,action_embed] at h
    exact h)

#print axioms incrementRows
#print axioms incrementRows_pin
#print axioms incrementRows_limit
#print axioms realRadius
#print axioms realRadius_positive
#print axioms real_smallTime
#print axioms realContinuityCertificate
#print axioms rangeOfRealContinuity

end YMGap.Continuum.BF4WilsonAllNomeTimeRangeRealContinuity
