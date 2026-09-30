/-
# SAME-real-time independence and original dyadic recovery

The original positive-time limit is independent of the supplied time floor,
start index, Cauchy modulus and real representative. Equality proofs compare
already-constructed outputs; no data are extracted from Prop-valued Equiv.
Every positive dyadic time, including original integer time, is recovered.

Only the carrier-free numerical time quotient and rational-time constructor
are reused from the legacy PositiveTimePins namespace. The operator below
is newly descended from the original Wilson action; no legacy carrier or
operator law is used. Time addition, appropriate continuity at zero and
the generator/physical-time/scaling joins remain separate obligations.
-/

import YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins

namespace YMGap.Continuum.BF4WilsonAllNomePositiveTimePins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint embed)
open YMGap.Constructive.DyadicTimeRationals (value upper upper_error)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (action action_whole)
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (mesh_positive dyadicTime PositiveTimeValue timeValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "P" => distanceData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "d" => completedDist hw0 hw1
local notation "F" => positiveAction hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Equal represented real times give the same already-constructed original operator. -/
theorem positiveAction_time_congr (time other : PositiveTime)
    (heq : Equiv time.real other.real) (x : V) : F time x = F other x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply CRealSeminormCauchyRows.completed_eq_of_small P
  intro epsilon he
  let e := quarter (quarter epsilon)
  have he' : (0 : Q') < e := quarter_pos (quarter_pos he)
  let floor := Q'.min' time.floor other.floor
  have hf : (0 : Q') < floor := by
    unfold floor Q'.min'
    split
    · exact time.floor_positive
    · exact other.floor_positive
  let k := rangeModulus hw0 hw1 X e
  have hdelta := Q'.mul_pos hf (half_power_positive k)
  have htime := (approximationReal_equiv time).trans
    (heq.trans (approximationReal_equiv other).symm)
  obtain ⟨N,hN⟩ := htime (floor*HalfPow.half^k) hdelta
  let n := max (max (convergenceModulus hw0 hw1 time X e) (convergenceModulus hw0 hw1 other X e)) N
  have hleft := approximation_bound hw0 hw1 time X e he' n
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have hright := approximation_bound hw0 hw1 other X e he' n
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  have hcompare := hN n (Nat.le_max_right _ _)
  have hmiddle := RCle_trans
    (mesh_close_bound hw0 hw1 (approximation time n) (approximation other n) k floor
      (Q'.le_trans' _ _ _ (Q'.min_le_left' _ _) (approximation_lower time n))
      (Q'.le_trans' _ _ _ (Q'.min_le_right' _ _) (approximation_lower other n))
      hcompare.1 hcompare.2 (Class X))
    (scaled_norm_small hw0 hw1 X e he' k (Nat.le_refl _))
  rw [completedDist_symm] at hleft
  exact CRealSeminormCompletedApproximation.completedDist_three_segment P _ _ _ _ epsilon he
    hleft hmiddle hright

def dyadicPinModulus (p : MeshPoint) (X : (D).Cauchy) (epsilon : Q') : Nat :=
  (value p*HalfPow.half^(rangeModulus hw0 hw1 X epsilon)).den

theorem dyadic_approximation_bound (p : MeshPoint) (hp : 0 < p.steps) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat) (hn : dyadicPinModulus hw0 hw1 p X epsilon ≤ n) :
    RCle (d (rowPoint hw0 hw1 (timeRows hw0 hw1 (dyadicTime p hp) X) n)
      (action hw0 hw1 (embed p) (Class X))) (rat epsilon) := by
  let k := rangeModulus hw0 hw1 X epsilon
  have hdelta := Q'.mul_pos (mesh_positive p hp) (half_power_positive k)
  have herr : HalfPow.half^n ≤ value p*HalfPow.half^k :=
    Q'.le_trans' _ _ _ (HalfPow.pow_half_le_invSucc n)
      (Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le _ hdelta))
  have hu := upper_error (value p) (Q'.le_of_lt (mesh_positive p hp)) n
  have hleft := Q'.le_trans' _ _ _ hu.2 (Q'.add_le_add_left _ _ _ herr)
  have hright := Q'.le_trans' _ _ _ hu.1 (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hdelta))
  have h := RCle_trans (mesh_close_bound hw0 hw1 (upper (value p) n) p k (value p)
    hu.1 (Q'.le_refl' _) hleft hright (Class X))
    (scaled_norm_small hw0 hw1 X epsilon he k (Nat.le_refl _))
  rw [timeRows_pin]
  exact h

/-- Actual recovery, not merely compatibility with an independently supplied dyadic map. -/
theorem positiveAction_dyadic (p : MeshPoint) (hp : 0 < p.steps) (x : V) :
    F (dyadicTime p hp) x = action hw0 hw1 (embed p) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact limit_unique hw0 hw1 (timeRows hw0 hw1 (dyadicTime p hp) X) _
    (dyadicPinModulus hw0 hw1 p X) (dyadic_approximation_bound hw0 hw1 p hp X)

/-- A whole positive time interval is exactly the ORIGINAL geometric-time operator. -/
theorem positiveAction_original (n : Nat) (hn : 0 < n) (x : V) :
    F (dyadicTime ⟨0,n⟩ hn) x = completedTime hw0 hw1 n x :=
  (positiveAction_dyadic hw0 hw1 ⟨0,n⟩ hn x).trans (action_whole hw0 hw1 n x)

/-- Reuse the numerical real-time quotient, but descend the ORIGINAL Wilson operator. -/
def realTimeAction (time : PositiveTimeValue) (x : V) : V :=
  Quotient.lift (fun t => F t x) (fun t u h => positiveAction_time_congr hw0 hw1 t u h x) time

theorem realTimeAction_pin (time : PositiveTime) (x : V) :
    realTimeAction hw0 hw1 (timeValue time) x = F time x := rfl

theorem realTimeAction_dyadic (p : MeshPoint) (hp : 0 < p.steps) (x : V) :
    realTimeAction hw0 hw1 (timeValue (dyadicTime p hp)) x = action hw0 hw1 (embed p) x :=
  positiveAction_dyadic hw0 hw1 p hp x

#print axioms positiveAction_time_congr
#print axioms dyadicPinModulus
#print axioms dyadic_approximation_bound
#print axioms positiveAction_dyadic
#print axioms positiveAction_original
#print axioms realTimeAction
#print axioms realTimeAction_pin
#print axioms realTimeAction_dyadic

end YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
