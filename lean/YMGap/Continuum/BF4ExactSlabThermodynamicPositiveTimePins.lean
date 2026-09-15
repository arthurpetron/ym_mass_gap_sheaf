/-
# Positive real-time action depends only on the SAME real time

Equivalent supplied real times give identical original operators, even
when their floors, starting indices, Cauchy data and dyadic approximations
differ. The already-constructed limits are compared inside an equality
proof; the legacy Prop-valued Equiv never selects any output data.
Every positive dyadic time recovers the existing dyadic action exactly.
The same original unit and centering map are retained. Quotient time
indexing is pinned injectively to the original RC value of the time.

Time addition, full-space continuity at zero, geometric T1 identification,
Hamiltonian/physical-scale/continuum/Clay closure remain open. Fixed SU(2)
nome and spacing only; no new physical hypothesis or surrogate carrier.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint)
open YMGap.Constructive.DyadicTimeRationals (value value_num upper upper_error)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.RegularLinearGeometricModulus (halfCutoff halfCutoff_spec)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation (completedDist_three_segment)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection (unitCauchy unitCauchy_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (center centerCauchy center_mk)
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity
  (centeredRows centeredRows_rowPoint rowLimit_centeredRows)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup (action)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

/-- Equality of already-constructed limits; no computational witness is extracted from Equiv. -/
theorem positiveAction_time_congr (D E : PositiveTime) (hDE : Equiv D.real E.real) (x : Completion) :
    positiveAction D x = positiveAction E x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completed_eq_of_small
  intro epsilon he
  let e := quarter (quarter epsilon)
  have he' : (0 : Q') < e := quarter_pos (quarter_pos he)
  let b := Q'.min' D.floor E.floor
  have hb : (0 : Q') < b := by
    unfold b Q'.min'
    split
    · exact D.floor_positive
    · exact E.floor_positive
  let k := rangeModulus X e
  have hdelta := Q'.mul_pos hb (half_power_positive k)
  have htime := (approximationReal_equiv D).trans (hDE.trans (approximationReal_equiv E).symm)
  obtain ⟨N,hN⟩ := htime (b*HalfPow.half^k) hdelta
  let n := max (max (rowLimitRate (timeRows D X) e) (rowLimitRate (timeRows E X) e)) N
  have hD := rowLimit_bound (timeRows D X) e he' n (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have hE := rowLimit_bound (timeRows E X) e he' n (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  have hcompare := hN n (Nat.le_max_right _ _)
  have hmiddle := RCle_trans (mesh_close_bound (approximation D n) (approximation E n) k b
    (Q'.le_trans' _ _ _ (Q'.min_le_left' _ _) (approximation_lower D n))
    (Q'.le_trans' _ _ _ (Q'.min_le_right' _ _) (approximation_lower E n))
    hcompare.1 hcompare.2 (point X)) (scaled_norm_small X e he' k (Nat.le_refl _))
  rw [timeRows_pin, completedDist_symm] at hD
  rw [timeRows_pin] at hE
  exact completedDist_three_segment _ _ _ _ epsilon he hD hmiddle hE

theorem positiveAction_unit (D : PositiveTime) : positiveAction D completedUnit = completedUnit := by
  have h : rowLimit (timeRows D unitCauchy) = rowLimit (constantRows unitCauchy) := by
    apply rowLimit_independent
    intro n
    rw [timeRows_pin, constantRows_pin, unitCauchy_pin]
    exact BF4ExactSlabThermodynamicDyadicSemigroup.action_unit _
  rw [rowLimit_constant] at h
  exact h

theorem positiveAction_center (D : PositiveTime) (x : Completion) :
    positiveAction D (center x) = center (positiveAction D x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h : rowLimit (timeRows D (centerCauchy X)) = rowLimit (centeredRows (timeRows D X)) := by
    apply rowLimit_independent
    intro n
    rw [timeRows_pin, centeredRows_rowPoint, timeRows_pin, ← center_mk]
    exact BF4ExactSlabThermodynamicDyadicSemigroup.action_center _ _
  rw [rowLimit_centeredRows] at h
  exact h

theorem mesh_positive (p : MeshPoint) (hp : 0 < p.steps) : (0 : Q') < value p := by
  apply CReal.pos_of_num_pos
  rw [value_num]
  exact Int.ofNat_lt.mpr hp

def dyadicTime (p : MeshPoint) (hp : 0 < p.steps) : PositiveTime := rational (value p) (mesh_positive p hp)

def dyadicPinModulus (p : MeshPoint) (X : seminorm.Cauchy) (epsilon : Q') : Nat :=
  halfCutoff (value p * HalfPow.half^(rangeModulus X epsilon))

theorem dyadic_approximation_bound (p : MeshPoint) (hp : 0 < p.steps) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat) (hn : dyadicPinModulus p X epsilon ≤ n) :
    RCle (completedDist (rowPoint (timeRows (dyadicTime p hp) X) n)
      (action (NonnegativeDyadicTime.embed p) (point X))) (rat epsilon) := by
  let k := rangeModulus X epsilon
  have hdelta := Q'.mul_pos (mesh_positive p hp) (half_power_positive k)
  have herr : HalfPow.half^n ≤ value p * HalfPow.half^k :=
    Q'.le_trans' _ _ _ (half_pow_antitone _ n hn) (halfCutoff_spec _ hdelta)
  have hu := upper_error (value p) (Q'.le_of_lt (mesh_positive p hp)) n
  have hleft := Q'.le_trans' _ _ _ hu.2 (Q'.add_le_add_left _ _ _ herr)
  have hright := Q'.le_trans' _ _ _ hu.1 (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hdelta))
  have h := RCle_trans (mesh_close_bound (upper (value p) n) p k (value p)
    hu.1 (Q'.le_refl' _) hleft hright (point X)) (scaled_norm_small X epsilon he k (Nat.le_refl _))
  rw [timeRows_pin]
  exact h

/-- Exact recovery of every existing POSITIVE dyadic operator, not merely a new compatible action. -/
theorem positiveAction_dyadic (p : MeshPoint) (hp : 0 < p.steps) (x : Completion) :
    positiveAction (dyadicTime p hp) x = action (NonnegativeDyadicTime.embed p) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact rowLimit_eq_of_bound (timeRows (dyadicTime p hp) X) _ (dyadicPinModulus p X)
    (dyadic_approximation_bound p hp X)

def timeSetoid : Setoid PositiveTime where
  r D E := Equiv D.real E.real
  iseqv := ⟨fun _ => Equiv.refl _, fun h => h.symm, fun h k => h.trans k⟩

def PositiveTimeValue : Type := Quotient timeSetoid

def timeValue (D : PositiveTime) : PositiveTimeValue := Quotient.mk timeSetoid D

def realValue : PositiveTimeValue → RC :=
  Quotient.lift (fun D => Quotient.mk crealSetoid D.real) (fun _ _ h => Quotient.sound h)

theorem realValue_pin (D : PositiveTime) : realValue (timeValue D) = Quotient.mk crealSetoid D.real := rfl

/-- The time quotient has no identifications beyond equality of the supplied real values. -/
theorem realValue_injective (s t : PositiveTimeValue) (h : realValue s = realValue t) : s = t := by
  revert h
  refine Quotient.inductionOn₂ s t ?_
  intro D E h
  change Quotient.mk crealSetoid D.real = Quotient.mk crealSetoid E.real at h
  have hDE : Equiv D.real E.real := Quotient.exact h
  exact Quotient.sound hDE

def realTimeAction (t : PositiveTimeValue) (x : Completion) : Completion :=
  Quotient.lift (fun D => positiveAction D x) (fun D E h => positiveAction_time_congr D E h x) t

theorem realTimeAction_pin (D : PositiveTime) (x : Completion) :
    realTimeAction (timeValue D) x = positiveAction D x := rfl

theorem realTimeAction_dyadic (p : MeshPoint) (hp : 0 < p.steps) (x : Completion) :
    realTimeAction (timeValue (dyadicTime p hp)) x = action (NonnegativeDyadicTime.embed p) x :=
  positiveAction_dyadic p hp x

theorem realTimeAction_unit (t : PositiveTimeValue) : realTimeAction t completedUnit = completedUnit := by
  refine Quotient.inductionOn t ?_
  exact positiveAction_unit

theorem realTimeAction_contraction (t : PositiveTimeValue) (x : Completion) :
    RCle (completedInner (realTimeAction t x) (realTimeAction t x)) (completedInner x x) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_contraction D x

theorem realTimeAction_nonnegative (t : PositiveTimeValue) (x : Completion) :
    RCnonneg (completedInner (realTimeAction t x) x) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_nonnegative D x

theorem realTimeAction_symmetric (t : PositiveTimeValue) (x y : Completion) :
    completedInner (realTimeAction t x) y = completedInner x (realTimeAction t y) := by
  refine Quotient.inductionOn t ?_
  exact fun D => positiveAction_symmetric D x y

end YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.positiveAction_time_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.positiveAction_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.positiveAction_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.mesh_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.dyadicTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.dyadicPinModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.dyadic_approximation_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.positiveAction_dyadic
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.timeSetoid
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.PositiveTimeValue
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.timeValue
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realValue
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realValue_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realValue_injective
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realTimeAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realTimeAction_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realTimeAction_dyadic
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realTimeAction_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realTimeAction_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realTimeAction_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins.realTimeAction_symmetric
