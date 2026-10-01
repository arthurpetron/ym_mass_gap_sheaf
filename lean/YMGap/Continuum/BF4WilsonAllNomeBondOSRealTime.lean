/-
# Numerical real time on the physical bond completion

The original time action descends to numerical positive real values on the
completed odd-window bond sources. Composition, symmetry, contraction and
the vacuum are preserved on that SAME completion. Time one is the original
geometric source advance.

Every represented bond state supplies a positive rational zero-continuity
radius, computed from its own Cauchy rows and the existing range witness.
The same radius controls forward time increments at every positive time.
No representative is selected from a quotient to compute a modulus.
All times are dimensionless at fixed nome and width. No spatial/scaling
uniformity, physical mass calibration or continuum QFT is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSTime
import YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeRealContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue realValue dyadicTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup (addTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
  (positiveAction_time_congr realTimeAction realTimeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup
  (realTimeAction_symmetric realTimeAction_nonnegative realTimeAction_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion Rows rowSetoid toSectorRep bondCompletedDistance
    bondCompletedInner ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_distance bondValue_inner
    bondAction bondAction_value bondAction_sum bondAction_distance_bound
    vacuum bondAction_vacuum bondAction_ofSource_one)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeRealContinuity
  (realRadius realRadius_positive real_smallTime)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "dist" => bondCompletedDistance hw0 hw1
local notation "B" => bondCompletedInner hw0 hw1
local notation "Class" => Quotient.mk (rowSetoid hw0 hw1 (width := width))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem bondAction_time_congr (s t : PositiveTime)
    (h : Equiv s.real t.real) (x : H) :
    bondAction hw0 hw1 s x = bondAction hw0 hw1 t x := by
  apply bondValue_injective hw0 hw1
  rw [bondAction_value, bondAction_value]
  exact positiveAction_time_congr hw0 hw1 s t h _

/-- Quotient only the output state; range data were constructed beforehand. -/
def action (t : PositiveTimeValue) (x : H) : H :=
  Quotient.lift (fun time => bondAction hw0 hw1 time x)
    (fun s u h => bondAction_time_congr hw0 hw1 s u h x) t

theorem action_pin (time : PositiveTime) (x : H) :
    action hw0 hw1 (timeValue time) x = bondAction hw0 hw1 time x := rfl

/-- Exact identification with the original completed operator. -/
theorem action_value (t : PositiveTimeValue) (x : H) :
    bondValue hw0 hw1 (action hw0 hw1 t x) =
      realTimeAction hw0 hw1 t (bondValue hw0 hw1 x) := by
  refine Quotient.inductionOn t ?_
  intro time
  exact bondAction_value hw0 hw1 time x

theorem action_addTime (s t : PositiveTimeValue) (x : H) :
    action hw0 hw1 (addTime s t) x =
      action hw0 hw1 s (action hw0 hw1 t x) := by
  refine Quotient.inductionOn₂ s t ?_
  intro S T
  exact bondAction_sum hw0 hw1 S T x

theorem action_distance_bound (t : PositiveTimeValue) (x y : H) :
    RCle (dist (action hw0 hw1 t x) (action hw0 hw1 t y)) (dist x y) := by
  refine Quotient.inductionOn t ?_
  intro time
  exact bondAction_distance_bound hw0 hw1 time x y

theorem action_symmetric (t : PositiveTimeValue) (x y : H) :
    B (action hw0 hw1 t x) y = B x (action hw0 hw1 t y) := by
  rw [bondValue_inner, bondValue_inner, action_value, action_value]
  exact realTimeAction_symmetric hw0 hw1 t _ _

theorem action_nonnegative (t : PositiveTimeValue) (x : H) :
    RCnonneg (B x (action hw0 hw1 t x)) := by
  rw [bondValue_inner, action_value]
  exact realTimeAction_nonnegative hw0 hw1 t _

theorem action_norm_bound (t : PositiveTimeValue) (x : H) :
    RCle (B (action hw0 hw1 t x) (action hw0 hw1 t x)) (B x x) := by
  rw [bondValue_inner, bondValue_inner, action_value]
  exact realTimeAction_norm_bound hw0 hw1 t _

theorem action_vacuum (t : PositiveTimeValue) :
    action hw0 hw1 t (vacuum hw0 hw1 (width := width)) =
      vacuum hw0 hw1 (width := width) := by
  refine Quotient.inductionOn t ?_
  intro time
  exact bondAction_vacuum hw0 hw1 time

theorem action_ofSource_one (x : IntrinsicExpression width) :
    action hw0 hw1 (timeValue (dyadicTime ⟨0,1⟩ (Nat.succ_pos 0)))
      (ofSource hw0 hw1 x) = ofSource hw0 hw1 (advance 1 x) :=
  bondAction_ofSource_one hw0 hw1 x

/-- An explicit radius for each represented bond state, not quotient choice. -/
def continuityRadius (X : Rows hw0 hw1 (width := width)) (e : Q') : Q' :=
  realRadius hw0 hw1 (toSectorRep hw0 hw1 X).range e

theorem continuityRadius_positive (X : Rows hw0 hw1 (width := width)) (e : Q') :
    (0 : Q') < continuityRadius hw0 hw1 X e :=
  realRadius_positive hw0 hw1 (toSectorRep hw0 hw1 X).range e

theorem action_smallTime (X : Rows hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) (t : PositiveTimeValue)
    (ht : RCle (realValue t) (rat (continuityRadius hw0 hw1 X e))) :
    RCle (dist (action hw0 hw1 t (Class X)) (Class X)) (rat e) := by
  revert ht
  refine Quotient.inductionOn t ?_
  intro time ht
  rw [bondValue_distance, action_value]
  exact real_smallTime hw0 hw1 (toSectorRep hw0 hw1 X).range e he time ht

/-- The original Cauchy rows supply the continuity data as a Type-level value. -/
def continuityCertificate (X : Rows hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveTimeValue, RCle (realValue t) (rat r) →
        RCle (dist (action hw0 hw1 t (Class X)) (Class X)) (rat e)) :=
  ⟨continuityRadius hw0 hw1 X e, continuityRadius_positive hw0 hw1 X e,
    action_smallTime hw0 hw1 X e he⟩

/-- Contraction propagates the same represented radius to every forward
increment. It is not a rate uniform in nome, width or represented state. -/
theorem action_smallIncrement (X : Rows hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) (s t : PositiveTimeValue)
    (ht : RCle (realValue t) (rat (continuityRadius hw0 hw1 X e))) :
    RCle (dist (action hw0 hw1 (addTime s t) (Class X))
      (action hw0 hw1 s (Class X))) (rat e) := by
  rw [action_addTime]
  exact RCle_trans (action_distance_bound hw0 hw1 s _ _)
    (action_smallTime hw0 hw1 X e he t ht)

#print axioms bondAction_time_congr
#print axioms action
#print axioms action_pin
#print axioms action_value
#print axioms action_addTime
#print axioms action_distance_bound
#print axioms action_symmetric
#print axioms action_nonnegative
#print axioms action_norm_bound
#print axioms action_vacuum
#print axioms action_ofSource_one
#print axioms continuityRadius
#print axioms continuityRadius_positive
#print axioms action_smallTime
#print axioms continuityCertificate
#print axioms action_smallIncrement

end YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime
