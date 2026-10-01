/-
# Positive time on the completed physical bond sources

The actual positive-time action on the original Wilson completion preserves
the witnessed time sector. Transport through the represented completion of
the physical odd-window bond sources therefore gives an action on that SAME
bond completion. Its source pin is the original one-step geometric advance.
This is fixed-nome, fixed-width dimensionless time; no time-zero observable
algebra, continuum OS root, or physical calibration is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeComposition
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeVacuum
import YMGap.Continuum.BF4WilsonAllNomePositiveTimePins

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.PositiveRealDyadicTimeAddition (sumTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (dyadicTime)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner unitState)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure
  (positiveAction_preservesRange)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeComposition (positiveAction_sum)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws (positiveAction_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeVacuum (positiveAction_unit)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (positiveAction_original)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State stateSetoid)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion SectorQuotient toSector fromSector toSector_fromSector
    fromSector_toSector bondCompletedDistance bondCompletedInner sectorDistance ofSource
    constantRows constantRows_limit)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization
  (image image_advance image_unit)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "F" => positiveAction hw0 hw1

/-- The original completed vector underlying a witnessed sector class. -/
def sectorValue : SectorQuotient hw0 hw1 (width := width) → V :=
  Quotient.lift (fun x => x.val) (fun _ _ h => h)

/-- The original completed vector realized by a physical bond Cauchy class. -/
def bondValue (z : BondCompletion hw0 hw1 (width := width)) : V :=
  sectorValue hw0 hw1 (toSector hw0 hw1 z)

theorem sectorValue_injective {x y : SectorQuotient hw0 hw1 (width := width)}
    (h : sectorValue hw0 hw1 x = sectorValue hw0 hw1 y) : x = y := by
  revert h
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      intro h
      exact Quotient.sound h

theorem bondValue_injective {x y : BondCompletion hw0 hw1 (width := width)}
    (h : bondValue hw0 hw1 x = bondValue hw0 hw1 y) : x = y := by
  have hs : toSector hw0 hw1 x = toSector hw0 hw1 y :=
    sectorValue_injective hw0 hw1 h
  calc
    x = fromSector hw0 hw1 (toSector hw0 hw1 x) :=
      (fromSector_toSector hw0 hw1 x).symm
    _ = fromSector hw0 hw1 (toSector hw0 hw1 y) := congrArg _ hs
    _ = y := fromSector_toSector hw0 hw1 y

/-- Preserve the supplied Type-valued range witness before quotienting. -/
def sectorActionRep (time : PositiveTime)
    (x : State hw0 hw1 (width := width)) : State hw0 hw1 (width := width) where
  val := F time x.val
  range := positiveAction_preservesRange hw0 hw1 time x.range

def sectorAction (time : PositiveTime) :
    SectorQuotient hw0 hw1 (width := width) →
      SectorQuotient hw0 hw1 (width := width) :=
  Quotient.lift
    (fun x => Quotient.mk (stateSetoid hw0 hw1)
      (sectorActionRep hw0 hw1 time x))
    (fun _ _ h => Quotient.sound (congrArg (F time) h))

theorem sectorValue_action (time : PositiveTime)
    (x : SectorQuotient hw0 hw1 (width := width)) :
    sectorValue hw0 hw1 (sectorAction hw0 hw1 time x) =
      F time (sectorValue hw0 hw1 x) := by
  induction x using Quotient.inductionOn with
  | h a => rfl

/-- The physical bond action uses no new completion or chosen preimage. -/
def bondAction (time : PositiveTime)
    (z : BondCompletion hw0 hw1 (width := width)) :
    BondCompletion hw0 hw1 (width := width) :=
  fromSector hw0 hw1 (sectorAction hw0 hw1 time (toSector hw0 hw1 z))

theorem toSector_bondAction (time : PositiveTime)
    (z : BondCompletion hw0 hw1 (width := width)) :
    toSector hw0 hw1 (bondAction hw0 hw1 time z) =
      sectorAction hw0 hw1 time (toSector hw0 hw1 z) :=
  toSector_fromSector hw0 hw1 _

theorem bondAction_value (time : PositiveTime)
    (z : BondCompletion hw0 hw1 (width := width)) :
    bondValue hw0 hw1 (bondAction hw0 hw1 time z) =
      F time (bondValue hw0 hw1 z) := by
  rw [bondValue, toSector_bondAction, sectorValue_action]
  rfl

theorem bondValue_distance (x y : BondCompletion hw0 hw1 (width := width)) :
    bondCompletedDistance hw0 hw1 x y =
      completedDist hw0 hw1 (bondValue hw0 hw1 x) (bondValue hw0 hw1 y) := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b => rfl

theorem bondValue_inner (x y : BondCompletion hw0 hw1 (width := width)) :
    bondCompletedInner hw0 hw1 x y =
      completedInner hw0 hw1 (bondValue hw0 hw1 x) (bondValue hw0 hw1 y) := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b => rfl

theorem bondAction_sum (s t : PositiveTime)
    (z : BondCompletion hw0 hw1 (width := width)) :
    bondAction hw0 hw1 (sumTime s t) z =
      bondAction hw0 hw1 s (bondAction hw0 hw1 t z) := by
  apply bondValue_injective hw0 hw1
  rw [bondAction_value, bondAction_value, bondAction_value]
  exact positiveAction_sum hw0 hw1 s t (bondValue hw0 hw1 z)

theorem bondAction_distance_bound (time : PositiveTime)
    (x y : BondCompletion hw0 hw1 (width := width)) :
    RCle (bondCompletedDistance hw0 hw1
      (bondAction hw0 hw1 time x) (bondAction hw0 hw1 time y))
      (bondCompletedDistance hw0 hw1 x y) := by
  rw [bondValue_distance, bondValue_distance]
  rw [bondAction_value, bondAction_value]
  exact positiveAction_distance_bound hw0 hw1 time _ _

def vacuum : BondCompletion hw0 hw1 (width := width) :=
  ofSource hw0 hw1 (unit width)

theorem bondValue_ofSource (x : IntrinsicExpression width) :
    bondValue hw0 hw1 (ofSource hw0 hw1 x) = (image hw0 hw1 x).val :=
  constantRows_limit hw0 hw1 x

theorem bondAction_vacuum (time : PositiveTime) :
    bondAction hw0 hw1 time (vacuum hw0 hw1 (width := width)) =
      vacuum hw0 hw1 (width := width) := by
  apply bondValue_injective hw0 hw1
  rw [bondAction_value, vacuum, bondValue_ofSource, image_unit,
    positiveAction_unit]

/-- The positive time-one operator agrees with the original finite-source
geometric advance after the physical bond-null completion. -/
theorem bondAction_ofSource_one (x : IntrinsicExpression width) :
    bondAction hw0 hw1 (dyadicTime ⟨0,1⟩ (Nat.succ_pos 0))
      (ofSource hw0 hw1 x) = ofSource hw0 hw1 (advance 1 x) := by
  apply bondValue_injective hw0 hw1
  rw [bondAction_value, bondValue_ofSource, bondValue_ofSource,
    positiveAction_original hw0 hw1 1 (Nat.succ_pos 0)]
  exact (image_advance hw0 hw1 x).symm

#print axioms sectorValue
#print axioms bondValue
#print axioms sectorValue_injective
#print axioms bondValue_injective
#print axioms sectorActionRep
#print axioms sectorAction
#print axioms sectorValue_action
#print axioms bondAction
#print axioms toSector_bondAction
#print axioms bondAction_value
#print axioms bondValue_distance
#print axioms bondValue_inner
#print axioms bondAction_sum
#print axioms bondAction_distance_bound
#print axioms vacuum
#print axioms bondValue_ofSource
#print axioms bondAction_vacuum
#print axioms bondAction_ofSource_one

end YMGap.Continuum.BF4WilsonAllNomeBondOSTime
