/-
# Positive-time Wilson insertions on the ORIGINAL witnessed sector

For a literal original Wilson multiplier M, the sandwich S(t) M S(t), t>0,
maps the witnessed continuous-time sector into itself. The intervening M
need not preserve that sector: its representative is propagated on the
ambient ORIGINAL carrier, and only the outer positive-time map supplies
range membership. Symmetry, real linearity and the original spin-only norm
cap are retained, with no new action or carrier.

Its vacuum-created state and integer-time lag remain pinned to the actual
Wilson loop and original correlator. This is a time-regularized insertion,
not a restriction of M, an observable-algebra homomorphism, physical-time
identification, or a continuum OS reconstruction.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeSector
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeVacuum
import YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum
import YMGap.Continuum.BF4WilsonAllNomePositiveTimePins

namespace YMGap.Continuum.BF4WilsonAllNomeSectorInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completedRealSmul)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum (completedMultiply_unitState)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity (lagMoment)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
  (positiveAction outputRepresentative outputRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (positiveAction_original)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeVacuum (positiveAction_unit)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure (positiveAction_range)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier (multiplierCap_nonnegative)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (dyadicTime)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "F" => positiveAction hw0 hw1
local notation "M" => completedMultiply hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- The literal time-regularized operator, on the unchanged ambient carrier. -/
def sandwich (time : PositiveTime) (loop : SourceLoop width) (spin : Nat) (x : V) : V :=
  F time (M loop spin (F time x))

/-- Construct the outer range witness by carrying the actual middle
multiplier representative. No sector invariance of M is assumed. -/
def sandwichRange (time : PositiveTime) (loop : SourceLoop width) (spin : Nat)
    (X : (D).Cauchy) : RangeLimit hw0 hw1 (sandwich hw0 hw1 time loop spin (Class X)) := by
  have h := positiveAction_range hw0 hw1 time
    (multiplyCauchy hw0 hw1 loop spin (outputRepresentative hw0 hw1 time X))
  change RangeLimit hw0 hw1
    (F time (M loop spin (Class (outputRepresentative hw0 hw1 time X)))) at h
  rw [outputRepresentative_pin] at h
  exact h

/-- An actual operator on the presented sector, pinned by its underlying val. -/
def insertion (time : PositiveTime) (loop : SourceLoop width) (spin : Nat)
    (x : State hw0 hw1 (width := width)) : State hw0 hw1 (width := width) where
  val := sandwich hw0 hw1 time loop spin x.val
  range := by
    have h := sandwichRange hw0 hw1 time loop spin (representative hw0 hw1 x.range)
    rwa [representative_pin] at h

theorem insertion_congr (time : PositiveTime) (loop : SourceLoop width) (spin : Nat)
    (x y : State hw0 hw1 (width := width)) (h : x.val = y.val) :
    (insertion hw0 hw1 time loop spin x).val = (insertion hw0 hw1 time loop spin y).val :=
  congrArg (sandwich hw0 hw1 time loop spin) h

theorem sandwich_add (time : PositiveTime) (loop : SourceLoop width) (spin : Nat)
    (x y : V) :
    sandwich hw0 hw1 time loop spin (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (sandwich hw0 hw1 time loop spin x)
        (sandwich hw0 hw1 time loop spin y) := by
  simp only [sandwich,positiveAction_add,completedMultiply_add]

theorem sandwich_realSmul (time : PositiveTime) (loop : SourceLoop width) (spin : Nat)
    (s : CReal) (cs : QCauchy s.approx) (x : V) :
    sandwich hw0 hw1 time loop spin (completedRealSmul hw0 hw1 s cs x) =
      completedRealSmul hw0 hw1 s cs (sandwich hw0 hw1 time loop spin x) := by
  simp only [sandwich,positiveAction_realSmul,completedMultiply_realSmul]

/-- Symmetry of the original sandwich; M need not be positive. -/
theorem sandwich_symmetric (time : PositiveTime) (loop : SourceLoop width) (spin : Nat)
    (x y : V) :
    B (sandwich hw0 hw1 time loop spin x) y = B x (sandwich hw0 hw1 time loop spin y) := by
  unfold sandwich
  rw [positiveAction_symmetric,completedInner_multiplier_balance,positiveAction_symmetric]

/-- The exact original spin-only squared-norm cap survives regularization. -/
theorem sandwich_norm_bound (time : PositiveTime) (loop : SourceLoop width) (spin : Nat)
    (x : V) :
    RCle (B (sandwich hw0 hw1 time loop spin x) (sandwich hw0 hw1 time loop spin x))
      (RCscale (characterBound spin) (B x x)) := by
  have hM := completedInner_multiplier_bound hw0 hw1 loop spin (F time x)
  change RCle _ (RCscale (characterBound spin) (B (F time x) (F time x))) at hM
  exact RCle_trans (positiveAction_norm_bound hw0 hw1 time (M loop spin (F time x)))
    (RCle_trans hM (RCscale_mono (multiplierCap_nonnegative spin)
      (positiveAction_norm_bound hw0 hw1 time x)))

/-- The created state is the original loop translated by the actual time. -/
theorem sandwich_unit (time : PositiveTime) (loop : SourceLoop width) :
    sandwich hw0 hw1 time loop 1 U = F time (embed hw0 hw1 (loopState loop)) := by
  unfold sandwich
  rw [positiveAction_unit,completedMultiply_unitState]

/-- One positive original integer time keeps the literal Wilson transfer. -/
theorem sandwich_unit_original (loop : SourceLoop width) (n : Nat) (hn : 0 < n) :
    sandwich hw0 hw1 (dyadicTime ⟨0,n⟩ hn) loop 1 U =
      T n (embed hw0 hw1 (loopState loop)) := by
  rw [sandwich_unit,positiveAction_original]

/-- Exact SAME-object autocorrelation at every original integer lag.
Both external time shifts contribute; no norm or normalization is replaced. -/
theorem sandwich_unit_lag (loop : SourceLoop width) (n : Nat) (hn : 0 < n) (lag : Nat) :
    B (sandwich hw0 hw1 (dyadicTime ⟨0,n⟩ hn) loop 1 U)
      (T lag (sandwich hw0 hw1 (dyadicTime ⟨0,n⟩ hn) loop 1 U)) =
      Quotient.mk crealSetoid (lagMoment hw0 hw1 loop ((n+lag)+n)) := by
  rw [sandwich_unit_original,completedInner_time_balance,
    ← completedTime_add,← completedTime_add]
  exact completedTime_loop_lag hw0 hw1 loop ((n+lag)+n)

#print axioms sandwich
#print axioms sandwichRange
#print axioms insertion
#print axioms insertion_congr
#print axioms sandwich_add
#print axioms sandwich_realSmul
#print axioms sandwich_symmetric
#print axioms sandwich_norm_bound
#print axioms sandwich_unit
#print axioms sandwich_unit_original
#print axioms sandwich_unit_lag

end YMGap.Continuum.BF4WilsonAllNomeSectorInsertion
