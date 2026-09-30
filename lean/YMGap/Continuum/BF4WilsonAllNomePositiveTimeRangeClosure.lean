/-
# Positive dyadic images lie in the original witnessed time range

Every positive mesh step has a final root applied to a supplied original
representative, so the fixed-root range witness applies directly.  Positive
real-time images are limits of these same pinned rows, and the existing
constructive closedness theorem preserves their range witnesses.  This is a
fixed-nome, fixed-width statement on the original completion; it retains the
ambient time kernel and makes no physical-time or scaling claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootTimeRange
import YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed

namespace YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint embed)
open YMGap.Constructive.DyadicTimeRationals (upper_steps_positive)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction action action_embed)
open YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives (meshRepresentative meshRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeRootTimeRange (rootRange)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
  (timeRows timeRows_pin positiveAction positiveAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (rowPoint)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
  (representedLimit representative representative_pin)
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime approximation sample)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "R" => root hw0 hw1
local notation "S" => meshAction hw0 hw1
local notation "A" => action hw0 hw1
local notation "Range" x => RangeLimit hw0 hw1 x

/-- A positive number of supplied mesh steps ends in an actual fixed-depth
root image of an original Cauchy representative. -/
def meshAction_range (depth steps : Nat) (X : (D).Cauchy)
    (hsteps : 0 < steps) :
    Range (S depth steps (Class X)) := by
  cases steps with
  | zero => omega
  | succ n =>
      let Y := meshRepresentative hw0 hw1 depth n X
      have hpin : Class Y = S depth n (Class X) :=
        meshRepresentative_pin hw0 hw1 depth n X
      have htarget : S depth (n + 1) (Class X) = R depth (Class Y) := by
        change R depth (S depth n (Class X)) = R depth (Class Y)
        rw [hpin]
      rw [htarget]
      exact rootRange hw0 hw1 depth Y

/-- Every supplied positive dyadic action on an original represented input
has an explicit original-time-range witness. -/
def dyadicAction_range (p : MeshPoint) (X : (D).Cauchy)
    (hsteps : 0 < p.steps) :
    Range (A (embed p) (Class X)) := by
  rw [action_embed]
  exact meshAction_range hw0 hw1 p.depth p.steps X hsteps

/-- Every strictly-positive represented real-time action remains in the
existing witnessed range sector, with the original row representatives and
moduli propagated through its actual limit. -/
def positiveAction_range (time : PositiveTime) (X : (D).Cauchy) :
    Range (positiveAction hw0 hw1 time (Class X)) := by
  have hrows : ∀ n, Range (rowPoint hw0 hw1 (timeRows hw0 hw1 time X) n) := by
    intro n
    rw [timeRows_pin]
    exact dyadicAction_range hw0 hw1 (approximation time n) X
      (upper_steps_positive (sample time n) n)
  rw [positiveAction_pin]
  exact representedLimit hw0 hw1 (timeRows hw0 hw1 time X) hrows

/-- Sector invariance needs no additional input representative: the
supplied range witness itself computes one. -/
def positiveAction_preservesRange (time : PositiveTime) {x : V}
    (witness : Range x) : Range (positiveAction hw0 hw1 time x) := by
  have h := positiveAction_range hw0 hw1 time (representative hw0 hw1 witness)
  rwa [representative_pin] at h

#print axioms meshAction_range
#print axioms dyadicAction_range
#print axioms positiveAction_range
#print axioms positiveAction_preservesRange

end YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure
