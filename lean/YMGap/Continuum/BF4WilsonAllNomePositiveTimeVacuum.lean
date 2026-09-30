/-
# Positive real time fixes the original Wilson vacuum

The finite dyadic actions fix the normalized unit because their increments
are controlled by the actual derivative image of that unit, which vanishes.
The supplied positive-time rows therefore have the same limit as constant
unit rows. Symmetry then gives preservation of the original vacuum pairing
and its orthogonal complement. No OS, physical-time or scaling statement is
made.
-/

import YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
import YMGap.Continuum.BF4WilsonAllNomeDerivativeIncrement
import YMGap.Continuum.BF4WilsonAllNomeDerivativeCore
import YMGap.Continuum.BF4WilsonAllNomeUnitProjection
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

namespace YMGap.Continuum.BF4WilsonAllNomePositiveTimeVacuum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (embed)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction action_embed)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
  (positiveAction_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeIncrement (mesh_increment_bound)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeCore (derivativeAction_unit_zero)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection (unitCauchy)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
  (constantRows limit_constantRows)
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime approximation)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "S" => meshAction hw0 hw1
local notation "F" => positiveAction hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- Every positive finite mesh action fixes the unit of the original
completion. The proof uses the actual original increment estimate. -/
theorem meshAction_unit (depth steps : Nat) : S depth steps U = U := by
  have hi := mesh_increment_bound hw0 hw1 depth steps U
  rw [completedUnit_fixed hw0 hw1 1, derivativeAction_unit_zero] at hi
  rw [completedInner_zero_left, RCscale_RCzero] at hi
  have hz : completedDist hw0 hw1 U (S depth steps U) = RCzero :=
    RCle_antisymm hi (completedDist_nonnegative hw0 hw1 U (S depth steps U))
  exact ((completedDist_zero_iff hw0 hw1 U (S depth steps U)).mp hz).symm

/-- The constructed positive-real action fixes the same original unit. -/
theorem positiveAction_unit (time : PositiveTime) : F time U = U := by
  let X : (D).Cauchy := unitCauchy hw0 hw1
  have hclass : Class X = U := rfl
  have hrows : ∀ n, rowPoint hw0 hw1 (timeRows hw0 hw1 time X) n = U := by
    intro n
    rw [timeRows_pin, action_embed, hclass]
    exact meshAction_unit hw0 hw1 (approximation time n).depth
      (approximation time n).steps
  have h := limit_independent hw0 hw1 (timeRows hw0 hw1 time X)
    (constantRows hw0 hw1 X) hrows
  rw [limit_constantRows] at h
  rw [← hclass, positiveAction_pin]
  exact h

/-- The original unit pairing is preserved by every strictly positive real
time action on the same completion. -/
theorem positiveAction_vacuum_pairing (time : PositiveTime) (x : V) :
    B U (F time x) = B U x := by
  calc
    B U (F time x) = B (F time x) U :=
      completedInner_symm hw0 hw1 U (F time x)
    _ = B x (F time U) := positiveAction_symmetric hw0 hw1 time x U
    _ = B x U := congrArg (B x) (positiveAction_unit hw0 hw1 time)
    _ = B U x := completedInner_symm hw0 hw1 x U

/-- The existing vacuum-orthogonal subspace is preserved; this asserts no
identification with a reflected OS carrier. -/
theorem positiveAction_preserves_vacuum_complement (time : PositiveTime) (x : V)
    (h : B U x = RCzero) :
    B U (F time x) = RCzero := by
  rw [positiveAction_vacuum_pairing hw0 hw1 time x]
  exact h

#print axioms meshAction_unit
#print axioms positiveAction_unit
#print axioms positiveAction_vacuum_pairing
#print axioms positiveAction_preserves_vacuum_complement

end YMGap.Continuum.BF4WilsonAllNomePositiveTimeVacuum
