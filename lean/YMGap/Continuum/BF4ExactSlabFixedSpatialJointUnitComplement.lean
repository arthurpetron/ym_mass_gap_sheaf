/-
# The invariant unit-orthogonal sector of the actual joint completion

Physical time balance passes through the actual representative pairing
limits. Since the same completed unit is fixed, its orthogonal complement
is preserved by every discrete physical advance. Restricting the existing
time semigroup to that subtype preserves its zero and addition laws.

The previously proved completed two-step form bound restricts directly to
this sector with the SAME nome/width-dependent q^2<1. Time balance also
identifies this with a one-step squared-norm bound; it does not make the
one-step map positive. No new Hilbert, positive-definiteness, representative
choice, metric-completeness or continuum premise is introduced.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm (jointSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap
  (completed_twoStep_form_gap completed_even_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width

/-- The same actual scalar pairing limits retain finite physical-time
balance on every pair of supplied Cauchy representatives. -/
theorem representativeInner_time_balance (n : Nat) (X Y : (D).Cauchy) :
    Equiv
      (representativeInner hw0 hw1 width
        ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy X) Y)
      (representativeInner hw0 hw1 width X
        ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy Y)) :=
  Equiv_of_limit_of_equal
    (fun k => jointPairing_time_balance hw0 hw1 width n (X.seq k) (Y.seq k))
    (pairSequence_converges hw0 hw1 width
      ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy X) Y)
    (pairSequence_converges hw0 hw1 width X
      ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy Y))

theorem completedInner_time_balance (n : Nat) (x y : JointCompletion hw0 hw1 width) :
    B (T n x) y = B x (T n y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_time_balance hw0 hw1 width n X Y)

/-- Unit coefficients are invariant because the actual completed unit is
fixed and the actual completed pairing satisfies time balance. -/
theorem completedUnitCoefficient_time (n : Nat) (x : JointCompletion hw0 hw1 width) :
    B (T n x) U = B x U := by
  rw [completedInner_time_balance, jointCompletedUnit_fixed]

theorem completedTime_preserves_orthogonal (n : Nat)
    (x : JointCompletion hw0 hw1 width) (hx : B x U = RCzero) :
    B (T n x) U = RCzero :=
  (completedUnitCoefficient_time hw0 hw1 width n x).trans hx

/-- The unit-orthogonal sector of the SAME joint completion and pairing. -/
def UnitComplement : Type :=
  {x : JointCompletion hw0 hw1 width // B x U = RCzero}

def unitComplementTime (n : Nat) (x : UnitComplement hw0 hw1 width) :
    UnitComplement hw0 hw1 width :=
  ⟨T n x.val, completedTime_preserves_orthogonal hw0 hw1 width n x.val x.property⟩

theorem unitComplementTime_val (n : Nat) (x : UnitComplement hw0 hw1 width) :
    (unitComplementTime hw0 hw1 width n x).val = T n x.val := rfl

theorem unitComplementTime_zero (x : UnitComplement hw0 hw1 width) :
    unitComplementTime hw0 hw1 width 0 x = x :=
  Subtype.ext (jointCompletedTime_zero hw0 hw1 width x.val)

theorem unitComplementTime_add (m n : Nat) (x : UnitComplement hw0 hw1 width) :
    unitComplementTime hw0 hw1 width (m+n) x =
      unitComplementTime hw0 hw1 width m (unitComplementTime hw0 hw1 width n x) :=
  Subtype.ext (jointCompletedTime_add hw0 hw1 width m n x.val)

/-- The canonical even-time transfer on this sector. Its form positivity is
the n=1 case of unitComplement_even_nonnegative below. -/
def twoStepTransfer (x : UnitComplement hw0 hw1 width) : UnitComplement hw0 hw1 width :=
  unitComplementTime hw0 hw1 width 2 x

/-- The strict form bound is inherited, with the original twoStepRate q^2.
Its nonnegativity and strict inequality below one are already proved in
DenseCenteredGap; neither is a new premise here. -/
theorem unitComplement_twoStep_form_gap (x : UnitComplement hw0 hw1 width) :
    RCle (B x.val (unitComplementTime hw0 hw1 width 2 x).val)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width)))
        (B x.val x.val)) :=
  completed_twoStep_form_gap hw0 hw1 width x.val x.property

/-- Site-reflected positivity is retained at even physical time only. -/
theorem unitComplement_even_nonnegative (n : Nat) (x : UnitComplement hw0 hw1 width) :
    RCnonneg (B x.val (unitComplementTime hw0 hw1 width (2*n) x).val) :=
  completed_even_nonnegative hw0 hw1 width n x.val x.property

/-- Time balance turns the two-step form bound into a strict one-step
squared-norm bound, without asserting positivity of one-step time. -/
theorem unitComplement_oneStep_norm_gap (x : UnitComplement hw0 hw1 width) :
    RCle (B (unitComplementTime hw0 hw1 width 1 x).val
        (unitComplementTime hw0 hw1 width 1 x).val)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width)))
        (B x.val x.val)) := by
  have hdiag : B (T 1 x.val) (T 1 x.val) = B x.val (T 2 x.val) :=
    (completedInner_time_balance hw0 hw1 width 1 x.val (T 1 x.val)).trans
      (congrArg (fun y => B x.val y) (jointCompletedTime_add hw0 hw1 width 1 1 x.val).symm)
  change RCle (B (T 1 x.val) (T 1 x.val))
    (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width))) (B x.val x.val))
  rw [hdiag]
  exact completed_twoStep_form_gap hw0 hw1 width x.val x.property

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.representativeInner_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.completedInner_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.completedUnitCoefficient_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.completedTime_preserves_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.UnitComplement
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.unitComplementTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.unitComplementTime_val
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.unitComplementTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.unitComplementTime_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.twoStepTransfer
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.unitComplement_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.unitComplement_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement.unitComplement_oneStep_norm_gap
