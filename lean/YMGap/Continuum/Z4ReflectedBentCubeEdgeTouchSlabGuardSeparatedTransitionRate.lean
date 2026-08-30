/-
# The explicit three-factor separated-transition rate

The guarded route has three independent quantitative payments:

* the complete canonical-peeling inverse-fiber rate;
* the cutoff-uniform guarded insertion rate; and
* the quarter-mass separated recoupling cylinder.

This module contracts those payments into one explicit positive rational and
proves the exact finite inequality that turns the three hypotheses into a
separated joint-transition lower bound.

Constructive contract: exact rational order and previously constructed rates
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRateCutoffUniform
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderSeparatedEvent

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionRate

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRate
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRateCutoffUniform

local infix:50 " ≈ " => Q'.eqv

/-- The uncapped product of separated cylinder mass, insertion payment, and
complete peeling payment. -/
def reflectedBentGuardRawSeparatedTransitionRate
    (coupling : Q') (faces : List Nat) : Q' :=
  oneQuarter *
    (reflectedBentGuardCutoffUniformInsertionRate coupling *
      pairedPeelProfilePaymentRate faces)

/-- The unit-capped separated-transition candidate. -/
def reflectedBentGuardSeparatedTransitionRate
    (coupling : Q') (faces : List Nat) : Q' :=
  capAtOne (reflectedBentGuardRawSeparatedTransitionRate coupling faces)

theorem reflectedBentGuardRawSeparatedTransitionRate_pos
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (faces : List Nat) :
    (0 : Q') < reflectedBentGuardRawSeparatedTransitionRate coupling faces :=
  Q'.mul_pos (by decide)
    (Q'.mul_pos
      (reflectedBentGuardCutoffUniformInsertionRate_pos coupling hcoupling)
      (pairedPeelProfilePaymentRate_pos faces))

theorem reflectedBentGuardSeparatedTransitionRate_pos
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (faces : List Nat) :
    (0 : Q') < reflectedBentGuardSeparatedTransitionRate coupling faces :=
  capAtOne_pos
    (reflectedBentGuardRawSeparatedTransitionRate_pos
      coupling hcoupling faces)

theorem reflectedBentGuardSeparatedTransitionRate_le_one
    (coupling : Q') (faces : List Nat) :
    reflectedBentGuardSeparatedTransitionRate coupling faces ≤ (1 : Q') :=
  capAtOne_le_one _

private theorem three_factor_separated_joint_bound
    (first second third rate sourceMass terminalWeight
      receiverWeight eventMass : Q')
    (first_nonnegative : (0 : Q') ≤ first)
    (second_nonnegative : (0 : Q') ≤ second)
    (sourceMass_nonnegative : (0 : Q') ≤ sourceMass)
    (receiverWeight_nonnegative : (0 : Q') ≤ receiverWeight)
    (rate_le : rate ≤ first * (second * third))
    (third_payment : third * sourceMass ≤ terminalWeight)
    (second_payment : second * terminalWeight ≤ receiverWeight)
    (first_event_floor : first ≤ eventMass) :
    rate * sourceMass ≤ receiverWeight * eventMass := by
  have hrateScaled := Q'.mul_le_mul_of_nonneg_right _ _ sourceMass
    rate_le sourceMass_nonnegative
  have hthirdScaled := Q'.mul_le_mul_of_nonneg_left _ _ second
    third_payment second_nonnegative
  have hsecond : second * (third * sourceMass) ≤ receiverWeight :=
    Q'.le_trans' _ _ _ hthirdScaled second_payment
  have hfirstScaled := Q'.mul_le_mul_of_nonneg_left _ _ first
    hsecond first_nonnegative
  have heventScaled := Q'.mul_le_mul_of_nonneg_left _ _ receiverWeight
    first_event_floor receiverWeight_nonnegative
  exact Q'.le_trans' _ _ _ hrateScaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv first (second * third) sourceMass)
          (Q'.mul_eqv_congr_left first _ _
            (Q'.mul_assoc_eqv second third sourceMass))))
      (Q'.le_trans' _ _ _ hfirstScaled
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_comm_eqv first receiverWeight))
          heventScaled)))

/-- **Three quantitative payments give one separated joint-transition
floor.**  This is the exact algebra needed after the concrete carrier maps
identify `sourceMass`, `terminalWeight`, `receiverWeight`, and `eventMass`. -/
theorem reflectedBentGuardSeparatedTransitionRate_mul_sourceMass_le_joint
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (faces : List Nat)
    (sourceMass terminalWeight receiverWeight eventMass : Q')
    (sourceMass_nonnegative : (0 : Q') ≤ sourceMass)
    (receiverWeight_nonnegative : (0 : Q') ≤ receiverWeight)
    (peeling_payment : pairedPeelProfilePaymentRate faces * sourceMass ≤
      terminalWeight)
    (insertion_payment :
      reflectedBentGuardCutoffUniformInsertionRate coupling *
        terminalWeight ≤ receiverWeight)
    (separated_event_floor : oneQuarter ≤ eventMass) :
    reflectedBentGuardSeparatedTransitionRate coupling faces * sourceMass ≤
      receiverWeight * eventMass := by
  apply three_factor_separated_joint_bound
    oneQuarter
    (reflectedBentGuardCutoffUniformInsertionRate coupling)
    (pairedPeelProfilePaymentRate faces)
    (reflectedBentGuardSeparatedTransitionRate coupling faces)
    sourceMass terminalWeight receiverWeight eventMass
  · decide
  · exact Q'.le_of_lt
      (reflectedBentGuardCutoffUniformInsertionRate_pos coupling hcoupling)
  · exact sourceMass_nonnegative
  · exact receiverWeight_nonnegative
  · unfold reflectedBentGuardSeparatedTransitionRate
      reflectedBentGuardRawSeparatedTransitionRate
    exact capAtOne_le _
  · exact peeling_payment
  · exact insertion_payment
  · exact separated_event_floor

#print axioms reflectedBentGuardRawSeparatedTransitionRate_pos
#print axioms reflectedBentGuardSeparatedTransitionRate_pos
#print axioms reflectedBentGuardSeparatedTransitionRate_le_one
#print axioms reflectedBentGuardSeparatedTransitionRate_mul_sourceMass_le_joint

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionRate
