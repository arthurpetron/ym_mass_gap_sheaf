/-
# Inverse-square route for matched dynamic correlated capacity debt

The matched correlated frontier is one antitone tail control for the exact
total deficit.  This module gives it a concrete analytic shape: an offset
`B >= 2`, a nonnegative rational coefficient `A`, and the pointwise estimate

  totalDeficit(k) <= A / (k + B)^2.

The existing constructive inverse-square compiler then supplies the antitone
tail modulus.  A second interface preserves four-way analytic parallelism:
the transported-old and three shell-face deficits may be bounded separately
with a common offset, and their coefficients add to the one total bound.

No inverse-square estimate is inhabited.  No tail allowance, initial closure,
continuum theory, or Clay conclusion is supplied.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
import YMGap.Continuum.InverseSquareAntitoneTailControl

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.InverseSquareAntitoneTailControl
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add_local
    {a b c d : Q'} (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem four_coefficient_products_eqv
    (first second third fourth term : Q') :
    first * term +
        (second * term + (third * term + fourth * term)) ≈
      (first + (second + (third + fourth))) * term := by
  have hthirdFourth :
      (third + fourth) * term ≈ third * term + fourth * term :=
    Q'.add_mul_eqv third fourth term
  have hsecondRest :
      (second + (third + fourth)) * term ≈
        second * term + (third * term + fourth * term) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv second (third + fourth) term)
      (Q'.add_eqv_congr_left (second * term)
        ((third + fourth) * term)
        (third * term + fourth * term) hthirdFourth)
  have hall :
      (first + (second + (third + fourth))) * term ≈
        first * term +
          (second * term + (third * term + fourth * term)) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv first (second + (third + fourth)) term)
      (Q'.add_eqv_congr_left (first * term)
        ((second + (third + fourth)) * term)
        (second * term + (third * term + fourth * term)) hsecondRest)
  exact Q'.eqv_symm hall

/-! ## 1. One inverse-square estimate constructs the serial total tail -/

structure MatchedEventualCanonicalCapacityDebtInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  totalDeficit_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalCapacityDebtTotalDeficit
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalCapacityDebtInverseSquareControl.toTotalDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control : MatchedEventualCanonicalCapacityDebtInverseSquareControl
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale where
  tailControl := inverseSquareTermTailControl
    (matchedEventualCanonicalCapacityDebtTotalDeficit
      trajectory transitionStart physicalScale)
    control.offset control.offset_at_least_two
    control.coefficient control.coefficient_nonnegative
    control.totalDeficit_le

/-! ## 2. Four regional inverse-square estimates rejoin the same total -/

structure MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  transportCoefficient : Q'
  oldNewCoefficient : Q'
  newOldCoefficient : Q'
  newNewCoefficient : Q'
  transportCoefficient_nonnegative :
    (0 : Q') <= transportCoefficient
  oldNewCoefficient_nonnegative :
    (0 : Q') <= oldNewCoefficient
  newOldCoefficient_nonnegative :
    (0 : Q') <= newOldCoefficient
  newNewCoefficient_nonnegative :
    (0 : Q') <= newNewCoefficient
  transport_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      transportCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  oldNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      oldNewCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  newOld_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newOldCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  newNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newNewCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl.totalCoefficient
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control : MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl
      trajectory transitionStart physicalScale) : Q' :=
  control.transportCoefficient +
    (control.oldNewCoefficient +
      (control.newOldCoefficient + control.newNewCoefficient))

theorem MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl.totalCoefficient_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control : MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl
      trajectory transitionStart physicalScale) :
    (0 : Q') <= control.totalCoefficient := by
  unfold totalCoefficient
  exact Q'.zero_le_add _ _
    control.transportCoefficient_nonnegative
    (Q'.zero_le_add _ _
      control.oldNewCoefficient_nonnegative
      (Q'.zero_le_add _ _
        control.newOldCoefficient_nonnegative
        control.newNewCoefficient_nonnegative))

def MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl.toTotalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control : MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.totalCoefficient
  coefficient_nonnegative := control.totalCoefficient_nonnegative
  totalDeficit_le := by
    intro cutoffOffset
    let term := invSqTerm
      control.offset control.offset_at_least_two cutoffOffset
    have hregional :
        matchedEventualCanonicalCapacityDebtTotalDeficit
            trajectory transitionStart physicalScale cutoffOffset <=
          control.transportCoefficient * term +
            (control.oldNewCoefficient * term +
              (control.newOldCoefficient * term +
                control.newNewCoefficient * term)) := by
      unfold matchedEventualCanonicalCapacityDebtTotalDeficit
      exact add_le_add_local
        (control.transport_le cutoffOffset)
        (add_le_add_local
          (control.oldNew_le cutoffOffset)
          (add_le_add_local
            (control.newOld_le cutoffOffset)
            (control.newNew_le cutoffOffset)))
    exact Q'.le_trans' _ _ _ hregional
      (Q'.le_of_eqv
        (four_coefficient_products_eqv
          control.transportCoefficient control.oldNewCoefficient
          control.newOldCoefficient control.newNewCoefficient term))

def MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl.toTotalDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control : MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale :=
  control.toTotalControl.toTotalDeficitTail

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail.MatchedEventualCanonicalCapacityDebtInverseSquareControl.toTotalDeficitTail
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail.MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl.totalCoefficient_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail.MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl.toTotalControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail.MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl.toTotalDeficitTail
