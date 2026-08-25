/-
# Inverse-square analytic route for canonical BF4 capacity-debt deficits

The exact total-deficit tail is the necessary dynamic input.  This module
provides a concrete sufficient route to it that matches the existing
constructive AF tail technology: exhibit an offset `B >= 2`, a nonnegative
rational coefficient `A`, and the pointwise bound

  totalDeficit(k) <= A / (k + B)^2.

The generic inverse-square compiler then constructs the representation-
invariant antitone tail modulus.  Four regional inverse-square estimates may
also be proved in parallel with a common offset; their coefficients and
pointwise bounds add to the one total control.  The resulting tail enters the
already verified computed-prefix and scalar-slack closure unchanged.

No inverse-square bound, tail allowance, or slack inequality is supplied.
The fixed strong-coupling anchor is not the physical AF/grouped-BF4
trajectory, and no thermodynamic, continuum, or Clay conclusion is asserted.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure
import YMGap.Continuum.InverseSquareAntitoneTailControl

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler
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

/-! ## 1. One explicit inverse-square control constructs the total tail -/

structure AnchorCanonicalCapacityDebtInverseSquareControl : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  totalDeficit_le : forall scale : Nat,
    anchorCanonicalCapacityDebtTotalDeficit scale <=
      coefficient * invSqTerm offset offset_at_least_two scale

def AnchorCanonicalCapacityDebtInverseSquareControl.toTotalDeficitTail
    (control : AnchorCanonicalCapacityDebtInverseSquareControl) :
    AnchorCanonicalCapacityDebtTotalDeficitTail where
  tailControl := inverseSquareTermTailControl
    anchorCanonicalCapacityDebtTotalDeficit
    control.offset control.offset_at_least_two
    control.coefficient control.coefficient_nonnegative
    control.totalDeficit_le

/-! ## 2. Four regional estimates remain independently attackable -/

structure AnchorCanonicalCapacityDebtRegionalInverseSquareControl : Type 1 where
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
  transport_le : forall scale : Nat,
    anchorTransportedCapacityDebtDeficitMaximum scale <=
      transportCoefficient *
        invSqTerm offset offset_at_least_two scale
  oldNew_le : forall scale : Nat,
    anchorOldNewReturnCapacityDebtDeficitMaximum scale <=
      oldNewCoefficient *
        invSqTerm offset offset_at_least_two scale
  newOld_le : forall scale : Nat,
    anchorNewOldReturnCapacityDebtDeficitMaximum scale <=
      newOldCoefficient *
        invSqTerm offset offset_at_least_two scale
  newNew_le : forall scale : Nat,
    anchorNewNewReturnCapacityDebtDeficitMaximum scale <=
      newNewCoefficient *
        invSqTerm offset offset_at_least_two scale

def AnchorCanonicalCapacityDebtRegionalInverseSquareControl.totalCoefficient
    (control : AnchorCanonicalCapacityDebtRegionalInverseSquareControl) : Q' :=
  control.transportCoefficient +
    (control.oldNewCoefficient +
      (control.newOldCoefficient + control.newNewCoefficient))

theorem AnchorCanonicalCapacityDebtRegionalInverseSquareControl.totalCoefficient_nonnegative
    (control : AnchorCanonicalCapacityDebtRegionalInverseSquareControl) :
    (0 : Q') <= control.totalCoefficient := by
  unfold totalCoefficient
  exact Q'.zero_le_add _ _
    control.transportCoefficient_nonnegative
    (Q'.zero_le_add _ _
      control.oldNewCoefficient_nonnegative
      (Q'.zero_le_add _ _
        control.newOldCoefficient_nonnegative
        control.newNewCoefficient_nonnegative))

def AnchorCanonicalCapacityDebtRegionalInverseSquareControl.toTotalControl
    (control : AnchorCanonicalCapacityDebtRegionalInverseSquareControl) :
    AnchorCanonicalCapacityDebtInverseSquareControl where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.totalCoefficient
  coefficient_nonnegative := control.totalCoefficient_nonnegative
  totalDeficit_le := by
    intro scale
    let term := invSqTerm
      control.offset control.offset_at_least_two scale
    have hregional :
        anchorCanonicalCapacityDebtTotalDeficit scale <=
          control.transportCoefficient * term +
            (control.oldNewCoefficient * term +
              (control.newOldCoefficient * term +
                control.newNewCoefficient * term)) := by
      unfold anchorCanonicalCapacityDebtTotalDeficit
      exact add_le_add_local
        (control.transport_le scale)
        (add_le_add_local
          (control.oldNew_le scale)
          (add_le_add_local
            (control.newOld_le scale)
            (control.newNew_le scale)))
    exact Q'.le_trans' _ _ _ hregional
      (Q'.le_of_eqv
        (four_coefficient_products_eqv
          control.transportCoefficient control.oldNewCoefficient
          control.newOldCoefficient control.newNewCoefficient term))

def AnchorCanonicalCapacityDebtRegionalInverseSquareControl.toTotalDeficitTail
    (control : AnchorCanonicalCapacityDebtRegionalInverseSquareControl) :
    AnchorCanonicalCapacityDebtTotalDeficitTail :=
  control.toTotalControl.toTotalDeficitTail

/-! ## 3. Inverse-square control reaches the computed-prefix closure -/

def anchorCanonicalCapacityDebtPersistenceOfInverseSquare
    (control : AnchorCanonicalCapacityDebtInverseSquareControl)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget
          control.toTotalDeficitTail tailAllowance <= (1 : Q')) :
    AnchorCanonicalCapacityDebtPersistence :=
  anchorCanonicalCapacityDebtPersistenceOfPrefixTail
    control.toTotalDeficitTail
    tailAllowance tailAllowance_pos initial_closure

def anchorGeometricCompletedFamilyOfInverseSquare
    (control : AnchorCanonicalCapacityDebtInverseSquareControl)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget
          control.toTotalDeficitTail tailAllowance <= (1 : Q')) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily
      0 :=
  (anchorCanonicalCapacityDebtPersistenceOfInverseSquare
    control tailAllowance tailAllowance_pos initial_closure).toAnchorGeometricCompletedFamily

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail.AnchorCanonicalCapacityDebtInverseSquareControl.toTotalDeficitTail
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail.AnchorCanonicalCapacityDebtRegionalInverseSquareControl.totalCoefficient_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail.AnchorCanonicalCapacityDebtRegionalInverseSquareControl.toTotalControl
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail.AnchorCanonicalCapacityDebtRegionalInverseSquareControl.toTotalDeficitTail
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail.anchorCanonicalCapacityDebtPersistenceOfInverseSquare
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail.anchorGeometricCompletedFamilyOfInverseSquare
