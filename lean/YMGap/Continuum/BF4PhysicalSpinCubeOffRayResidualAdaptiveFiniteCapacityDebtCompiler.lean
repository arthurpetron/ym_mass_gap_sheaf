/-
# A summable normalized-debt compiler for the adaptive BF4 margin

At the fixed strong-coupling anchor, the ray capacity and hence its shared
coercivity floor are already uniform in the cutoff.  The remaining exact
finite-margin inequality can therefore be normalized to the rational debt

  shared floor / exact routed finite margin.

Rather than force the variation proof to unfold the enormous finite minimum,
the denominator is a positive explicit lower proxy certified below that exact
margin.  A debt at most one reconstructs the required floor-versus-margin
comparison.  Consequently, one routing sequence and observable-connected
margin proxy, together with summable two-sided debt variation, a total
variation budget available from cutoff zero, and enough initial slack compile
to the preceding cofinal adaptive margin family and the same completed
dynamic family.

This is a sufficient persistence interface, not an inhabitant.  Neither a
canonical nor an adaptive routing sequence is proved to have summable debt
variation or the required initial slack.  The fixed anchor is not identified
with an AF or physical grouped BF4 trajectory.  No thermodynamic or continuum
limit, continuum Yang--Mills theory, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
import YMGap.Continuum.SummableRationalStepVariation

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact fixed-anchor normalized debt stream -/

/-- A routing choice at every anchor cutoff.  The same physical finite
carrier, kernel, and transition-product observable are retained. -/
abbrev AnchorAdaptivePositiveRoutingSequence : Type 1 :=
  forall K,
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) K

/-- The exact finite margin of the selected anchor routing at one cutoff. -/
def anchorAdaptiveFiniteCapacityMarginAt
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
    (routing K)

theorem anchorAdaptiveFiniteCapacityMarginAt_pos
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) :
    (0 : Q') < anchorAdaptiveFiniteCapacityMarginAt routing K :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin_pos
    (routing K)

/-- The cutoff-independent shared coercivity floor already supplied by the
proved fixed-anchor cofinal ray capacity. -/
def anchorAdaptiveSharedCoercivityFloor : Q' :=
  HalfPow.half * anchorCentralSpinCubeCofinalRayCapacity.delta

theorem anchorAdaptiveSharedCoercivityFloor_pos :
    (0 : Q') < anchorAdaptiveSharedCoercivityFloor := by
  unfold anchorAdaptiveSharedCoercivityFloor
  exact Q'.mul_pos (by decide)
    anchorCentralSpinCubeCofinalRayCapacity.delta_pos

/-- Normalized analytic debt for a positive lower proxy to the exact margin.
The separate proxy comparison keeps variation algebra small while preserving
an explicit proof edge back to the same routed observable. -/
def anchorAdaptiveFiniteCapacityDebt
    (marginLower : Nat -> Q')
    (marginLower_pos : forall K, (0 : Q') < marginLower K)
    (K : Nat) : Q' :=
  Q'.divPos anchorAdaptiveSharedCoercivityFloor
    (marginLower K) (marginLower_pos K)

/-- Debt at most one is exactly sufficient to pay the unchanged shared floor
from the positive lower proxy. -/
theorem anchorAdaptiveSharedCoercivityFloor_le_marginLower_of_debt_le_one
    (marginLower : Nat -> Q')
    (marginLower_pos : forall K, (0 : Q') < marginLower K)
    (K : Nat)
    (hdebt :
      anchorAdaptiveFiniteCapacityDebt marginLower marginLower_pos K <=
        (1 : Q')) :
    anchorAdaptiveSharedCoercivityFloor <= marginLower K := by
  let margin := marginLower K
  have hmargin : (0 : Q') < margin := marginLower_pos K
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ margin hdebt
    (Q'.le_of_lt hmargin)
  have hrecover :
      anchorAdaptiveFiniteCapacityDebt marginLower marginLower_pos K * margin ≈
        anchorAdaptiveSharedCoercivityFloor := by
    unfold anchorAdaptiveFiniteCapacityDebt
    exact Q'.divPos_mul_eqv anchorAdaptiveSharedCoercivityFloor margin hmargin
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hrecover)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.one_mul_eqv margin)))

/-! ## 2. Summable debt persistence closes every anchor cutoff -/

/-- A sufficient dynamic persistence certificate.  `budget_from_zero` says
the supplied positive budget controls the entire variation series, while
`initial_closure` records the finite initial slack that absorbs it. -/
structure AnchorAdaptiveFiniteCapacityDebtVariation : Type 1 where
  routing : AnchorAdaptivePositiveRoutingSequence
  marginLower : Nat -> Q'
  marginLower_pos : forall K, (0 : Q') < marginLower K
  marginLower_le_exact : forall K,
    marginLower K <= anchorAdaptiveFiniteCapacityMarginAt routing K
  variation : SummableRationalStepVariation
    (anchorAdaptiveFiniteCapacityDebt marginLower marginLower_pos)
  budget : Q'
  budget_pos : (0 : Q') < budget
  budget_from_zero : variation.tailControl.tailRate budget = 0
  initial_closure :
    anchorAdaptiveFiniteCapacityDebt marginLower marginLower_pos 0 + budget <=
      (1 : Q')

namespace AnchorAdaptiveFiniteCapacityDebtVariation

/-- The total variation budget preserves the normalized debt bound at every
cutoff. -/
theorem debt_le_one
    (data : AnchorAdaptiveFiniteCapacityDebtVariation) (K : Nat) :
    anchorAdaptiveFiniteCapacityDebt
        data.marginLower data.marginLower_pos K <= (1 : Q') :=
  data.variation.le_of_initial_add_totalBudget_le
    data.budget_pos data.budget_from_zero data.initial_closure K

/-- Contract normalized debt persistence back into the exact cofinal
finite-margin family. -/
def toAdaptiveFiniteCapacityMargin
    (data : AnchorAdaptiveFiniteCapacityDebtVariation) :
    AnchorAdaptiveFiniteCapacityMargin where
  routing := fun K _hK => data.routing K
  margin_bound := fun K _hK => by
    change anchorAdaptiveSharedCoercivityFloor <=
      anchorAdaptiveFiniteCapacityMarginAt data.routing K
    exact Q'.le_trans' _ _ _
      (anchorAdaptiveSharedCoercivityFloor_le_marginLower_of_debt_le_one
        data.marginLower data.marginLower_pos K (data.debt_le_one K))
      (data.marginLower_le_exact K)

/-- The normalized debt certificate discharges the remaining one-field
fixed-anchor dynamic extension. -/
def toAnchorGeometricExtension
    (data : AnchorAdaptiveFiniteCapacityDebtVariation) :
    AnchorGeometricAdaptiveTransitionProductExtension :=
  data.toAdaptiveFiniteCapacityMargin.toAnchorGeometricExtension

/-- Hence the same sufficient certificate reaches the existing completed
fixed-anchor geometric family. -/
def toAnchorGeometricCompletedFamily
    (data : AnchorAdaptiveFiniteCapacityDebtVariation) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily 0 :=
  data.toAnchorGeometricExtension.toCompletedFamily

end AnchorAdaptiveFiniteCapacityDebtVariation

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler.anchorAdaptiveFiniteCapacityMarginAt_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler.anchorAdaptiveSharedCoercivityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler.anchorAdaptiveSharedCoercivityFloor_le_marginLower_of_debt_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler.AnchorAdaptiveFiniteCapacityDebtVariation.debt_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler.AnchorAdaptiveFiniteCapacityDebtVariation.toAdaptiveFiniteCapacityMargin
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler.AnchorAdaptiveFiniteCapacityDebtVariation.toAnchorGeometricCompletedFamily
