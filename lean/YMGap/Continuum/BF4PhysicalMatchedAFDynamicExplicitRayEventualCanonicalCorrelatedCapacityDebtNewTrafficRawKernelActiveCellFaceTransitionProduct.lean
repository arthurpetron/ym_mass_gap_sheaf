/-
# Exact transition-product rows for the three matched traffic faces

The source-cancelled demand on an actual routed cell is already known to be
the exact reverse/forward conditional-transition product along the route
prefix to that cell, including directed-edge multiplicity.  This module keeps
the same mapped current edge, literal new-endpoint list, and three shell-face
masks while lifting that pointwise identity to three exact row identities.

Three transition-product/conditional-capacity estimates then compile without
loss to the relative-source controls and the unchanged exact debt maximum.
No such estimate, continuum theory, or Clay conclusion is supplied.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private def oldNewShellPairDecidable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInOldNewShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private def newOldShellPairDecidable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewOldShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewOldShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private def newNewShellPairDecidable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewNewShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private theorem masked_eqv_masked
    (face : Prop) [Decidable face] (left right : Q')
    (hvalue : left ≈ right) :
    (if face then left else 0) ≈ if face then right else 0 := by
  by_cases hface : face
  · rw [if_pos hface, if_pos hface]
    exact hvalue
  · rw [if_neg hface, if_neg hface]
    exact Q'.eqv_refl _

/-! ## 1. The exact transition product on one routed cell -/

def matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset cell.1
  centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset)
    edge.1 edge.2 cell.2

theorem matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemand_eqv_transitionProductOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hpair : cell.1 ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemandOnCell
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  have hedge := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset cell.1 hpair
  have hsource := (mem_cartesian_iff _ _ _).mp hedge |>.1
  have hendpoint := List.mem_filter.mp hendpointPair |>.1
  exact
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand_eqv_transitionProduct
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      hsource
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset cell.1).2
      cell.2 hendpoint

/-! ## 2. Preserve the identity through the three exact face rows -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProduct
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
      trajectory transitionStart physicalScale) cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProduct
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
      trajectory transitionStart physicalScale) cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProduct
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
      trajectory transitionStart physicalScale) cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProduct
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProduct
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProduct
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceLoadRow_eqv_transitionProductRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceLoadRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductRow
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceLoadRow
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductRow
  apply listQSum_congr_on
  intro endpointPair hendpointPair
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceDemand
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProduct
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
  exact masked_eqv_masked _ _ _
    (matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemand_eqv_transitionProductOnCell
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hpair hendpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceLoadRow_eqv_transitionProductRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceLoadRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductRow
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceLoadRow
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductRow
  apply listQSum_congr_on
  intro endpointPair hendpointPair
  letI := newOldShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceDemand
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProduct
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
  exact masked_eqv_masked _ _ _
    (matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemand_eqv_transitionProductOnCell
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hpair hendpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceLoadRow_eqv_transitionProductRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceLoadRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductRow
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceLoadRow
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductRow
  apply listQSum_congr_on
  intro endpointPair hendpointPair
  letI := newNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceDemand
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProduct
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
  exact masked_eqv_masked _ _ _
    (matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemand_eqv_transitionProductOnCell
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hpair hendpointPair)

/-! ## 3. Transition-product estimates compile to exact debt -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  transitionProduct_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  transitionProduct_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  transitionProduct_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductCapacityBalanceInverseSquareControl.toRelativeSourceControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  relative_le := by
    intro cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceLoadRow_eqv_transitionProductRow
          trajectory transitionStart physicalScale cutoffOffset pair hpair)))
      (control.transitionProduct_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductCapacityBalanceInverseSquareControl.toRelativeSourceControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  relative_le := by
    intro cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceLoadRow_eqv_transitionProductRow
          trajectory transitionStart physicalScale cutoffOffset pair hpair)))
      (control.transitionProduct_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductCapacityBalanceInverseSquareControl.toRelativeSourceControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  relative_le := by
    intro cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceLoadRow_eqv_transitionProductRow
          trajectory transitionStart physicalScale cutoffOffset pair hpair)))
      (control.transitionProduct_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceTransitionProductCapacityBalances
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceRelativeSourceCapacityBalances
    oldNew.toRelativeSourceControl newOld.toRelativeSourceControl
      newNew.toRelativeSourceControl cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct.matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemand_eqv_transitionProductOnCell
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceLoadRow_eqv_transitionProductRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct.matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceLoadRow_eqv_transitionProductRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct.matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceLoadRow_eqv_transitionProductRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductCapacityBalanceInverseSquareControl.toRelativeSourceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct.MatchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductCapacityBalanceInverseSquareControl.toRelativeSourceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct.MatchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductCapacityBalanceInverseSquareControl.toRelativeSourceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceTransitionProductCapacityBalances
