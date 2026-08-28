/-
# Exact residual-capacity compiler for the constructed adaptive routes

Unconditional deleted-support reachability fixes one constructive path family
at every cutoff.  The remaining combined-capacity proposition asks the
transported old traffic and the weighted ceiling for new traffic to share one
literal half-kernel capacity.

This module rewrites that proposition without loss into the causal residual
form

  new capacity use <= half-kernel capacity - old capacity use.

Thus the old load cannot be hidden or double-counted, and the sole analytic
frontier is the exact capacity left after transporting old traffic.  The
equivalence is constructive rational algebra on the same edge and the same
selected routes.

No residual-capacity certificate, regional tail, completed gap, continuum
limit, continuum Yang--Mills theory, isolated vacuum, or Clay conclusion is
inhabited here.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingTrafficRejoin
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion

local infix:50 " ≈ " => Q'.eqv

private theorem add_sub_left_eqv_right_local (left right : Q') :
    (left + right) + -left ≈ right := by
  refine Q'.eqv_trans _ ((-left) + (left + right)) _
    (Q'.add_comm_eqv (left + right) (-left)) ?_
  refine Q'.eqv_trans _ (((-left) + left) + right) _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-left) left right)) ?_
  refine Q'.eqv_trans _ (0 + right) _
    (Q'.add_eqv_congr_right ((-left) + left) 0 right
      (Q'.neg_add_self_eqv left)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' right)

private theorem left_add_right_sub_left_eqv_right_local
    (left right : Q') : left + (right + -left) ≈ right := by
  refine Q'.eqv_trans _ ((left + right) + -left) _
    (Q'.eqv_symm (Q'.add_assoc_eqv left right (-left))) ?_
  exact add_sub_left_eqv_right_local left right

/-! ## 1. The literal constructed path family and its two capacity uses -/

def matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset :=
  matchedEventualActivatedDeletedSupportObservablePathFamilyAt
    trajectory transitionStart physicalScale cutoffOffset

def matchedEventualActivatedDeletedSupportOldCapacityUseOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge

def matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
      paths edge

def matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))
      0 edge.1 edge.2

def matchedEventualActivatedDeletedSupportResidualCapacityOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
      trajectory transitionStart physicalScale cutoffOffset edge +
    -matchedEventualActivatedDeletedSupportOldCapacityUseOnPair
      trajectory transitionStart physicalScale cutoffOffset edge

/-! ## 2. Exact equivalence of combined and residual capacity -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveResidualCapacityCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset) : Prop :=
  forall edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
          trajectory transitionStart physicalScale cutoffOffset paths edge <=
        matchedEventualActivatedDeletedSupportResidualCapacityOnPair
          trajectory transitionStart physicalScale cutoffOffset edge

theorem simpleAdaptiveCombinedCapacity_iff_residualCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveOldPlusWeightedCeilingCapacityCertificate
        paths ↔
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveResidualCapacityCertificate
        paths := by
  constructor
  · intro combined edge hedge
    let oldUse := matchedEventualActivatedDeletedSupportOldCapacityUseOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
    let newUse := matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
      trajectory transitionStart physicalScale cutoffOffset paths edge
    let capacity := matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
    have hcombined := combined edge hedge
    have hsplit : oldUse + newUse <= capacity := by
      apply Q'.le_trans' _
        (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
              trajectory transitionStart physicalScale cutoffOffset edge +
            MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
              paths edge)) _
      · exact Q'.ge_of_eqv
          (Q'.mul_add_eqv
            (matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale)
            (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
              trajectory transitionStart physicalScale cutoffOffset edge)
            (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
              paths edge))
      · exact hcombined
    have hadd := Q'.add_le_add_right
      (oldUse + newUse) capacity (-oldUse) hsplit
    exact Q'.le_trans' _ ((oldUse + newUse) + -oldUse) _
      (Q'.ge_of_eqv (add_sub_left_eqv_right_local oldUse newUse)) hadd
  · intro residual edge hedge
    let oldUse := matchedEventualActivatedDeletedSupportOldCapacityUseOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
    let newUse := matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
      trajectory transitionStart physicalScale cutoffOffset paths edge
    let capacity := matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
    have hresidual := residual edge hedge
    have hadd := Q'.add_le_add_left oldUse newUse
      (capacity + -oldUse) hresidual
    have hsplit : oldUse + newUse <= capacity :=
      Q'.le_trans' _ (oldUse + (capacity + -oldUse)) _ hadd
        (Q'.le_of_eqv
          (left_add_right_sub_left_eqv_right_local oldUse capacity))
    exact Q'.le_trans' _ (oldUse + newUse) _
      (Q'.le_of_eqv
        (Q'.mul_add_eqv
          (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale)
          (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
            trajectory transitionStart physicalScale cutoffOffset edge)
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
            paths edge)))
      hsplit

/-! ## 3. The all-cutoff frontier is exactly residual capacity -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffResidualCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset,
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveResidualCapacityCertificate
      (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)

theorem allCutoffCombinedCapacity_iff_residualCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffCombinedCapacity
        trajectory transitionStart physicalScale ↔
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffResidualCapacity
        trajectory transitionStart physicalScale := by
  constructor
  · intro combined cutoffOffset
    apply (simpleAdaptiveCombinedCapacity_iff_residualCapacity
      (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)).mp
    exact combined cutoffOffset
  · intro residual cutoffOffset
    apply (simpleAdaptiveCombinedCapacity_iff_residualCapacity
      (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)).mpr
    exact residual cutoffOffset

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.ofResidualCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (residual :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffResidualCapacity
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.ofCombinedCapacity
    ((allCutoffCombinedCapacity_iff_residualCapacity
      trajectory transitionStart physicalScale).mpr residual)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler.matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler.simpleAdaptiveCombinedCapacity_iff_residualCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler.allCutoffCombinedCapacity_iff_residualCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler.MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.ofResidualCapacity
