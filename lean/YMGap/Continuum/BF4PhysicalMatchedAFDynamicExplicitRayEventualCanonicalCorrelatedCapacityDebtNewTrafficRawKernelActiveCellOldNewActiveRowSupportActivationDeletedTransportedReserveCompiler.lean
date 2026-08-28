/-
# A transported full-load reserve sufficient for adaptive capacity

The exact residual-capacity frontier subtracts only transported old traffic.
For a reusable analytic split, this module replaces that old sub-load by the
larger full canonical transported load.  The replacement is sound because the
complementary new-endpoint sub-sum is nonnegative.

An explicit reserve witness then separates the remaining proof into two
parallel, observable-connected lanes on the same edge:

* the full canonical transported traffic leaves the stated reserve; and
* the weighted ceiling of the constructed new routes fits in that reserve.

The two fields construct the exact all-cutoff residual-capacity certificate
and hence the existing adaptive observable certificate.  No reserve family is
inhabited here, and no regional tail, completed gap, continuum limit,
continuum Yang--Mills theory, isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedTransportedReserveCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingTrafficRejoin
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.FiniteDeterministicKernelPushforward

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

private theorem right_le_residual_of_add_le
    {left right capacity : Q'} (h : left + right <= capacity) :
    right <= capacity + -left := by
  have hadd := Q'.add_le_add_right
    (left + right) capacity (-left) h
  exact Q'.le_trans' _ ((left + right) + -left) _
    (Q'.ge_of_eqv (add_sub_left_eqv_right_local left right)) hadd

/-! ## 1. Transported old traffic is bounded by transported full traffic -/

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
  apply listQSum_nonnegative_on
  intro pair _hpair
  exact
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm_nonnegative
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      edge.1 edge.2 pair

theorem matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair_le_full
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset) edge := by
  let oldLoad :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let newLoad :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  have hnew : (0 : Q') <= newLoad :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset edge
  have hadd : oldLoad <= oldLoad + newLoad :=
    Q'.add_le_self_of_nonneg oldLoad newLoad hnew
  exact Q'.le_trans' _ (oldLoad + newLoad) _ hadd
    (Q'.ge_of_eqv
      (matchedEventualCanonicalTransportedBridgeRoutedLoadOnPair_eqv_old_add_new
        trajectory transitionStart physicalScale cutoffOffset edge))

/-! ## 2. The conservative transported residual -/

def matchedEventualActivatedDeletedSupportTransportedFullCapacityUseOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset) edge

def matchedEventualActivatedDeletedSupportTransportedFullResidualCapacityOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
      trajectory transitionStart physicalScale cutoffOffset edge +
    -matchedEventualActivatedDeletedSupportTransportedFullCapacityUseOnPair
      trajectory transitionStart physicalScale cutoffOffset edge

theorem matchedEventualActivatedDeletedSupportOldCapacityUseOnPair_le_transportedFull
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportOldCapacityUseOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <=
      matchedEventualActivatedDeletedSupportTransportedFullCapacityUseOnPair
        trajectory transitionStart physicalScale cutoffOffset edge := by
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair_le_full
      trajectory transitionStart physicalScale cutoffOffset edge)
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))

theorem matchedEventualActivatedDeletedSupportTransportedFullResidual_le_oldResidual
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportTransportedFullResidualCapacityOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <=
      matchedEventualActivatedDeletedSupportResidualCapacityOnPair
        trajectory transitionStart physicalScale cutoffOffset edge := by
  apply Q'.add_le_add_left
  exact Q'.neg_le_neg
    (matchedEventualActivatedDeletedSupportOldCapacityUseOnPair_le_transportedFull
      trajectory transitionStart physicalScale cutoffOffset edge)

/-! ## 3. An explicit reserve compiles the two quantitative lanes -/

structure MatchedEventualActivatedDeletedSupportAllCutoffTransportedReserve
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type where
  reserve : Nat -> Nat × Nat -> Q'
  transported_le_capacity : forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      matchedEventualActivatedDeletedSupportTransportedFullCapacityUseOnPair
            trajectory transitionStart physicalScale cutoffOffset edge +
          reserve cutoffOffset edge <=
        matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
          trajectory transitionStart physicalScale cutoffOffset edge
  new_ceiling_le_reserve : forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
            trajectory transitionStart physicalScale cutoffOffset)
          edge <= reserve cutoffOffset edge

def MatchedEventualActivatedDeletedSupportAllCutoffTransportedReserve.toResidualCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data : MatchedEventualActivatedDeletedSupportAllCutoffTransportedReserve
      trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffResidualCapacity
      trajectory transitionStart physicalScale := by
  intro cutoffOffset edge hedge
  have hreserve : data.reserve cutoffOffset edge <=
      matchedEventualActivatedDeletedSupportTransportedFullResidualCapacityOnPair
        trajectory transitionStart physicalScale cutoffOffset edge :=
    right_le_residual_of_add_le
      (data.transported_le_capacity cutoffOffset edge hedge)
  exact Q'.le_trans' _ (data.reserve cutoffOffset edge) _
    (data.new_ceiling_le_reserve cutoffOffset edge hedge)
    (Q'.le_trans' _
      (matchedEventualActivatedDeletedSupportTransportedFullResidualCapacityOnPair
        trajectory transitionStart physicalScale cutoffOffset edge) _
      hreserve
      (matchedEventualActivatedDeletedSupportTransportedFullResidual_le_oldResidual
        trajectory transitionStart physicalScale cutoffOffset edge))

def MatchedEventualActivatedDeletedSupportAllCutoffTransportedReserve.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data : MatchedEventualActivatedDeletedSupportAllCutoffTransportedReserve
      trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.ofResidualCapacity
    data.toResidualCapacity

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedTransportedReserveCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedTransportedReserveCompiler.matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair_le_full
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedTransportedReserveCompiler.matchedEventualActivatedDeletedSupportTransportedFullResidual_le_oldResidual
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedTransportedReserveCompiler.MatchedEventualActivatedDeletedSupportAllCutoffTransportedReserve.toResidualCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedTransportedReserveCompiler.MatchedEventualActivatedDeletedSupportAllCutoffTransportedReserve.toObservableCertificate
