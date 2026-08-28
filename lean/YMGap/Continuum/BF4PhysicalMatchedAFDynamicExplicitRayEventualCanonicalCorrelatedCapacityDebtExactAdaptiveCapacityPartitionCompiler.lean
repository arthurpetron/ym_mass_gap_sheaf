/-
# Exact adaptive capacity splits by edge age

The preceding normalized-reserve route was deliberately sufficient: it kept
the full transported canonical debt and paid a carrier-length ceiling for the
replacement new-endpoint routes.  The observable itself is strictly smaller.
Its exact adaptive load is

  transported old-endpoint load + adaptive new-endpoint load.

On a genuinely new edge the transported old term is exactly zero.  This
module records the resulting sharp edge-age partition directly in physical
capacity units and compiles it to the minimal exact observable certificate.
Thus neither canonical new-endpoint traffic nor the constructed weighted
ceiling occurs in the new-edge lane.

Neither exact lane is inhabited here.  No regional tail, completed gap,
continuum limit, continuum Yang--Mills theory, isolated vacuum, or Clay
conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtPartitionedCombinedDebtCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingTrafficRejoin
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr_right_local
    (scale left right : Q') (h : left ≈ right) :
    scale * left ≈ scale * right :=
  Q'.mul_eqv_congr_left scale left right h

/-! ## 1. The two exact physical-capacity lanes -/

def matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  matchedEventualNewEndpointTrafficLoadOnPairForRouting
    trajectory transitionStart physicalScale cutoffOffset
    (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
      trajectory transitionStart physicalScale cutoffOffset)
    edge

theorem matchedEventualActivatedDeletedSupportExactAdaptiveFullLoad_eqv_old_add_new
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge ≈
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge +
        matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge := by
  exact
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRoutedLoad_eqv_canonicalOld_add_new
      (matchedEventualActivatedDeletedSupportObservablePathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
      edge

def MatchedEventualActivatedDeletedSupportAllCutoffOldEdgeExactAdaptiveCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      edge ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
          trajectory transitionStart physicalScale cutoffOffset ->
        matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale *
            (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
                  trajectory transitionStart physicalScale cutoffOffset edge +
              matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
                trajectory transitionStart physicalScale cutoffOffset
                edge) <=
          HalfPow.half *
            centralPhysicalFiniteConditionalKernel
              (trajectory.nome physicalScale)
              (Q'.le_of_lt (trajectory.nome_pos physicalScale))
              (transitionStart physicalScale + (cutoffOffset + 1))
              0 edge.1 edge.2

def MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeExactAdaptiveCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
          trajectory transitionStart physicalScale cutoffOffset ->
        matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale *
            matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
              trajectory transitionStart physicalScale cutoffOffset
              edge <=
          HalfPow.half *
            centralPhysicalFiniteConditionalKernel
              (trajectory.nome physicalScale)
              (Q'.le_of_lt (trajectory.nome_pos physicalScale))
              (transitionStart physicalScale + (cutoffOffset + 1))
              0 edge.1 edge.2

/-! ## 2. Exact edge partition, with no ceiling or double counting -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveCapacityOfEdgePartition
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (oldEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffOldEdgeExactAdaptiveCapacity
        trajectory transitionStart physicalScale)
    (newEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeExactAdaptiveCapacity
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffExactAdaptiveCapacity
      trajectory transitionStart physicalScale := by
  intro cutoffOffset edge hedge
  let oldLoad :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let newLoad :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  have hrejoin :
      matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge ≈
        oldLoad + newLoad :=
    matchedEventualActivatedDeletedSupportExactAdaptiveFullLoad_eqv_old_add_new
      trajectory transitionStart physicalScale cutoffOffset edge
  by_cases hold : edge ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale cutoffOffset
  · have hscaled :
        matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale *
            matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
              trajectory transitionStart physicalScale cutoffOffset edge ≈
          matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale * (oldLoad + newLoad) :=
      mul_eqv_congr_right_local
        (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale)
        _ _ hrejoin
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled)
      (oldEdge cutoffOffset edge hedge hold)
  · have holdZero : oldLoad ≈ (0 : Q') :=
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair_eqv_zero_of_newEdge
        trajectory transitionStart physicalScale cutoffOffset edge hold
    have hsum : oldLoad + newLoad ≈ newLoad :=
      Q'.eqv_trans _ (0 + newLoad) _
        (Q'.add_eqv_congr_right _ _ newLoad holdZero)
        (Q'.eqv_of_eq (Q'.zero_add' newLoad))
    have hfullNew :
        matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
            trajectory transitionStart physicalScale cutoffOffset edge ≈
          newLoad :=
      Q'.eqv_trans _ _ _ hrejoin hsum
    have hscaled :
        matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale *
            matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
              trajectory transitionStart physicalScale cutoffOffset edge ≈
          matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale * newLoad :=
      mul_eqv_congr_right_local
        (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale)
        _ _ hfullNew
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled)
      (newEdge cutoffOffset edge hedge hold)

def matchedEventualActivatedDeletedSupportObservableCertificateOfExactEdgePartition
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (oldEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffOldEdgeExactAdaptiveCapacity
        trajectory transitionStart physicalScale)
    (newEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeExactAdaptiveCapacity
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale where
  exactAdaptiveCapacity :=
    matchedEventualActivatedDeletedSupportExactAdaptiveCapacityOfEdgePartition
      oldEdge newEdge

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveFullLoad_eqv_old_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveCapacityOfEdgePartition
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler.matchedEventualActivatedDeletedSupportObservableCertificateOfExactEdgePartition
