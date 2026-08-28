/-
# Minimal all-cutoff quantitative package for the adaptive branch

The deleted-support adaptive branch originally packaged literal all-cutoff
reachability, full old-plus-new capacity, and projective route coherence.
Reachability is now constructed unconditionally, and the regional-deficit
pipeline never consumes literal path equality.  Its one load-bearing input is
therefore the full old-plus-new capacity estimate on the paths constructively
extracted from that reachability theorem.

The package below contains exactly that remaining quantitative input and
contracts it at every cutoff to the exact full routed capacity debt bound.
Projective path equality remains available as an independent optional
diagnostic and can be supplied directly to the two edge-list consequences.

The capacity field is not inhabited here.  No regional tail, completed gap,
continuum limit, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingTrafficRejoin
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRouteCoherence
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRouteCoherence
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingTrafficRejoin
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One quantitative field on the constructed route family -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffCombinedCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset,
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveOldPlusWeightedCeilingCapacityCertificate
      (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies_of_reachability
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupport_allCutoffReachability
          trajectory transitionStart physicalScale)
        cutoffOffset)

structure MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type where
  combinedCapacity :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffCombinedCapacity
      trajectory transitionStart physicalScale

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.reachable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (_certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
      trajectory transitionStart physicalScale :=
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupport_allCutoffReachability
    trajectory transitionStart physicalScale

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.pathsAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset :=
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies_of_reachability
    certificate.reachable cutoffOffset

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) :=
  matchedEventualTransportedOldAdaptiveNewRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
      (certificate.pathsAt cutoffOffset))

/-! ## 2. Pointwise contraction to the one full capacity observable -/

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullLoad_capacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
          (certificate.fullRoutingAt cutoffOffset) edge <=
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1))
          0 edge.1 edge.2 := by
  unfold
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullRoutingAt
  exact
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveFullWeightedLoad_capacity
      (certificate.pathsAt cutoffOffset)
      (certificate.combinedCapacity cutoffOffset) edge hedge

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullDebt_le_one
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualRoutedCapacityDebtOnPairForRouting
          trajectory transitionStart physicalScale (cutoffOffset + 1)
          (certificate.fullRoutingAt cutoffOffset) edge <=
      (1 : Q') := by
  unfold
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullRoutingAt
  exact
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveFullWeightedDebt_le_one
      (certificate.pathsAt cutoffOffset)
      (certificate.combinedCapacity cutoffOffset) edge hedge

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullLoadOnMappedActivated_eqv_canonicalOld
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
        (certificate.fullRoutingAt cutoffOffset)
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) ≈
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) := by
  unfold
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullRoutingAt
  exact
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRoutedLoadOnMappedActivated_eqv_canonicalOld
      (certificate.pathsAt cutoffOffset) pair hpair

/-! ## 3. The same package retains the consecutive observable path -/

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.consecutiveDirectedEdges_eq
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (coherent :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffRouteCoherence
        certificate.reachable)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    PositiveKernelChainIn.directedEdges
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveMappedPathToFollowing
          certificate.reachable cutoffOffset pair hpair) =
      PositiveKernelChainIn.directedEdges
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveFollowingPathOnMappedPair
          certificate.reachable cutoffOffset pair hpair) :=
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffDirectedEdges_eq
    coherent cutoffOffset pair hpair

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.consecutiveDirectedEdge_mem_iff
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (coherent :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffRouteCoherence
        certificate.reachable)
    (cutoffOffset : Nat) (pair edge : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    edge ∈ PositiveKernelChainIn.directedEdges
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveMappedPathToFollowing
          certificate.reachable cutoffOffset pair hpair) ↔
      edge ∈ PositiveKernelChainIn.directedEdges
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveFollowingPathOnMappedPair
          certificate.reachable cutoffOffset pair hpair) :=
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffDirectedEdge_mem_iff
    coherent cutoffOffset pair edge hpair

/-! ## Axiom audit -/

#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffCombinedCapacity
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.reachable
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.pathsAt
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullRoutingAt
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullLoad_capacity
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullDebt_le_one
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullLoadOnMappedActivated_eqv_canonicalOld
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.consecutiveDirectedEdges_eq
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.consecutiveDirectedEdge_mem_iff

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
