/-
# Exact all-cutoff observable capacity for the adaptive branch

The deleted-support adaptive branch originally packaged literal all-cutoff
reachability, full old-plus-new capacity, and projective route coherence.
Reachability is now constructed unconditionally, and the regional-deficit
pipeline never consumes literal path equality.  Its one load-bearing input is
therefore the full old-plus-new capacity estimate on the paths constructively
extracted from that reachability theorem.

The package below now stores exactly that observable input: the literal full
adaptive routed load fits under the literal later half-kernel capacity.  The
older old-plus-weighted-ceiling comparison remains available as a sufficient
constructor, but is no longer baked into the downstream certificate.  This
removes both canonical-new-traffic double counting and the carrier-length
ceiling from the logical statement consumed by the regional deficit bridge.
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

/-! ## 1. Strong ceiling input and exact observable output -/

def matchedEventualActivatedDeletedSupportObservablePathFamilyAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset :=
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies_of_reachability
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupport_allCutoffReachability
      trajectory transitionStart physicalScale)
    cutoffOffset

def matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) :=
  matchedEventualTransportedOldAdaptiveNewRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
      (matchedEventualActivatedDeletedSupportObservablePathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset))

def matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
    (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
      trajectory transitionStart physicalScale cutoffOffset)
    edge

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffCombinedCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset,
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveOldPlusWeightedCeilingCapacityCertificate
      (matchedEventualActivatedDeletedSupportObservablePathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffExactAdaptiveCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
            trajectory transitionStart physicalScale cutoffOffset
            edge <=
        HalfPow.half *
          centralPhysicalFiniteConditionalKernel
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1))
            0 edge.1 edge.2

structure MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type where
  exactAdaptiveCapacity :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffExactAdaptiveCapacity
      trajectory transitionStart physicalScale

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.ofCombinedCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (combined :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffCombinedCapacity
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale where
  exactAdaptiveCapacity := by
    intro cutoffOffset edge hedge
    exact
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveFullWeightedLoad_capacity
        (matchedEventualActivatedDeletedSupportObservablePathFamilyAt
          trajectory transitionStart physicalScale cutoffOffset)
        (combined cutoffOffset) edge hedge

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
    (_certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset :=
  matchedEventualActivatedDeletedSupportObservablePathFamilyAt
    trajectory transitionStart physicalScale cutoffOffset

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.fullRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (_certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) :=
  matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
    trajectory transitionStart physicalScale cutoffOffset

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
  change matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale *
      matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <= _
  exact certificate.exactAdaptiveCapacity cutoffOffset edge hedge

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
  unfold matchedEventualRoutedCapacityDebtOnPairForRouting
  dsimp only
  by_cases hcapacity : (0 : Q') < HalfPow.half *
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        0 edge.1 edge.2
  · rw [dif_pos hcapacity]
    apply Q'.divPos_le_of_le_mul _ _ hcapacity
    exact Q'.le_trans' _ _ _
      (certificate.fullLoad_capacity cutoffOffset edge hedge)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.one_mul_eqv
            (HalfPow.half *
              centralPhysicalFiniteConditionalKernel
                (trajectory.nome physicalScale)
                (Q'.le_of_lt (trajectory.nome_pos physicalScale))
                (transitionStart physicalScale + (cutoffOffset + 1))
                0 edge.1 edge.2))))
  · rw [dif_neg hcapacity]
    decide

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
  matchedEventualActivatedDeletedSupportObservablePathFamilyAt
#print axioms
  matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
#print axioms
  matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffCombinedCapacity
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffExactAdaptiveCapacity
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.ofCombinedCapacity
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
