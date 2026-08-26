/-
# Projective coherence of all-cutoff simple adaptive routes

Raw equality of paths at consecutive cutoffs is ill-typed: the paths live on
different finite carriers.  The existing matched cutoff embedding already
maps any positive path into the following carrier.  This module uses exactly
that map to state the route-coherence frontier.

For every pair in the literal later vacuum-sector carrier, coherence says
that mapping the selected simple hybrid path once more is equal to the path
selected by the following hybrid routing on the mapped endpoints.  Thus the
comparison follows one observable path through consecutive compiler stages.
It implies equality of the literal directed-edge occurrence lists and route
lengths after recoding.

The coherence proposition is not inhabited here.  No routed-data variation,
uniform weighted capacity, regional tail, continuum limit, or Clay conclusion
is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRouteCoherence

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. The same selected path before and after cutoff recoding -/

def matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptivePathOnPairAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      pair.1 pair.2 :=
  let hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
    reachable cutoffOffset).routing.path
      pair.1 pair.2 hmembers.1 hmembers.2

def matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveMappedPathToFollowing
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + ((cutoffOffset + 1) + 1)) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale ((cutoffOffset + 1) + 1))
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale (cutoffOffset + 1) pair.1)
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale (cutoffOffset + 1) pair.2) :=
  let hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  matchedEventualCanonicalMapPositivePathToNext
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    hmembers.1
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptivePathOnPairAt
      reachable cutoffOffset pair hpair)

def matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveFollowingPathOnMappedPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + ((cutoffOffset + 1) + 1)) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale ((cutoffOffset + 1) + 1))
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale (cutoffOffset + 1) pair.1)
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale (cutoffOffset + 1) pair.2) :=
  let hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  let hleft := matchedEventualCanonicalCurrentIndexToNext_mem
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    pair.1 hmembers.1
  let hright := matchedEventualCanonicalCurrentIndexToNext_mem
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    pair.2 hmembers.2
  (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
    reachable (cutoffOffset + 1)).routing.path
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale (cutoffOffset + 1) pair.1)
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale (cutoffOffset + 1) pair.2)
      hleft hright

/-! ## 2. The projective route-coherence certificate -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveRouteCoherenceAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) : Prop :=
  forall pair,
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) ->
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveMappedPathToFollowing
        reachable cutoffOffset pair hpair =
      matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveFollowingPathOnMappedPair
        reachable cutoffOffset pair hpair

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffRouteCoherence
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale) : Prop :=
  forall cutoffOffset,
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveRouteCoherenceAt
      reachable cutoffOffset

/-! ## 3. Observable consequences on the same recoded path -/

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffDirectedEdges_eq
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    {reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale}
    (coherent :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffRouteCoherence
        reachable)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    PositiveKernelChainIn.directedEdges
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveMappedPathToFollowing
          reachable cutoffOffset pair hpair) =
      PositiveKernelChainIn.directedEdges
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveFollowingPathOnMappedPair
          reachable cutoffOffset pair hpair) :=
  congrArg PositiveKernelChainIn.directedEdges
    (coherent cutoffOffset pair hpair)

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffEdgeLength_eq
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    {reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale}
    (coherent :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffRouteCoherence
        reachable)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    PositiveKernelChainIn.edgeLength
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveMappedPathToFollowing
          reachable cutoffOffset pair hpair) =
      PositiveKernelChainIn.edgeLength
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveFollowingPathOnMappedPair
          reachable cutoffOffset pair hpair) :=
  congrArg PositiveKernelChainIn.edgeLength
    (coherent cutoffOffset pair hpair)

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffDirectedEdge_mem_iff
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    {reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale}
    (coherent :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffRouteCoherence
        reachable)
    (cutoffOffset : Nat) (pair edge : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    edge ∈ PositiveKernelChainIn.directedEdges
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveMappedPathToFollowing
          reachable cutoffOffset pair hpair) ↔
      edge ∈ PositiveKernelChainIn.directedEdges
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveFollowingPathOnMappedPair
          reachable cutoffOffset pair hpair) := by
  rw [matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffDirectedEdges_eq
    coherent cutoffOffset pair hpair]

/-! ## Axiom audit -/

#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptivePathOnPairAt
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveMappedPathToFollowing
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveFollowingPathOnMappedPair
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffDirectedEdges_eq
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffEdgeLength_eq
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportSimpleAdaptiveAllCutoffDirectedEdge_mem_iff

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRouteCoherence
