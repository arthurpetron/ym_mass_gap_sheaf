/-
# Executable deleted-path decisions for activated old--new births

The deleted-connectivity compiler reduces birth-local adaptive routing to a
finite directed Boolean path problem, but leaves its path family as an open
Type-level producer.  This module makes that finite problem executable at
every fixed physical scale and cutoff.

For the exact later vacuum-sector carrier and the exact finite new-endpoint
traffic list, the decision returns either

* all deleted-support chains demanded by that observable, hence the already
  verified birth-avoiding adaptive routing; or
* a literal demanded endpoint pair whose sound-and-complete Warshall check is
  false, together with a constructive refutation of any deleted-support chain
  for that pair.

The failure branch is therefore evidence about the exact observable-sized
detour obligation, not failure of a heuristic search.  It does not assert
that the success branch holds uniformly over cutoffs, and it does not supply
the still-open routed-capacity or congestion estimate.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
import YMGap.Continuum.FiniteBoolGraphWarshallPathDecision

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedPathDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphWarshallPathDecision

/-! ## 1. The literal fixed-cutoff deleted-support check -/

def matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachableB
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat) : Bool :=
  finiteSupportReachableB
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    endpointPair.1 endpointPair.2

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyDecisionAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type :=
  FiniteSupportPathFamilyDecision
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

/-- Total finite inspection of every endpoint pair used by the exact
new-endpoint observable. -/
def decideMatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyDecisionAt
      trajectory transitionStart physicalScale cutoffOffset :=
  decideFiniteSupportPathFamily
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 2. Exact meaning of a failed endpoint check -/

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportNoChainOfReachableBFalse
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    {endpointPair : Nat × Nat}
    (hfalse :
      matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachableB
        trajectory transitionStart physicalScale cutoffOffset
        endpointPair = false) :
    ChainIn
      (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      endpointPair.1 endpointPair.2 -> False := by
  apply noChainInOfFiniteSupportReachableBFalse
  exact hfalse

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyImpossibleOfBlocked
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    {endpointPair : Nat × Nat}
    (hmem : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)
    (hfalse :
      matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachableB
        trajectory transitionStart physicalScale cutoffOffset
        endpointPair = false) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset -> False := by
  intro paths
  exact
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportNoChainOfReachableBFalse
      hfalse (paths endpointPair hmem)

/-! ## 3. Contract the success branch back to the physical routing -/

inductive MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingDecisionAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type 1
  | routed
      (routing :
        MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
          trajectory transitionStart physicalScale cutoffOffset)
  | blocked
      (endpointPair : Nat × Nat)
      (endpoint_mem : endpointPair ∈
        matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset)
      (check_false :
        matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachableB
          trajectory transitionStart physicalScale cutoffOffset
          endpointPair = false)

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyDecisionAt.toRoutingDecision
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat} :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyDecisionAt
        trajectory transitionStart physicalScale cutoffOffset ->
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingDecisionAt
        trajectory transitionStart physicalScale cutoffOffset
  | .found paths =>
      .routed
        (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.toBirthAvoidingRoutingAt
          paths)
  | .blocked endpointPair hmem hfalse =>
      .blocked endpointPair hmem hfalse

/-- The executable fixed-cutoff decision already targets the same
birth-avoiding routing used by the zero activated-load/debt compiler. -/
def decideMatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingDecisionAt
      trajectory transitionStart physicalScale cutoffOffset :=
  (decideMatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
    trajectory transitionStart physicalScale cutoffOffset).toRoutingDecision

/-! ## Axiom audit -/

#print axioms
  decideMatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportNoChainOfReachableBFalse
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyImpossibleOfBlocked
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyDecisionAt.toRoutingDecision
#print axioms
  decideMatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedPathDecision
