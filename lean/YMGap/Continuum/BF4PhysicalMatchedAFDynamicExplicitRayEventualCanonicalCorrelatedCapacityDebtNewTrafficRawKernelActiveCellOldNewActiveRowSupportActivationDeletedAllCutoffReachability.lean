/-
# All-cutoff reachability interface for activated-edge detours

The fixed-cutoff deleted-path decision already computes either every detour
needed by the exact new-endpoint observable or a literal blocked endpoint
pair.  The remaining success frontier should therefore not be restated as an
opaque family of paths.

This module names the smaller Boolean interface: at every cutoff, every
endpoint pair in the literal new-traffic list makes the exact directed
Warshall check return true.  Soundness extracts the required Type-level path
families from that proposition, while completeness maps any such families
back to the same Boolean equations.  The extracted simple routes then feed
the existing birth-avoidance compiler at every cutoff and give its exact zero
activated route-factor, load, and debt conclusions.

No proof that the all-cutoff Boolean interface is inhabited, no route
coherence, no uniform weighted capacity, and no continuum conclusion is
asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedPathDecision
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedPathDecision
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteBoolGraphWarshallPathDecision

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact Boolean success frontier -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachabilityAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Prop :=
  forall endpointPair,
    endpointPair ∈
        matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset ->
      matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachableB
        trajectory transitionStart physicalScale cutoffOffset endpointPair = true

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset,
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachabilityAt
      trajectory transitionStart physicalScale cutoffOffset

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type :=
  forall cutoffOffset,
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset

/-! ## 2. Soundness and completeness on the same literal checks -/

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachabilityAt_of_pathFamily
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachabilityAt
      trajectory transitionStart physicalScale cutoffOffset := by
  intro endpointPair hendpointPair
  unfold
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachableB
  exact finiteSupportReachableB_complete
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (paths endpointPair hendpointPair)

def matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt_of_reachabilityAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachabilityAt
        trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset :=
  fun endpointPair hendpointPair =>
    chainInOfFiniteSupportReachableB
      (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      endpointPair.1 endpointPair.2
      (reachable endpointPair hendpointPair)

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability_of_pathFamilies
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
      trajectory transitionStart physicalScale := by
  intro cutoffOffset
  exact
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachabilityAt_of_pathFamily
      (paths cutoffOffset)

def matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies_of_reachability
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies
      trajectory transitionStart physicalScale :=
  fun cutoffOffset =>
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt_of_reachabilityAt
      (reachable cutoffOffset)

/-! ## 3. Contract all-cutoff success to the existing physical observable -/

def matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
      trajectory transitionStart physicalScale cutoffOffset :=
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.toSimpleBirthAvoidingRoutingAt
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies_of_reachability
      reachable cutoffOffset)

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleRouteFactor_eq_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
          reachable cutoffOffset).routing
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair)
        endpointPair = 0 :=
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.routeFactor_eq_zero
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
      reachable cutoffOffset)
    pair hpair endpointPair hendpointPair

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleLoad_eqv_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualNewEndpointTrafficLoadOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
          reachable cutoffOffset).routing
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) ≈ 0 :=
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.load_eqv_zero
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
      reachable cutoffOffset)
    pair hpair

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleDebt_eqv_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (reachable :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualNewEndpointTrafficDebtOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
          reachable cutoffOffset).routing
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) ≈ 0 :=
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.debt_eqv_zero
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
      reachable cutoffOffset)
    pair hpair

/-! ## Axiom audit -/

#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportReachabilityAt_of_pathFamily
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt_of_reachabilityAt
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability_of_pathFamilies
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies_of_reachability
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleBirthAvoidingRoutingAt
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleRouteFactor_eq_zero
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleLoad_eqv_zero
#print axioms
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffSimpleDebt_eqv_zero

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability
