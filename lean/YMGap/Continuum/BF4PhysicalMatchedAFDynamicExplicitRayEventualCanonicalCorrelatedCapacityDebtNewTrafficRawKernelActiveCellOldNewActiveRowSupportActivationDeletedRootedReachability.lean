/-
# Rooted deleted-support reachability for the exact new-endpoint observable

The activated-edge deletion frontier was previously stated either as one
directed path for every demanded endpoint pair or as connectivity of the
whole later vacuum carrier.  Both descriptions duplicate graph work whenever
many endpoint pairs share a state.

This module factors the exact observable-sized problem through one rooted
family.  The duplicate-free carrier contains precisely the states occurring
as endpoints of the literal new-traffic pairs.  For each such state the
certificate supplies a deleted-support path to and from the embedded vacuum
root.  Concatenation then constructs every demanded ordered path:

    left endpoint -> embedded vacuum root -> right endpoint.

The construction remains directed: both orientations are retained as data.
A finite recursive decision returns either the complete rooted family or a
literal endpoint state and orientation whose exact Warshall check fails.
Thus no finite search is hidden in the new interface.

At every cutoff the rooted family compiles to the existing path family,
birth-avoiding adaptive routing, and all-cutoff reachability consumer.  No
rooted success family, capacity estimate, route coherence, thermodynamic or
continuum limit, continuum Yang--Mills theory, or Clay conclusion is
inhabited here.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphWarshallPathDecision

/-! ## 1. A generic rooted compiler for a finite demanded endpoint family -/

/-- The duplicate-free list of states which actually occur in a demanded
endpoint-pair list. -/
def finiteEndpointStateCarrier {State : Type} [BEq State] [LawfulBEq State]
    (endpointPairs : List (State × State)) : List State :=
  (endpointPairs.flatMap (fun pair => [pair.1, pair.2])).eraseDups

theorem finiteEndpointStateCarrier_first_mem
    {State : Type} [BEq State] [LawfulBEq State]
    {endpointPairs : List (State × State)} {pair : State × State}
    (hpair : pair ∈ endpointPairs) :
    pair.1 ∈ finiteEndpointStateCarrier endpointPairs := by
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  exact ⟨pair, hpair, List.mem_cons_self⟩

theorem finiteEndpointStateCarrier_second_mem
    {State : Type} [BEq State] [LawfulBEq State]
    {endpointPairs : List (State × State)} {pair : State × State}
    (hpair : pair ∈ endpointPairs) :
    pair.2 ∈ finiteEndpointStateCarrier endpointPairs := by
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  exact ⟨pair, hpair,
    List.mem_cons_of_mem pair.1 List.mem_cons_self⟩

/-- Directed root paths for every state in one explicit finite carrier. -/
def FiniteSupportRootPathFamily
    {State : Type}
    (adjacent : State -> State -> Bool) (support : List State)
    (root : State) (states : List State) : Type :=
  forall state, state ∈ states ->
    (ChainIn adjacent support state root) ×
      (ChainIn adjacent support root state)

/-- Concatenate the two rooted legs to construct every demanded ordered
endpoint path. -/
def FiniteSupportRootPathFamily.toEndpointPathFamily
    {State : Type} [DecidableEq State] [BEq State] [LawfulBEq State]
    {adjacent : State -> State -> Bool} {support : List State}
    {root : State} {endpointPairs : List (State × State)}
    (paths : FiniteSupportRootPathFamily adjacent support root
      (finiteEndpointStateCarrier endpointPairs)) :
    FiniteSupportPathFamily adjacent support endpointPairs :=
  fun pair hpair =>
    ChainIn.trans
      (paths pair.1 (finiteEndpointStateCarrier_first_mem hpair)).1
      (paths pair.2 (finiteEndpointStateCarrier_second_mem hpair)).2

/-- Exact finite outcome of inspecting both directed root checks for every
state in a displayed list. -/
inductive FiniteSupportRootPathFamilyDecision
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (root : State) : List State -> Type
  | found {states : List State}
      (paths : FiniteSupportRootPathFamily adjacent support root states) :
      FiniteSupportRootPathFamilyDecision adjacent support root states
  | blockedToRoot {states : List State}
      (state : State) (state_mem : state ∈ states)
      (check_false : finiteSupportReachableB adjacent support state root = false) :
      FiniteSupportRootPathFamilyDecision adjacent support root states
  | blockedFromRoot {states : List State}
      (state : State) (state_mem : state ∈ states)
      (check_false : finiteSupportReachableB adjacent support root state = false) :
      FiniteSupportRootPathFamilyDecision adjacent support root states

/-- Inspect a rooted family by structural recursion.  A failure retains the
literal state, direction, and false Warshall equation. -/
def decideFiniteSupportRootPathFamily
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (root : State) : forall states : List State,
      FiniteSupportRootPathFamilyDecision adjacent support root states
  | [] =>
      .found (fun state hstate => False.elim (List.not_mem_nil hstate))
  | head :: tail =>
      match decideFiniteSupportPath adjacent support head root with
      | .blocked hfalse =>
          .blockedToRoot head List.mem_cons_self hfalse
      | .found toRoot =>
          match decideFiniteSupportPath adjacent support root head with
          | .blocked hfalse =>
              .blockedFromRoot head List.mem_cons_self hfalse
          | .found fromRoot =>
              match decideFiniteSupportRootPathFamily
                  adjacent support root tail with
              | .blockedToRoot state hstate hfalse =>
                  .blockedToRoot state
                    (List.mem_cons_of_mem head hstate) hfalse
              | .blockedFromRoot state hstate hfalse =>
                  .blockedFromRoot state
                    (List.mem_cons_of_mem head hstate) hfalse
              | .found tailPaths =>
                  .found (fun state hstate => by
                    by_cases hhead : state = head
                    · subst state
                      exact ⟨toRoot, fromRoot⟩
                    · exact tailPaths state
                        ((List.mem_cons.mp hstate).resolve_left hhead))

/-! ## 2. Exact rooted deletion data at one matched cutoff -/

/-- The embedded current vacuum index is a literal old state in the later
carrier and is used as the common root. -/
def matchedEventualActivatedDeletedSupportRoot
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Nat :=
  matchedEventualCanonicalCurrentIndexToNext
    trajectory transitionStart physicalScale cutoffOffset 0

theorem matchedEventualActivatedDeletedSupportRoot_mem
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportRoot
        trajectory transitionStart physicalScale cutoffOffset ∈
      matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1) := by
  apply matchedEventualCanonicalCurrentIndexToNext_mem
    trajectory transitionStart physicalScale cutoffOffset 0
  exact zero_mem_centralPhysicalFiniteVacuumSectorIndices
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + cutoffOffset) 0

/-- The exact duplicate-free endpoint-state carrier for the literal new
traffic at one consecutive cutoff. -/
def matchedEventualActivatedDeletedSupportEndpointStates
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    List Nat :=
  finiteEndpointStateCarrier
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

/-- Root paths replace one path for every ordered new-traffic endpoint pair. -/
abbrev MatchedEventualActivatedDeletedSupportRootPathFamilyAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type :=
  FiniteSupportRootPathFamily
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (matchedEventualActivatedDeletedSupportRoot
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualActivatedDeletedSupportEndpointStates
      trajectory transitionStart physicalScale cutoffOffset)

def MatchedEventualActivatedDeletedSupportRootPathFamilyAt.toPathFamily
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths : MatchedEventualActivatedDeletedSupportRootPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset := by
  exact FiniteSupportRootPathFamily.toEndpointPathFamily paths

def MatchedEventualActivatedDeletedSupportRootPathFamilyAt.toBirthAvoidingRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths : MatchedEventualActivatedDeletedSupportRootPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
      trajectory transitionStart physicalScale cutoffOffset :=
  paths.toPathFamily.toBirthAvoidingRoutingAt

/-- At a fixed cutoff, decide all exact rooted endpoint checks. -/
def decideMatchedEventualActivatedDeletedSupportRootPathFamilyAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    FiniteSupportRootPathFamilyDecision
      (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      (matchedEventualActivatedDeletedSupportRoot
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualActivatedDeletedSupportEndpointStates
        trajectory transitionStart physicalScale cutoffOffset) :=
  decideFiniteSupportRootPathFamily _ _ _ _

/-! ## 3. The rooted family rejoins the existing all-cutoff observable -/

def MatchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type :=
  forall cutoffOffset,
    MatchedEventualActivatedDeletedSupportRootPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset

def MatchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies.toPathFamilies
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (paths : MatchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies
      trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffPathFamilies
      trajectory transitionStart physicalScale :=
  fun cutoffOffset => (paths cutoffOffset).toPathFamily

theorem MatchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies.toReachability
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (paths : MatchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies
      trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
      trajectory transitionStart physicalScale :=
  matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability_of_pathFamilies
    paths.toPathFamilies

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability.FiniteSupportRootPathFamily.toEndpointPathFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability.decideFiniteSupportRootPathFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability.matchedEventualActivatedDeletedSupportRoot_mem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability.MatchedEventualActivatedDeletedSupportRootPathFamilyAt.toPathFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability.MatchedEventualActivatedDeletedSupportRootPathFamilyAt.toBirthAvoidingRoutingAt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability.decideMatchedEventualActivatedDeletedSupportRootPathFamilyAt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability.MatchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies.toReachability
