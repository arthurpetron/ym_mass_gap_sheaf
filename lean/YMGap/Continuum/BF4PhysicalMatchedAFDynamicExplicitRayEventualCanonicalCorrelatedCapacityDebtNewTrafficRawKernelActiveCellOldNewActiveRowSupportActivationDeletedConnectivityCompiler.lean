/-
# Deleted-support connectivity compiler for activated old--new births

The birth-local adaptive compiler consumes positive later-cutoff routes which
avoid every activated mapped edge.  This module reduces that pathwise
obligation to a finite Boolean graph problem on the exact later carrier.

The later support adjacency is masked by the mapped activated-row list.  A
generic constructive compiler turns any chain in that deleted adjacency into
a positive physical-kernel chain and proves that none of its directed edges
belongs to the forbidden list.

Two producers are exposed deliberately:

* the minimal producer supplies a deleted-support chain only for each
  new-endpoint pair in the exact old--new load; and
* the stronger producer proves internal connectivity of the whole later
  vacuum-sector carrier after deletion and restricts it to the minimal one.

Thus global deletion-connectivity is a sufficient proof path, not a hidden
necessary hypothesis.  The minimal producer compiles to the already verified
birth-avoiding routing, zero activated new-endpoint debt, and—when a routed
capacity is supplied—the unchanged finite residual-coercivity consumer.

No deleted-support path family, global connectivity theorem, routed capacity,
uniform cutoff coherence, thermodynamic/continuum limit, continuum
Yang--Mills theory, or Clay conclusion is inhabited here.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
import YMGap.Continuum.FiniteBoolGraphComponents

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.FiniteBoolGraphComponents

/-! ## 1. Generic constructive deletion compiler -/

def forbiddenDeletedAdjacentB {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool)
    (forbidden : List (State × State)) (first next : State) : Bool :=
  adjacent first next && !(decide ((first, next) ∈ forbidden))

/-- Compile a Boolean chain avoiding a literal directed-edge list into a
positive-kernel chain with the same sequence of vertices. -/
def PositiveKernelChainIn.ofForbiddenDeletedChainIn
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool)
    (kernel : State -> State -> Q') (support : List State)
    (forbidden : List (State × State))
    (edgePositive : forall first next,
      first ∈ support -> next ∈ support ->
      adjacent first next = true -> (0 : Q') < kernel first next) :
    {first last : State} -> first ∈ support ->
      ChainIn (forbiddenDeletedAdjacentB adjacent forbidden)
        support first last ->
      PositiveKernelChainIn kernel support first last
  | first, _, _hfirst, ChainIn.refl _ =>
      PositiveKernelChainIn.refl first
  | first, _, hfirst,
      ChainIn.step (b := next) hedge hnext rest =>
      let hparts := (Bool.and_eq_true _ _).mp hedge
      PositiveKernelChainIn.step
        (edgePositive first next hfirst hnext hparts.1)
        hnext
        (PositiveKernelChainIn.ofForbiddenDeletedChainIn
          adjacent kernel support forbidden edgePositive hnext rest)

theorem PositiveKernelChainIn.ofForbiddenDeletedChainIn_avoids
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool)
    (kernel : State -> State -> Q') (support : List State)
    (forbidden : List (State × State))
    (edgePositive : forall first next,
      first ∈ support -> next ∈ support ->
      adjacent first next = true -> (0 : Q') < kernel first next) :
    {first last : State} -> (hfirst : first ∈ support) ->
      (chain : ChainIn (forbiddenDeletedAdjacentB adjacent forbidden)
        support first last) ->
      forall forbiddenEdge, forbiddenEdge ∈ forbidden ->
        forbiddenEdge ∉ PositiveKernelChainIn.directedEdges
          (PositiveKernelChainIn.ofForbiddenDeletedChainIn
            adjacent kernel support forbidden edgePositive hfirst chain)
  | _, _, _, ChainIn.refl _, _, _, hedge => by
      cases hedge
  | first, _, hfirst,
      ChainIn.step (b := next) hedge hnext rest,
      forbiddenEdge, hforbidden, hedgePath => by
      change forbiddenEdge ∈
        (first, next) :: PositiveKernelChainIn.directedEdges
          (PositiveKernelChainIn.ofForbiddenDeletedChainIn
            adjacent kernel support forbidden edgePositive hnext rest)
        at hedgePath
      rcases List.mem_cons.mp hedgePath with hhead | htail
      · have hnotHead : (first, next) ∉ forbidden := by
          intro hmem
          have havoid := ((Bool.and_eq_true _ _).mp hedge).2
          have hdecision : decide ((first, next) ∈ forbidden) = true :=
            decide_eq_true hmem
          simp only [hdecision, Bool.not_true, Bool.false_eq_true] at havoid
        exact hnotHead (hhead ▸ hforbidden)
      · exact PositiveKernelChainIn.ofForbiddenDeletedChainIn_avoids
          adjacent kernel support forbidden edgePositive hnext rest
          forbiddenEdge hforbidden htail

/-! ## 2. The exact mapped activated-edge deletion at one cutoff -/

def matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    List (Nat × Nat) :=
  (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
    trajectory transitionStart physicalScale cutoffOffset).map
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (first next : Nat) : Bool :=
  forbiddenDeletedAdjacentB
    (centralPhysicalFiniteSupportAdjacentB
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0)
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
      trajectory transitionStart physicalScale cutoffOffset)
    first next

/-! ## 3. Minimal observable-sized deleted paths -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type :=
  forall endpointPair,
    endpointPair ∈
        matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset ->
      ChainIn
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        endpointPair.1 endpointPair.2

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.newRouting
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) where
  path := fun left right hleft hright => by
    let endpointPair := (left, right)
    by_cases hnew : endpointPair ∈
        matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset
    · exact PositiveKernelChainIn.ofForbiddenDeletedChainIn
        (centralPhysicalFiniteSupportAdjacentB
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0)
        (centralPhysicalFiniteKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
          trajectory transitionStart physicalScale cutoffOffset)
        (fun first next hfirst hnext hedge =>
          centralPhysicalFiniteKernel_pos_of_supportAdjacent
            hfirst hnext hedge)
        hleft
        (data endpointPair hnew)
    · exact
        (matchedEventualCanonicalRoutingAt
          trajectory transitionStart physicalScale (cutoffOffset + 1)).path
            left right hleft hright

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.newRouting_avoids_mapped_activated
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair) ∉
      PositiveKernelChainIn.directedEdges
        (data.newRouting.path endpointPair.1 endpointPair.2
          (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
            (List.mem_filter.mp hendpointPair).1).1
          (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
            (List.mem_filter.mp hendpointPair).1).2) := by
  simp only [
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.newRouting,
    dif_pos hendpointPair]
  apply PositiveKernelChainIn.ofForbiddenDeletedChainIn_avoids
    (centralPhysicalFiniteSupportAdjacentB
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0)
    (centralPhysicalFiniteKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0)
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
      trajectory transitionStart physicalScale cutoffOffset)
    (fun first next hfirst hnext hedge =>
      centralPhysicalFiniteKernel_pos_of_supportAdjacent hfirst hnext hedge)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
      (List.mem_filter.mp hendpointPair).1).1
    (data endpointPair hendpointPair)
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset pair)
  exact List.mem_map.mpr ⟨pair, hpair, rfl⟩

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.toBirthAvoidingRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
      trajectory transitionStart physicalScale cutoffOffset where
  newRouting := data.newRouting
  avoids_activated := by
    intro pair hpair endpointPair hendpointPair
    dsimp only
    have havoid := data.newRouting_avoids_mapped_activated
      pair hpair endpointPair hendpointPair
    have hnewTest := (List.mem_filter.mp hendpointPair).2
    by_cases hleftOld : endpointPair.1 ∈
        matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset
    · by_cases hrightOld : endpointPair.2 ∈
          matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset
      · have holdTest :
          matchedEventualCanonicalTransportedBridgeEndpointPairOldB
              trajectory transitionStart physicalScale cutoffOffset
              endpointPair = true := by
          unfold matchedEventualCanonicalTransportedBridgeEndpointPairOldB
          exact decide_eq_true ⟨hleftOld, hrightOld⟩
        simp only [holdTest, Bool.not_true, Bool.false_eq_true] at hnewTest
      · simpa only [matchedEventualTransportedOldAdaptiveNewRoutingAtNext,
          dif_pos hleftOld, dif_neg hrightOld] using havoid
    · simpa only [matchedEventualTransportedOldAdaptiveNewRoutingAtNext,
        dif_neg hleftOld] using havoid

/-! ## 4. Stronger whole-carrier connectivity is only a sufficient producer -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportConnectivityAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type :=
  InternallyConnected
    (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportConnectivityAt.toPathFamily
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportConnectivityAt
        trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset :=
  fun endpointPair hendpointPair =>
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
        (List.mem_filter.mp hendpointPair).1
    data endpointPair.1 endpointPair.2 hfull.1 hfull.2

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportConnectivityAt.toBirthAvoidingRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportConnectivityAt
        trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
      trajectory transitionStart physicalScale cutoffOffset :=
  data.toPathFamily.toBirthAvoidingRoutingAt

/-! ## Axiom audit -/

#print axioms PositiveKernelChainIn.ofForbiddenDeletedChainIn
#print axioms PositiveKernelChainIn.ofForbiddenDeletedChainIn_avoids
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.newRouting
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.newRouting_avoids_mapped_activated
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.toBirthAvoidingRoutingAt
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportConnectivityAt.toPathFamily
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportConnectivityAt.toBirthAvoidingRoutingAt

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
