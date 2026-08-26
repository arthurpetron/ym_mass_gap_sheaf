/-
# Support-bounded simple routing after activated-edge deletion

The executable deleted-path decision returns exact `ChainIn` data, but a
Warshall witness may contain repeated transitive syntax.  This module applies
the existing constructive loop erasure before compiling a successful deleted
chain to a positive physical-kernel path.

The resulting path

* still avoids every forbidden directed edge;
* has duplicate-free directed edges; and
* has edge length at most the literal later vacuum-sector carrier length.

The observable specialization supplies this simple routing only on the exact
new-endpoint traffic list and reconnects it to the same birth-avoiding hybrid
routing.  The carrier-size estimate is finite and explicit, not uniform in
cutoff; no congestion/capacity rate or continuum conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedPathDecision

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedPathDecision
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphSimplePaths

/-! ## 1. Generic simple paths for a directed deletion mask -/

def forbiddenDeletedSupportBoundedSimpleWalk
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (forbidden : List (State × State))
    {first last : State} (hfirst : first ∈ support)
    (chain : ChainIn
      (forbiddenDeletedAdjacentB adjacent forbidden)
      support first last) :
    SupportBoundedSimpleWalk
      (forbiddenDeletedAdjacentB adjacent forbidden)
      support first last :=
  supportBoundedSimpleWalkOfChainIn
    (forbiddenDeletedAdjacentB adjacent forbidden)
    support hfirst chain

def PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool)
    (kernel : State -> State -> Q') (support : List State)
    (forbidden : List (State × State))
    (edgePositive : forall first next,
      first ∈ support -> next ∈ support ->
      adjacent first next = true -> (0 : Q') < kernel first next) :
    {first last : State} -> (hfirst : first ∈ support) ->
      ChainIn (forbiddenDeletedAdjacentB adjacent forbidden)
        support first last ->
      PositiveKernelChainIn kernel support first last := by
  intro first last hfirst chain
  let simple := forbiddenDeletedSupportBoundedSimpleWalk
    adjacent support forbidden hfirst chain
  apply
    BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
      (forbiddenDeletedAdjacentB adjacent forbidden)
      kernel support
  · intro source target hsource htarget hedge
    exact edgePositive source target hsource htarget
      ((Bool.and_eq_true _ _).mp hedge).1
  · exact hfirst
  · exact simple.walk

theorem PositiveKernelChainIn.directedEdges_ofSupportedWalk
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool)
    (kernel : State -> State -> Q') (support : List State)
    (edgePositive : forall first next,
      first ∈ support -> next ∈ support ->
      adjacent first next = true -> (0 : Q') < kernel first next) :
    forall {first last : State} (hfirst : first ∈ support)
      (path : Walk (supportedEdge adjacent support) first last),
      PositiveKernelChainIn.directedEdges
          (BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
            adjacent kernel support edgePositive hfirst path) =
        path.directedEdges
  | _, _, _, Walk.single _ => rfl
  | first, _, hfirst, Walk.cons hedge rest => by
      have hparts := (Bool.and_eq_true _ _).mp hedge
      have hnext : rest.start ∈ support := of_decide_eq_true hparts.2
      simp only [
        BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk,
        PositiveKernelChainIn.directedEdges, Walk.directedEdges]
      exact congrArg (List.cons (first, rest.start))
        (PositiveKernelChainIn.directedEdges_ofSupportedWalk
          adjacent kernel support edgePositive hnext rest)

theorem Walk.directedEdges_avoid_forbidden
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (forbidden : List (State × State)) :
    forall {first last : State}
      (path : Walk
        (supportedEdge
          (forbiddenDeletedAdjacentB adjacent forbidden) support)
        first last),
      forall forbiddenEdge, forbiddenEdge ∈ forbidden ->
        forbiddenEdge ∉ path.directedEdges
  | _, _, Walk.single _, _, _, hedge => by cases hedge
  | first, _, Walk.cons (next := next) hedge rest, forbiddenEdge, hforbidden,
      hedgePath => by
      have hdeleted := ((Bool.and_eq_true _ _).mp hedge).1
      have havoid := ((Bool.and_eq_true _ _).mp hdeleted).2
      rcases List.mem_cons.mp hedgePath with hhead | htail
      · have hdecision : decide ((first, next) ∈ forbidden) = true :=
          decide_eq_true (hhead ▸ hforbidden)
        simp only [hdecision, Bool.not_true, Bool.false_eq_true] at havoid
      · exact Walk.directedEdges_avoid_forbidden
          adjacent support forbidden rest forbiddenEdge hforbidden htail

theorem PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn_avoids
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool)
    (kernel : State -> State -> Q') (support : List State)
    (forbidden : List (State × State))
    (edgePositive : forall first next,
      first ∈ support -> next ∈ support ->
      adjacent first next = true -> (0 : Q') < kernel first next)
    {first last : State} (hfirst : first ∈ support)
    (chain : ChainIn (forbiddenDeletedAdjacentB adjacent forbidden)
      support first last) :
    forall forbiddenEdge, forbiddenEdge ∈ forbidden ->
      forbiddenEdge ∉ PositiveKernelChainIn.directedEdges
        (PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn
          adjacent kernel support forbidden edgePositive hfirst chain) := by
  intro forbiddenEdge hforbidden
  let simple := forbiddenDeletedSupportBoundedSimpleWalk
    adjacent support forbidden hfirst chain
  change forbiddenEdge ∉ PositiveKernelChainIn.directedEdges
    (BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
      (forbiddenDeletedAdjacentB adjacent forbidden) kernel support _
      hfirst simple.walk)
  rw [PositiveKernelChainIn.directedEdges_ofSupportedWalk]
  exact Walk.directedEdges_avoid_forbidden
    adjacent support forbidden simple.walk forbiddenEdge hforbidden

theorem PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn_edgeLength_le
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool)
    (kernel : State -> State -> Q') (support : List State)
    (forbidden : List (State × State))
    (edgePositive : forall first next,
      first ∈ support -> next ∈ support ->
      adjacent first next = true -> (0 : Q') < kernel first next)
    {first last : State} (hfirst : first ∈ support)
    (chain : ChainIn (forbiddenDeletedAdjacentB adjacent forbidden)
      support first last) :
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
        (PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn
          adjacent kernel support forbidden edgePositive hfirst chain) <=
      support.length := by
  let simple := forbiddenDeletedSupportBoundedSimpleWalk
    adjacent support forbidden hfirst chain
  have hlength :=
    BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.edgeLength_ofSupportedWalk
      (forbiddenDeletedAdjacentB adjacent forbidden) kernel support
      (fun source target hsource htarget hedge =>
        edgePositive source target hsource htarget
          ((Bool.and_eq_true _ _).mp hedge).1)
      hfirst simple.walk
  change BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
      (BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
        (forbiddenDeletedAdjacentB adjacent forbidden) kernel support _
        hfirst simple.walk) <= support.length
  rw [hlength]
  exact simple.edgeLength_le

theorem PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn_directedEdges_nodup
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool)
    (kernel : State -> State -> Q') (support : List State)
    (forbidden : List (State × State))
    (edgePositive : forall first next,
      first ∈ support -> next ∈ support ->
      adjacent first next = true -> (0 : Q') < kernel first next)
    {first last : State} (hfirst : first ∈ support)
    (chain : ChainIn (forbiddenDeletedAdjacentB adjacent forbidden)
      support first last) :
    (PositiveKernelChainIn.directedEdges
      (PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn
        adjacent kernel support forbidden edgePositive hfirst chain)).Nodup := by
  let simple := forbiddenDeletedSupportBoundedSimpleWalk
    adjacent support forbidden hfirst chain
  change (PositiveKernelChainIn.directedEdges
    (BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
      (forbiddenDeletedAdjacentB adjacent forbidden) kernel support _
      hfirst simple.walk)).Nodup
  rw [PositiveKernelChainIn.directedEdges_ofSupportedWalk]
  exact Walk.directedEdges_nodup_of_vertices_nodup
    simple.walk simple.nodup

/-! ## 2. Observable-sized simple later routing -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
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
    · exact PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn
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
        hleft (data endpointPair hnew)
    · exact
        (matchedEventualCanonicalRoutingAt
          trajectory transitionStart physicalScale (cutoffOffset + 1)).path
            left right hleft hright

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting_avoids_mapped_activated
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
        ((MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            data).path endpointPair.1 endpointPair.2
          (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
            (List.mem_filter.mp hendpointPair).1).1
          (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
            (List.mem_filter.mp hendpointPair).1).2) := by
  simp only [
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting,
    dif_pos hendpointPair]
  apply PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn_avoids
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

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting_path_edgeLength_le
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
        ((MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            data).path endpointPair.1 endpointPair.2
          (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
            (List.mem_filter.mp hendpointPair).1).1
          (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
            (List.mem_filter.mp hendpointPair).1).2) <=
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
  simp only [
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting,
    dif_pos hendpointPair]
  exact PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn_edgeLength_le
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

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting_path_directedEdges_nodup
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (PositiveKernelChainIn.directedEdges
      ((MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
          data).path endpointPair.1 endpointPair.2
        (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
          (List.mem_filter.mp hendpointPair).1).1
        (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
          (List.mem_filter.mp hendpointPair).1).2)).Nodup := by
  simp only [
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting,
    dif_pos hendpointPair]
  exact
    PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn_directedEdges_nodup
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

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_path_edgeLength_le
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
        ((matchedEventualTransportedOldAdaptiveNewRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            data)).path endpointPair.1 endpointPair.2
              (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
                (List.mem_filter.mp hendpointPair).1).1
              (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
                (List.mem_filter.mp hendpointPair).1).2) <=
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
  have hbound :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting_path_edgeLength_le
      data endpointPair hendpointPair
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
        dif_pos hleftOld, dif_neg hrightOld] using hbound
  · simpa only [matchedEventualTransportedOldAdaptiveNewRoutingAtNext,
      dif_neg hleftOld] using hbound

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_path_directedEdges_nodup
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (PositiveKernelChainIn.directedEdges
      ((matchedEventualTransportedOldAdaptiveNewRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset
        (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
          data)).path endpointPair.1 endpointPair.2
            (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
              (List.mem_filter.mp hendpointPair).1).1
            (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
              (List.mem_filter.mp hendpointPair).1).2)).Nodup := by
  have hnodup :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting_path_directedEdges_nodup
      data endpointPair hendpointPair
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
        dif_pos hleftOld, dif_neg hrightOld] using hnodup
  · simpa only [matchedEventualTransportedOldAdaptiveNewRoutingAtNext,
      dif_neg hleftOld] using hnodup

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.toSimpleBirthAvoidingRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
      trajectory transitionStart physicalScale cutoffOffset where
  newRouting :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
      data
  avoids_activated := by
    intro pair hpair endpointPair hendpointPair
    dsimp only
    have havoid :=
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting_avoids_mapped_activated
        data pair hpair endpointPair hendpointPair
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

/-! ## Axiom audit -/

#print axioms PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn
#print axioms PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn_avoids
#print axioms
  PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn_edgeLength_le
#print axioms
  PositiveKernelChainIn.ofForbiddenDeletedSimpleChainIn_directedEdges_nodup
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting_avoids_mapped_activated
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting_path_edgeLength_le
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting_path_directedEdges_nodup
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_path_edgeLength_le
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_path_directedEdges_nodup
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.toSimpleBirthAvoidingRoutingAt

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
