/-
# Activated-edge deletion preserves all demanded endpoint reachability

Every forbidden edge is the image of an activated pair in the current vacuum
sector.  Both endpoints of every forbidden edge therefore lie in the embedded
old carrier.  This elementary observation closes the apparent new-state
attachment frontier.

Indeed, take any later-sector chain from a state to the embedded vacuum root.
While its first state is outside the old carrier, both the next directed edge
and its reverse survive deletion: a forbidden edge would have both endpoints
old.  Recursing on the tail constructs paths in both directions.  As soon as
the chain reaches the old carrier, the already proved embedded-old root paths
replace the rest of the chain.  Thus every demanded endpoint state has both
deleted-support root paths, at every cutoff, without an additional attachment
hypothesis.

This is a finite graph-routing theorem.  It does not prove a capacity bound,
route coherence, thermodynamic or continuum passage, continuum Yang--Mills
theory, an isolated vacuum, or the Clay mass-gap conclusion.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Forbidden activated edges are old at both endpoints -/

theorem matchedEventualActivatedMappedEdge_endpoints_mem_embeddedOld
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (forbiddenPair : Nat × Nat)
    (hforbidden : forbiddenPair ∈
      matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
        trajectory transitionStart physicalScale cutoffOffset) :
    forbiddenPair.1 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
        trajectory transitionStart physicalScale cutoffOffset ∧
      forbiddenPair.2 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
        trajectory transitionStart physicalScale cutoffOffset := by
  rcases List.mem_map.mp hforbidden with
    ⟨currentPair, hcurrentPair, hpairMap⟩
  have hactive :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPair_mem_and_currentKernel_not_pos
      trajectory transitionStart physicalScale cutoffOffset
      currentPair hcurrentPair
  have hcarrier :=
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_mem_and_routeMaximum_pos
      trajectory transitionStart physicalScale cutoffOffset
      currentPair hactive.1).1
  have hmembers := (mem_cartesian_iff _ _ currentPair).mp hcarrier
  constructor
  · apply List.mem_map.mpr
    refine ⟨currentPair.1, hmembers.1, ?_⟩
    simpa only [matchedEventualCanonicalCurrentPairToNext] using
      congrArg Prod.fst hpairMap
  · apply List.mem_map.mpr
    refine ⟨currentPair.2, hmembers.2, ?_⟩
    simpa only [matchedEventualCanonicalCurrentPairToNext] using
      congrArg Prod.snd hpairMap

theorem matchedEventualLaterSupportEdge_maps_deleted_of_endpoint_outside
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (first next : Nat)
    (hedge : centralPhysicalFiniteSupportAdjacentB
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0
      first next = true)
    (houtside :
      first ∉ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset ∨
        next ∉ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
      trajectory transitionStart physicalScale cutoffOffset first next = true := by
  have hnotForbidden : (first, next) ∉
      matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
        trajectory transitionStart physicalScale cutoffOffset := by
    intro hforbidden
    have hends := matchedEventualActivatedMappedEdge_endpoints_mem_embeddedOld
      trajectory transitionStart physicalScale cutoffOffset
      (first, next) hforbidden
    exact houtside.elim
      (fun hfirst => hfirst hends.1)
      (fun hnext => hnext hends.2)
  unfold
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
    forbiddenDeletedAdjacentB
  apply (Bool.and_eq_true _ _).mpr
  constructor
  · exact hedge
  · have hdecision : decide
        ((first, next) ∈
          matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
            trajectory transitionStart physicalScale cutoffOffset) = false :=
      decide_eq_false hnotForbidden
    simp only [hdecision, Bool.not_false]

/-! ## 2. A later-sector chain yields deleted paths in both directions -/

def matchedEventualExtendDeletedRootPathsAlongLaterChain
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    {first last : Nat} ->
    (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1)) ->
    ChainIn
      (centralPhysicalFiniteSupportAdjacentB
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      first last ->
    ((ChainIn
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        last
        (matchedEventualActivatedDeletedSupportRoot
          trajectory transitionStart physicalScale cutoffOffset)) ×
      (ChainIn
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        (matchedEventualActivatedDeletedSupportRoot
          trajectory transitionStart physicalScale cutoffOffset)
        last)) ->
    (ChainIn
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        first
        (matchedEventualActivatedDeletedSupportRoot
          trajectory transitionStart physicalScale cutoffOffset)) ×
      (ChainIn
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        (matchedEventualActivatedDeletedSupportRoot
          trajectory transitionStart physicalScale cutoffOffset)
        first)
  | first, _, _hfirst, ChainIn.refl _, lastPaths => lastPaths
  | first, _, hfirst,
      ChainIn.step (b := next) hedge hnext rest, lastPaths => by
      by_cases hold : first ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset
      · exact
          ⟨matchedEventualEmbeddedOldToDeletedRootPath
              trajectory transitionStart physicalScale cutoffOffset first hold,
            matchedEventualDeletedRootToEmbeddedOldPath
              trajectory transitionStart physicalScale cutoffOffset first hold⟩
      · have tailPaths := matchedEventualExtendDeletedRootPathsAlongLaterChain
            trajectory transitionStart physicalScale cutoffOffset
            hnext rest lastPaths
        have hforward :=
          matchedEventualLaterSupportEdge_maps_deleted_of_endpoint_outside
            trajectory transitionStart physicalScale cutoffOffset
            first next hedge (Or.inl hold)
        have hreverseSupport : centralPhysicalFiniteSupportAdjacentB
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1)) 0
            next first = true := by
          rw [centralPhysicalFiniteSupportAdjacentB_symmetric
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1)) 0
            next first]
          exact hedge
        have hreverse :=
          matchedEventualLaterSupportEdge_maps_deleted_of_endpoint_outside
            trajectory transitionStart physicalScale cutoffOffset
            next first hreverseSupport (Or.inr hold)
        exact
          ⟨ChainIn.step hforward hnext tailPaths.1,
            ChainIn.trans tailPaths.2
              (ChainIn.step hreverse hfirst (ChainIn.refl first))⟩

def matchedEventualDeletedSupportRootPathsOfLaterChain
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    {first : Nat}
    (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (path : ChainIn
      (centralPhysicalFiniteSupportAdjacentB
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      first
      (matchedEventualActivatedDeletedSupportRoot
        trajectory transitionStart physicalScale cutoffOffset)) :
    (ChainIn
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        first
        (matchedEventualActivatedDeletedSupportRoot
          trajectory transitionStart physicalScale cutoffOffset)) ×
      (ChainIn
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        (matchedEventualActivatedDeletedSupportRoot
          trajectory transitionStart physicalScale cutoffOffset)
        first) :=
  matchedEventualExtendDeletedRootPathsAlongLaterChain
    trajectory transitionStart physicalScale cutoffOffset hfirst path
    ⟨ChainIn.refl _, ChainIn.refl _⟩

def matchedEventualDeletedSupportRootPathsForLaterSectorState
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset state : Nat)
    (hstate : state ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    (ChainIn
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        state
        (matchedEventualActivatedDeletedSupportRoot
          trajectory transitionStart physicalScale cutoffOffset)) ×
      (ChainIn
        (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        (matchedEventualActivatedDeletedSupportRoot
          trajectory transitionStart physicalScale cutoffOffset)
        state) := by
  have hroot := matchedEventualActivatedDeletedSupportRoot_mem
    trajectory transitionStart physicalScale cutoffOffset
  have supportPath := centralPhysicalFiniteVacuumSector_connected
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0
    state
    (matchedEventualActivatedDeletedSupportRoot
      trajectory transitionStart physicalScale cutoffOffset)
    hstate hroot
  exact matchedEventualDeletedSupportRootPathsOfLaterChain
    trajectory transitionStart physicalScale cutoffOffset hstate supportPath

/-! ## 3. All demanded endpoints, all cutoffs -/

theorem matchedEventualActivatedDeletedSupportEndpointState_mem_laterSector
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset state : Nat)
    (hstate : state ∈ matchedEventualActivatedDeletedSupportEndpointStates
      trajectory transitionStart physicalScale cutoffOffset) :
    state ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1) := by
  have hflat : state ∈
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset).flatMap
          (fun pair => [pair.1, pair.2]) := by
    exact List.mem_eraseDups.mp hstate
  rcases List.mem_flatMap.mp hflat with ⟨pair, hpair, hstatePair⟩
  have hsector :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
      (List.mem_filter.mp hpair).1
  rcases List.mem_cons.mp hstatePair with hfirst | hsecond
  · subst state
    exact hsector.1
  · have hlast : state = pair.2 := List.mem_singleton.mp hsecond
    subst state
    exact hsector.2

def matchedEventualActivatedDeletedSupportRootPathFamily
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    MatchedEventualActivatedDeletedSupportRootPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset := by
  intro state hstate
  exact matchedEventualDeletedSupportRootPathsForLaterSectorState
    trajectory transitionStart physicalScale cutoffOffset state
    (matchedEventualActivatedDeletedSupportEndpointState_mem_laterSector
      trajectory transitionStart physicalScale cutoffOffset state hstate)

def matchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) :
    MatchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies
      trajectory transitionStart physicalScale :=
  fun cutoffOffset => matchedEventualActivatedDeletedSupportRootPathFamily
    trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupport_allCutoffReachability
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
      trajectory transitionStart physicalScale :=
  (matchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies
    trajectory transitionStart physicalScale).toReachability

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability.matchedEventualActivatedMappedEdge_endpoints_mem_embeddedOld
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability.matchedEventualLaterSupportEdge_maps_deleted_of_endpoint_outside
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability.matchedEventualDeletedSupportRootPathsOfLaterChain
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability.matchedEventualActivatedDeletedSupportRootPathFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedUnconditionalReachability.matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupport_allCutoffReachability
