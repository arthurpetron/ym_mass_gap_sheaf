/-
# New-state attachments generate all rooted deleted-support paths

The rooted deleted-support compiler still asks for two root paths for every
endpoint state.  Most of those states lie in the embedded old vacuum sector,
where the paths are already forced by cutoff support persistence.

This module proves the key geometric fact.  Every current support edge maps
to a later support edge which is not deleted: if its image were a mapped
activated edge, injectivity of the cutoff embedding would identify the
current edge with an activated pair.  That is impossible because the first
edge is in current support while an activated pair has current support false.

Consequently every embedded old state has canonical deleted-support paths to
and from the embedded vacuum root.  The remaining input contains root paths
only for the duplicate-free endpoint states outside the old image.  These
genuinely new-state attachments construct the complete rooted family, then
the existing endpoint paths, birth-avoiding routing, and all-cutoff
reachability.

No new-state attachment family, capacity estimate, route coherence,
thermodynamic or continuum limit, continuum Yang--Mills theory, or Clay
conclusion is inhabited here.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedRootedReachability
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationGraphBirth
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Map a Boolean chain through an edge-preserving carrier map -/

private def mapChainInLocal
    {Source Target : Type}
    {sourceAdjacent : Source -> Source -> Bool}
    {targetAdjacent : Target -> Target -> Bool}
    {sourceSupport : List Source} {targetSupport : List Target}
    (map : Source -> Target)
    (map_mem : forall state,
      state ∈ sourceSupport -> map state ∈ targetSupport)
    (map_edge : forall first next,
      first ∈ sourceSupport -> next ∈ sourceSupport ->
      sourceAdjacent first next = true ->
        targetAdjacent (map first) (map next) = true) :
    {first last : Source} -> first ∈ sourceSupport ->
      ChainIn sourceAdjacent sourceSupport first last ->
        ChainIn targetAdjacent targetSupport (map first) (map last)
  | _, _, _, ChainIn.refl state => ChainIn.refl (map state)
  | first, _, hfirst, ChainIn.step (b := next) hedge hnext rest =>
      ChainIn.step
        (map_edge first next hfirst hnext hedge)
        (map_mem next hnext)
        (mapChainInLocal map map_mem map_edge hnext rest)

/-! ## 2. An old support edge survives activated-edge deletion -/

theorem matchedEventualCanonicalCurrentIndexToNext_injective_on_vacuumSector
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    {left right : Nat}
    (hleft : left ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (hright : right ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (hmap : matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale cutoffOffset left =
      matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale cutoffOffset right) :
    left = right := by
  apply centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
    (w := trajectory.nome physicalScale)
    (hw := Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (base := transitionStart physicalScale + cutoffOffset)
    (later := (transitionStart physicalScale + cutoffOffset) + 1)
    (half := 0) (left := left) (right := right)
    (Nat.le_succ (transitionStart physicalScale + cutoffOffset))
    hleft hright
  simpa only [matchedEventualCanonicalCurrentIndexToNext] using hmap

theorem matchedEventualCurrentSupportEdge_maps_deletedSupportEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (first next : Nat)
    (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (hnext : next ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (hedge : centralPhysicalFiniteSupportAdjacentB
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0 first next = true) :
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset first)
        (matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset next) = true := by
  have hlater : centralPhysicalFiniteSupportAdjacentB
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale cutoffOffset first)
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale cutoffOffset next) = true := by
    have hfirstLt := centralPhysicalFiniteVacuumSectorIndex_lt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0 hfirst
    have hnextLt := centralPhysicalFiniteVacuumSectorIndex_lt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0 hnext
    have hmapped := centralPhysicalFiniteSupportAdjacentB_cutoffIndexMap
      (w := trajectory.nome physicalScale)
      (hw := Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (base := transitionStart physicalScale + cutoffOffset)
      (later := (transitionStart physicalScale + cutoffOffset) + 1)
      (half := 0) (row := first) (column := next)
      (Nat.le_succ (transitionStart physicalScale + cutoffOffset))
      hfirstLt hnextLt hedge
    simpa only [matchedEventualCanonicalCurrentIndexToNext, Nat.add_assoc]
      using hmapped
  have hnotForbidden :
      (matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset first,
        matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset next) ∉
        matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
          trajectory transitionStart physicalScale cutoffOffset := by
    intro hforbidden
    rcases List.mem_map.mp hforbidden with
      ⟨pair, hpair, hpairMap⟩
    have hactive :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPair_mem_and_currentKernel_not_pos
        trajectory transitionStart physicalScale cutoffOffset pair hpair
    have hpairCarrier :=
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_mem_and_routeMaximum_pos
        trajectory transitionStart physicalScale cutoffOffset pair hactive.1).1
    have hmembers := (mem_cartesian_iff _ _ pair).mp hpairCarrier
    have hfirstEq : pair.1 = first := by
      apply matchedEventualCanonicalCurrentIndexToNext_injective_on_vacuumSector
        trajectory transitionStart physicalScale cutoffOffset
        hmembers.1 hfirst
      exact congrArg Prod.fst hpairMap
    have hnextEq : pair.2 = next := by
      apply matchedEventualCanonicalCurrentIndexToNext_injective_on_vacuumSector
        trajectory transitionStart physicalScale cutoffOffset
        hmembers.2 hnext
      exact congrArg Prod.snd hpairMap
    apply hactive.2
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair
      matchedEventualCanonicalCurrentCutoff
    rw [hfirstEq, hnextEq]
    exact centralPhysicalFiniteKernel_pos_of_supportAdjacent
      hfirst hnext hedge
  unfold
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
    forbiddenDeletedAdjacentB
  apply (Bool.and_eq_true _ _).mpr
  constructor
  · exact hlater
  · have hdecision : decide
        ((matchedEventualCanonicalCurrentIndexToNext
            trajectory transitionStart physicalScale cutoffOffset first,
          matchedEventualCanonicalCurrentIndexToNext
            trajectory transitionStart physicalScale cutoffOffset next) ∈
          matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
            trajectory transitionStart physicalScale cutoffOffset) = false :=
      decide_eq_false hnotForbidden
    simp only [hdecision, Bool.not_false]

/-- Map any current vacuum-sector support chain into the later support graph
with all activated mapped edges deleted. -/
def matchedEventualMapCurrentChainToDeletedSupport
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    {first last : Nat}
    (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (path : ChainIn
      (centralPhysicalFiniteSupportAdjacentB
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale cutoffOffset)
      first last) :
    ChainIn
      (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale cutoffOffset first)
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale cutoffOffset last) :=
  mapChainInLocal
    (matchedEventualCanonicalCurrentIndexToNext
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalCurrentIndexToNext_mem
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCurrentSupportEdge_maps_deletedSupportEdge
      trajectory transitionStart physicalScale cutoffOffset)
    hfirst path

/-! ## 3. The embedded old component is rooted automatically -/

def matchedEventualEmbeddedOldToDeletedRootPath
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset state : Nat)
    (hstate : state ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    ChainIn
      (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      state
      (matchedEventualActivatedDeletedSupportRoot
        trajectory transitionStart physicalScale cutoffOffset) := by
  let oldState := matchedEventualCanonicalNextIndexToCurrent
    trajectory transitionStart physicalScale cutoffOffset state
  have holdState : oldState ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset :=
    matchedEventualCanonicalNextIndexToCurrent_mem
      trajectory transitionStart physicalScale cutoffOffset state
  have hzero : 0 ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset := by
    unfold matchedEventualCanonicalVacuumSectorIndices
    exact zero_mem_centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0
  have currentPath := centralPhysicalFiniteVacuumSector_connected
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + cutoffOffset) 0
    oldState 0 holdState hzero
  have mapped := matchedEventualMapCurrentChainToDeletedSupport
    trajectory transitionStart physicalScale cutoffOffset holdState currentPath
  have hmapState :=
    matchedEventualCanonicalCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
      trajectory transitionStart physicalScale cutoffOffset state hstate
  rw [hmapState] at mapped
  exact mapped

def matchedEventualDeletedRootToEmbeddedOldPath
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset state : Nat)
    (hstate : state ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    ChainIn
      (matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      (matchedEventualActivatedDeletedSupportRoot
        trajectory transitionStart physicalScale cutoffOffset)
      state := by
  let oldState := matchedEventualCanonicalNextIndexToCurrent
    trajectory transitionStart physicalScale cutoffOffset state
  have holdState : oldState ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset :=
    matchedEventualCanonicalNextIndexToCurrent_mem
      trajectory transitionStart physicalScale cutoffOffset state
  have hzero : 0 ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset := by
    unfold matchedEventualCanonicalVacuumSectorIndices
    exact zero_mem_centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0
  have currentPath := centralPhysicalFiniteVacuumSector_connected
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + cutoffOffset) 0
    0 oldState hzero holdState
  have mapped := matchedEventualMapCurrentChainToDeletedSupport
    trajectory transitionStart physicalScale cutoffOffset hzero currentPath
  have hmapState :=
    matchedEventualCanonicalCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
      trajectory transitionStart physicalScale cutoffOffset state hstate
  rw [hmapState] at mapped
  exact mapped

/-! ## 4. Only genuinely new endpoint states remain as input -/

def matchedEventualActivatedDeletedSupportNewEndpointStates
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    List Nat :=
  (matchedEventualActivatedDeletedSupportEndpointStates
    trajectory transitionStart physicalScale cutoffOffset).filter
      (fun state => !(decide
        (state ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset)))

abbrev MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt
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
    (matchedEventualActivatedDeletedSupportNewEndpointStates
      trajectory transitionStart physicalScale cutoffOffset)

def MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt.toRootPathFamily
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (attachments : MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt
      trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualActivatedDeletedSupportRootPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset := by
  intro state hstate
  by_cases hold : state ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale cutoffOffset
  · exact
      ⟨matchedEventualEmbeddedOldToDeletedRootPath
          trajectory transitionStart physicalScale cutoffOffset state hold,
        matchedEventualDeletedRootToEmbeddedOldPath
          trajectory transitionStart physicalScale cutoffOffset state hold⟩
  · apply attachments state
    apply List.mem_filter.mpr
    constructor
    · exact hstate
    · have hdecision : decide
          (state ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset) = false :=
        decide_eq_false hold
      simp only [hdecision, Bool.not_false]

def MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt.toPathFamily
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (attachments : MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt
      trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset :=
  attachments.toRootPathFamily.toPathFamily

def MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt.toBirthAvoidingRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (attachments : MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt
      trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
      trajectory transitionStart physicalScale cutoffOffset :=
  attachments.toPathFamily.toBirthAvoidingRoutingAt

def MatchedEventualActivatedDeletedSupportAllCutoffNewStateAttachments
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type :=
  forall cutoffOffset,
    MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt
      trajectory transitionStart physicalScale cutoffOffset

def MatchedEventualActivatedDeletedSupportAllCutoffNewStateAttachments.toRootPathFamilies
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (attachments :
      MatchedEventualActivatedDeletedSupportAllCutoffNewStateAttachments
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffRootPathFamilies
      trajectory transitionStart physicalScale :=
  fun cutoffOffset => (attachments cutoffOffset).toRootPathFamily

theorem MatchedEventualActivatedDeletedSupportAllCutoffNewStateAttachments.toReachability
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (attachments :
      MatchedEventualActivatedDeletedSupportAllCutoffNewStateAttachments
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffReachability
      trajectory transitionStart physicalScale :=
  attachments.toRootPathFamilies.toReachability

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments.matchedEventualCanonicalCurrentIndexToNext_injective_on_vacuumSector
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments.matchedEventualCurrentSupportEdge_maps_deletedSupportEdge
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments.matchedEventualMapCurrentChainToDeletedSupport
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments.matchedEventualEmbeddedOldToDeletedRootPath
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments.matchedEventualDeletedRootToEmbeddedOldPath
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments.MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt.toRootPathFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments.MatchedEventualActivatedDeletedSupportNewStateAttachmentsAt.toBirthAvoidingRoutingAt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments.MatchedEventualActivatedDeletedSupportAllCutoffNewStateAttachments.toReachability
