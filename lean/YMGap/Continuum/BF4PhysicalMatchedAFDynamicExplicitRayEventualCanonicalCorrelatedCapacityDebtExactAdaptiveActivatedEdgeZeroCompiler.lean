/-
# Activated mapped edges carry exactly zero adaptive load

The exact adaptive capacity split still treated every embedded-old pair as a
single lane.  That is unnecessarily coarse.  A transported old route is the
coordinatewise image of a currently positive canonical route, so each of its
edges is the image of a current support edge.  Such an edge survives deletion
of the mapped activated pairs.  Hence transported old traffic, like the
already birth-avoiding new traffic, vanishes exactly on every mapped activated
edge.

The full exact adaptive load is therefore zero on that entire edge class.  Its
capacity inequality is automatic by kernel nonnegativity, leaving only two
genuine estimates: retained embedded-old edges and genuinely new edges.

Neither remaining estimate is inhabited here.  No regional tail, completed
gap, continuum limit, continuum Yang--Mills theory, isolated vacuum, or Clay
conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler

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
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewStateAttachments
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingTrafficRejoin
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_eqv_zero_of_pointwise_local
    {State : Type} (value : State -> Q') :
    forall states : List State,
      (forall state, state ∈ states -> value state ≈ (0 : Q')) ->
      listQSum value states ≈ (0 : Q')
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hall => by
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (hall head List.mem_cons_self)
          (listQSum_eqv_zero_of_pointwise_local value tail
            (fun state hstate =>
              hall state (List.mem_cons_of_mem head hstate)))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem mul_eqv_congr_right_local
    (scale left right : Q') (h : left ≈ right) :
    scale * left ≈ scale * right :=
  Q'.mul_eqv_congr_left scale left right h

/-! ## 1. Recover the positive current edge below each mapped path edge -/

theorem matchedEventualCanonicalMapPositivePathToNext_directedEdge_has_positive_preimage
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    {first last : Nat} ->
      (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale cutoffOffset) ->
      (path : PositiveKernelChainIn
        (centralPhysicalFiniteKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + cutoffOffset) 0)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale cutoffOffset)
        first last) ->
      forall edge,
        edge ∈ PositiveKernelChainIn.directedEdges
            (matchedEventualCanonicalMapPositivePathToNext
              trajectory transitionStart physicalScale cutoffOffset
              hfirst path) ->
          ∃ currentFirst currentNext,
            currentFirst ∈ matchedEventualCanonicalVacuumSectorIndices
                trajectory transitionStart physicalScale cutoffOffset ∧
              currentNext ∈ matchedEventualCanonicalVacuumSectorIndices
                  trajectory transitionStart physicalScale cutoffOffset ∧
                (0 : Q') < centralPhysicalFiniteKernel
                    (trajectory.nome physicalScale)
                    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
                    (transitionStart physicalScale + cutoffOffset) 0
                    currentFirst currentNext ∧
                  edge =
                    (matchedEventualCanonicalCurrentIndexToNext
                        trajectory transitionStart physicalScale cutoffOffset
                        currentFirst,
                      matchedEventualCanonicalCurrentIndexToNext
                        trajectory transitionStart physicalScale cutoffOffset
                        currentNext)
  | _, _, _, PositiveKernelChainIn.refl _, edge, hedge => by
      cases hedge
  | first, _, hfirst,
      PositiveKernelChainIn.step (next := next) positive hnext rest,
      edge, hedge => by
      rcases List.mem_cons.mp hedge with hhead | htail
      · exact ⟨first, next, hfirst, hnext, positive, hhead⟩
      · exact
          matchedEventualCanonicalMapPositivePathToNext_directedEdge_has_positive_preimage
            trajectory transitionStart physicalScale cutoffOffset
            hnext rest edge htail

/-! ## 2. Positive current edges cannot be activated current edges -/

theorem matchedEventualCanonicalMapPositivePathToNext_avoids_mappedActivated
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    {first last : Nat}
    (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale cutoffOffset)
      first last)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair ∉
      PositiveKernelChainIn.directedEdges
        (matchedEventualCanonicalMapPositivePathToNext
          trajectory transitionStart physicalScale cutoffOffset
          hfirst path) := by
  intro hedge
  rcases
    matchedEventualCanonicalMapPositivePathToNext_directedEdge_has_positive_preimage
      trajectory transitionStart physicalScale cutoffOffset
      hfirst path
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair)
      hedge with
    ⟨currentFirst, currentNext, hcurrentFirst, hcurrentNext,
      hpositive, hmap⟩
  have hadjacent :
      centralPhysicalFiniteSupportAdjacentB
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + cutoffOffset) 0
          currentFirst currentNext = true :=
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hcurrentFirst hcurrentNext).mpr hpositive
  have hdeleted :=
    matchedEventualCurrentSupportEdge_maps_deletedSupportEdge
      trajectory transitionStart physicalScale cutoffOffset
      currentFirst currentNext hcurrentFirst hcurrentNext hadjacent
  have hpairMapped :
      matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair ∈
        matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
          trajectory transitionStart physicalScale cutoffOffset :=
    List.mem_map.mpr ⟨pair, hpair, rfl⟩
  have hcurrentMapped :
      (matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset currentFirst,
        matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset currentNext) ∈
        matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
          trajectory transitionStart physicalScale cutoffOffset := by
    simpa only [hmap] using hpairMapped
  unfold
    matchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAdjacentB
    forbiddenDeletedAdjacentB at hdeleted
  have havoid := ((Bool.and_eq_true _ _).mp hdeleted).2
  have hdecision : decide
      ((matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset currentFirst,
        matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset currentNext) ∈
        matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
          trajectory transitionStart physicalScale cutoffOffset) = true :=
    decide_eq_true hcurrentMapped
  simp only [hdecision, Bool.not_true, Bool.false_eq_true] at havoid

/-! ## 3. Transported old traffic is zero on mapped activated edges -/

theorem matchedEventualCanonicalTransportedRoutingAtNext_path_avoids_mappedActivated_of_old
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (left right : Nat)
    (hleft : left ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (hright : right ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (hleftOld : left ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale cutoffOffset)
    (hrightOld : right ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale cutoffOffset)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair ∉
      PositiveKernelChainIn.directedEdges
        ((matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset).path
          left right hleft hright) := by
  rw [
    matchedEventualCanonicalTransportedRoutingAtNext_directedEdges_eq_mappedOld_of_old
      trajectory transitionStart physicalScale cutoffOffset left right
      hleft hright hleftOld hrightOld]
  unfold matchedEventualCanonicalMappedOldPathAtNext
  exact matchedEventualCanonicalMapPositivePathToNext_avoids_mappedActivated
    trajectory transitionStart physicalScale cutoffOffset
    (matchedEventualCanonicalNextIndexToCurrent_mem
      trajectory transitionStart physicalScale cutoffOffset left)
    ((matchedEventualCanonicalRoutingAt
      trajectory transitionStart physicalScale cutoffOffset).path
        (matchedEventualCanonicalNextIndexToCurrent
          trajectory transitionStart physicalScale cutoffOffset left)
        (matchedEventualCanonicalNextIndexToCurrent
          trajectory transitionStart physicalScale cutoffOffset right)
        (matchedEventualCanonicalNextIndexToCurrent_mem
          trajectory transitionStart physicalScale cutoffOffset left)
        (matchedEventualCanonicalNextIndexToCurrent_mem
          trajectory transitionStart physicalScale cutoffOffset right))
    pair hpair

theorem matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnMappedActivated_eqv_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) ≈
      (0 : Q') := by
  unfold matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
  apply listQSum_eqv_zero_of_pointwise_local
  intro endpointPair hendpointPair
  have hfiltered := List.mem_filter.mp hendpointPair
  have hfullPair := hfiltered.1
  have holdBoth :
      endpointPair.1 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset ∧
        endpointPair.2 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset := by
    have holdTest := hfiltered.2
    unfold matchedEventualCanonicalTransportedBridgeEndpointPairOldB at holdTest
    exact of_decide_eq_true holdTest
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hfullPair
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
  rw [dif_pos hfullPair]
  have havoid :=
    matchedEventualCanonicalTransportedRoutingAtNext_path_avoids_mappedActivated_of_old
      trajectory transitionStart physicalScale cutoffOffset
      endpointPair.1 endpointPair.2 hfull.1 hfull.2
      holdBoth.1 holdBoth.2 pair hpair
  rw [dif_neg havoid]
  exact Q'.eqv_refl 0

/-! ## 4. The full exact adaptive load and capacity are automatic there -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnMappedActivated_eqv_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) ≈
      (0 : Q') := by
  have hrejoin :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRoutedLoadOnMappedActivated_eqv_canonicalOld
      (matchedEventualActivatedDeletedSupportObservablePathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
      pair hpair
  exact Q'.eqv_trans _ _ _ hrejoin
    (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnMappedActivated_eqv_zero
      trajectory transitionStart physicalScale cutoffOffset pair hpair)

theorem matchedEventualActivatedDeletedSupportExactAdaptiveCapacityOnMappedActivated
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset pair).1
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset pair).2 := by
  have hscaled :
      matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
            trajectory transitionStart physicalScale cutoffOffset
            (matchedEventualCanonicalCurrentPairToNext
              trajectory transitionStart physicalScale cutoffOffset pair) ≈
        (0 : Q') :=
    Q'.eqv_trans _
      (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale * 0) _
      (mul_eqv_congr_right_local
        (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale)
        _ 0
        (matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnMappedActivated_eqv_zero
          trajectory transitionStart physicalScale cutoffOffset pair hpair))
      (Q'.mul_zero_eqv _)
  exact Q'.le_trans' _ (0 : Q') _
    (Q'.le_of_eqv hscaled)
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (centralPhysicalFiniteConditionalKernel_nonnegative
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).1
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).2))

/-! ## 5. Only retained-old and genuinely-new estimates remain -/

def MatchedEventualActivatedDeletedSupportAllCutoffRetainedOldEdgeExactAdaptiveCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      edge ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
          trajectory transitionStart physicalScale cutoffOffset ->
        edge ∉ matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
            trajectory transitionStart physicalScale cutoffOffset ->
          matchedEventualCanonicalSupportSharedFloor
                trajectory transitionStart physicalScale *
              (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
                    trajectory transitionStart physicalScale cutoffOffset edge +
                matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
                  trajectory transitionStart physicalScale cutoffOffset edge) <=
            HalfPow.half *
              centralPhysicalFiniteConditionalKernel
                (trajectory.nome physicalScale)
                (Q'.le_of_lt (trajectory.nome_pos physicalScale))
                (transitionStart physicalScale + (cutoffOffset + 1))
                0 edge.1 edge.2

theorem matchedEventualActivatedDeletedSupportExactAdaptiveCapacityOfRetainedOldAndNew
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (retainedOld :
      MatchedEventualActivatedDeletedSupportAllCutoffRetainedOldEdgeExactAdaptiveCapacity
        trajectory transitionStart physicalScale)
    (newEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeExactAdaptiveCapacity
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffExactAdaptiveCapacity
      trajectory transitionStart physicalScale := by
  apply matchedEventualActivatedDeletedSupportExactAdaptiveCapacityOfEdgePartition
  · intro cutoffOffset edge hedge hold
    by_cases hactivated :
        edge ∈ matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
          trajectory transitionStart physicalScale cutoffOffset
    · rcases List.mem_map.mp hactivated with
        ⟨pair, hpair, hpairMap⟩
      have hfullZero :=
        matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnMappedActivated_eqv_zero
          trajectory transitionStart physicalScale cutoffOffset pair hpair
      have hrejoin :=
        matchedEventualActivatedDeletedSupportExactAdaptiveFullLoad_eqv_old_add_new
          trajectory transitionStart physicalScale cutoffOffset edge
      have hsumZero :
          matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
                trajectory transitionStart physicalScale cutoffOffset edge +
              matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
                trajectory transitionStart physicalScale cutoffOffset edge ≈
            (0 : Q') := by
        exact Q'.eqv_trans _
          (matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
            trajectory transitionStart physicalScale cutoffOffset edge) _
          (Q'.eqv_symm hrejoin)
          (by simpa only [hpairMap] using hfullZero)
      have hscaled :
          matchedEventualCanonicalSupportSharedFloor
                trajectory transitionStart physicalScale *
              (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
                    trajectory transitionStart physicalScale cutoffOffset edge +
                matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
                  trajectory transitionStart physicalScale cutoffOffset edge) ≈
            (0 : Q') :=
        Q'.eqv_trans _
          (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * 0) _
          (mul_eqv_congr_right_local
            (matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale)
            _ 0 hsumZero)
          (Q'.mul_zero_eqv _)
      exact Q'.le_trans' _ (0 : Q') _
        (Q'.le_of_eqv hscaled)
        (Q'.mul_nonneg _ _ HalfPow.half_nonneg
          (centralPhysicalFiniteConditionalKernel_nonnegative
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1))
            0 edge.1 edge.2))
    · exact retainedOld cutoffOffset edge hedge hold hactivated
  · exact newEdge

def matchedEventualActivatedDeletedSupportObservableCertificateOfRetainedOldAndNew
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (retainedOld :
      MatchedEventualActivatedDeletedSupportAllCutoffRetainedOldEdgeExactAdaptiveCapacity
        trajectory transitionStart physicalScale)
    (newEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeExactAdaptiveCapacity
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale where
  exactAdaptiveCapacity :=
    matchedEventualActivatedDeletedSupportExactAdaptiveCapacityOfRetainedOldAndNew
      retainedOld newEdge

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler.matchedEventualCanonicalMapPositivePathToNext_avoids_mappedActivated
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler.matchedEventualCanonicalTransportedRoutingAtNext_path_avoids_mappedActivated_of_old
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler.matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnMappedActivated_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnMappedActivated_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveCapacityOnMappedActivated
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveCapacityOfRetainedOldAndNew
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler.matchedEventualActivatedDeletedSupportObservableCertificateOfRetainedOldAndNew
