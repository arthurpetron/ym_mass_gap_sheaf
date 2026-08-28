/-
# Transported old traffic vanishes on genuinely new later edges

Coordinatewise transport sends every edge of an old canonical route into the
embedded-old pair carrier.  The existing transported routing is an indexed
path whose endpoints have been cast back to the requested later indices.  We
first prove that reading its literal directed-edge list is invariant under
those two endpoint casts.  Hence an old--old branch of the actual transported
routing cannot traverse a genuinely new later edge.

The pointwise support statement contracts through the finite endpoint sum:
on a new edge, transported old-endpoint load and its normalized debt are both
exactly zero.  Therefore the full transported debt there is exactly its
new-endpoint debt.  This is a geometric reduction of the combined normalized-
debt frontier, not a numerical capacity estimate.

No combined debt bound, regional tail, completed gap, continuum limit,
continuum Yang--Mills theory, isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedOldSupport

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedOldSupport
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem directedEdges_cast_first_local
    {State : Type} {kernel : State -> State -> Q'} {support : List State}
    {first last first' : State}
    (hfirst : first = first')
    (path :
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last) :
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
        (Eq.mp
          (congrArg
            (fun start =>
              BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
                kernel support start last)
            hfirst)
          path) =
      BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
        path := by
  cases hfirst
  rfl

private theorem directedEdges_cast_last_local
    {State : Type} {kernel : State -> State -> Q'} {support : List State}
    {first last last' : State}
    (hlast : last = last')
    (path :
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last) :
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
        (Eq.mp
          (congrArg
            (fun target =>
              BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
                kernel support first target)
            hlast)
          path) =
      BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
        path := by
  cases hlast
  rfl

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

/-! ## 1. The actual transported old branch avoids new edges -/

theorem matchedEventualCanonicalTransportedRoutingAtNext_path_avoids_newEdge_of_old
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
    (edge : Nat × Nat)
    (hnew : edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    edge ∉
      BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
        ((matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset).path
          left right hleft hright) := by
  let oldLeft := matchedEventualCanonicalNextIndexToCurrent
    trajectory transitionStart physicalScale cutoffOffset left
  let oldRight := matchedEventualCanonicalNextIndexToCurrent
    trajectory transitionStart physicalScale cutoffOffset right
  have holdLeft : oldLeft ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset :=
    matchedEventualCanonicalNextIndexToCurrent_mem
      trajectory transitionStart physicalScale cutoffOffset left
  have holdRight : oldRight ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset :=
    matchedEventualCanonicalNextIndexToCurrent_mem
      trajectory transitionStart physicalScale cutoffOffset right
  let oldPath :=
    (matchedEventualCanonicalRoutingAt
      trajectory transitionStart physicalScale cutoffOffset).path
        oldLeft oldRight holdLeft holdRight
  let mapped := matchedEventualCanonicalMapPositivePathToNext
    trajectory transitionStart physicalScale cutoffOffset holdLeft oldPath
  have hleftMap :
      matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset oldLeft = left :=
    matchedEventualCanonicalCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
      trajectory transitionStart physicalScale cutoffOffset left hleftOld
  have hrightMap :
      matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset oldRight = right :=
    matchedEventualCanonicalCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
      trajectory transitionStart physicalScale cutoffOffset right hrightOld
  let laterKernel :=
    BF4PhysicalCutoffFiniteIndexBridge.centralPhysicalFiniteKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0
  let laterSupport := matchedEventualCanonicalVacuumSectorIndices
    trajectory transitionStart physicalScale (cutoffOffset + 1)
  let mappedRight := matchedEventualCanonicalCurrentIndexToNext
    trajectory transitionStart physicalScale cutoffOffset oldRight
  let leftCast :
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        laterKernel laterSupport left mappedRight :=
    Eq.mp
      (congrArg
        (fun start =>
          BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
            laterKernel laterSupport start mappedRight)
        hleftMap)
      mapped
  let bothCast :
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        laterKernel laterSupport left right :=
    Eq.mp
      (congrArg
        (fun target =>
          BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
            laterKernel laterSupport left target)
        hrightMap)
      leftCast
  have hactual : HEq
      ((matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset).path
          left right hleft hright)
      mapped := by
    unfold matchedEventualCanonicalTransportedRoutingAtNext
    dsimp only
    rw [dif_pos hleftOld, dif_pos hrightOld]
    apply HEq.trans
    · exact cast_heq _ _
    · exact cast_heq _ _
  have hboth : HEq bothCast mapped := by
    have houter : HEq bothCast leftCast := by
      dsimp only [bothCast]
      exact cast_heq _ _
    have hinner : HEq leftCast mapped := by
      dsimp only [leftCast]
      exact cast_heq _ _
    exact HEq.trans houter hinner
  have hpath :
      (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset).path
          left right hleft hright = bothCast :=
    eq_of_heq (HEq.trans hactual (HEq.symm hboth))
  have hleftEdges := directedEdges_cast_first_local hleftMap mapped
  have hrightEdges := directedEdges_cast_last_local hrightMap leftCast
  have hedges :
      BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          bothCast =
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          mapped :=
    Eq.trans hrightEdges hleftEdges
  rw [hpath]
  intro hedge
  have hedgeMapped := hedges ▸ hedge
  have hedgeMapped' : edge ∈
      BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
        (matchedEventualCanonicalMapPositivePathToNext
          trajectory transitionStart physicalScale cutoffOffset holdLeft oldPath) := by
    simpa only [mapped] using hedgeMapped
  exact hnew
    (matchedEventualCanonicalMapPositivePathToNext_directedEdges_mem_embeddedOldPair
      trajectory transitionStart physicalScale cutoffOffset holdLeft oldPath
      edge hedgeMapped')

/-! ## 2. Exact zero old load and debt on a new edge -/

theorem matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair_eqv_zero_of_newEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hnew : edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge ≈
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
    BF4PhysicalSpinCubeOffRayResidualFlow.centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
      hfullPair
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
  rw [dif_pos hfullPair]
  have havoid :=
    matchedEventualCanonicalTransportedRoutingAtNext_path_avoids_newEdge_of_old
      trajectory transitionStart physicalScale cutoffOffset
      endpointPair.1 endpointPair.2 hfull.1 hfull.2
      holdBoth.1 holdBoth.2 edge hnew
  rw [dif_neg havoid]
  exact Q'.eqv_refl 0

theorem matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair_eqv_zero_of_newEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hnew : edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge ≈
      (0 : Q') := by
  have hload :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair_eqv_zero_of_newEdge
      trajectory transitionStart physicalScale cutoffOffset edge hnew
  let load :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let capacity := HalfPow.half *
    BF4PhysicalSpinCubeOffRayResidualConditionalCongestion.centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))
      0 edge.1 edge.2
  have huse : floor * load ≈ (0 : Q') :=
    Q'.eqv_trans _ (floor * 0) _
      (Q'.mul_eqv_congr_left floor load 0 hload)
      (Q'.mul_zero_eqv floor)
  unfold matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
  unfold matchedEventualCapacityDebtFromLoadOnPair
  change (if h : (0 : Q') < capacity then
      Q'.divPos (floor * load) capacity h else 0) ≈ 0
  by_cases hcapacity : (0 : Q') < capacity
  · rw [dif_pos hcapacity]
    unfold Q'.divPos
    exact Q'.eqv_trans _ (0 * Q'.recipPos capacity hcapacity) _
      (Q'.mul_eqv_congr_right (floor * load) 0 _ huse)
      (Q'.zero_mul_eqv _)
  · rw [dif_neg hcapacity]
    exact Q'.eqv_refl 0

/-! ## 3. Full transported debt reduces exactly to new-endpoint debt -/

theorem matchedEventualRoutedCapacityDebtOnPairForTransportedRouting_eqv_newEndpointTrafficDebt_of_newEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hnew : edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualRoutedCapacityDebtOnPairForRouting
        trajectory transitionStart physicalScale (cutoffOffset + 1)
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset) edge ≈
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge := by
  have hsplit :=
    matchedEventualCanonicalTransportedBridgeCapacityDebtOnPair_eqv_old_add_new
      trajectory transitionStart physicalScale cutoffOffset edge
  have hold :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair_eqv_zero_of_newEdge
      trajectory transitionStart physicalScale cutoffOffset edge hnew
  exact Q'.eqv_trans _
    ((0 : Q') +
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge) _
    (Q'.eqv_trans _ _ _ hsplit
      (Q'.add_eqv_congr' hold (Q'.eqv_refl _)))
    (Q'.eqv_of_eq (Q'.zero_add' _))

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler.matchedEventualCanonicalTransportedRoutingAtNext_path_avoids_newEdge_of_old
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler.matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair_eqv_zero_of_newEdge
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler.matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair_eqv_zero_of_newEdge
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler.matchedEventualRoutedCapacityDebtOnPairForTransportedRouting_eqv_newEndpointTrafficDebt_of_newEdge
