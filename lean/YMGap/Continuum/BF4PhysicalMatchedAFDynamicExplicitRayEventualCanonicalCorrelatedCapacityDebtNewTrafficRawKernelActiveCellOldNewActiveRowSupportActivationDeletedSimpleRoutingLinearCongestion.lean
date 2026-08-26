/-
# Linear route-factor congestion for the exact activated-edge detours

The deleted-path compiler loop-erases every successful new-endpoint detour.
This module contracts the resulting duplicate-free directed-edge list to the
sharp per-route multiplicity bound `<= 1`.  Hence the exact route factor

  path length * directed-edge multiplicity

is bounded linearly, rather than quadratically, by the literal later carrier
length.  Summing over the exact new-endpoint traffic list gives an explicit
unweighted cross-endpoint congestion ceiling.

The transition-product weights and edge capacities are deliberately not
discarded: they remain the next observable-connected quantitative join.  No
cutoff-uniform congestion, flow capacity, continuum limit, or Clay conclusion
is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingLinearCongestion

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A duplicate-free path charges one directed edge at most once -/

theorem weightedDirectedEdgeLoad_unitMap_le_one_of_nodup
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (hnodup : edges.Nodup)
    (source target : State) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, (1 : Q')))) source target <= 1 := by
  have heq :
      weightedDirectedEdgeLoad
          (edges.map (fun edge => (edge, (1 : Q')))) source target ≈
        if (source, target) ∈ edges then 1 else 0 := by
    induction edges with
    | nil => exact Q'.eqv_refl 0
    | cons edge rest ih =>
        have hparts := List.nodup_cons.mp hnodup
        simp only [weightedDirectedEdgeLoad, List.map_cons, listQSum,
          weightedDirectedEdgeIndicator]
        by_cases hhead : edge = (source, target)
        · rw [if_pos hhead]
          have hnotmem : (source, target) ∉ rest := by
            intro hmem
            exact hparts.1 (hhead ▸ hmem)
          have hmem : (source, target) ∈ edge :: rest :=
            List.mem_cons.mpr (Or.inl hhead.symm)
          rw [if_pos hmem]
          have htail :
              weightedDirectedEdgeLoad
                  (rest.map (fun traversed => (traversed, (1 : Q'))))
                  source target ≈ 0 :=
            Q'.eqv_trans _
              (if (source, target) ∈ rest then 1 else 0) _
              (ih hparts.2)
              (by rw [if_neg hnotmem]; exact Q'.eqv_refl 0)
          change 1 + weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, (1 : Q'))))
              source target ≈ 1
          exact Q'.eqv_trans _ (1 + 0) _
            (Q'.add_eqv_congr_left 1 _ _ htail)
            (Q'.eqv_of_eq (Q'.add_zero' 1))
        · rw [if_neg hhead]
          have hne : (source, target) ≠ edge := fun hedge => hhead hedge.symm
          by_cases htailMem : (source, target) ∈ rest
          · have hmem : (source, target) ∈ edge :: rest :=
              List.mem_cons_of_mem edge htailMem
            rw [if_pos hmem]
            have htail :
                weightedDirectedEdgeLoad
                    (rest.map (fun traversed => (traversed, (1 : Q'))))
                    source target ≈ 1 :=
              Q'.eqv_trans _
                (if (source, target) ∈ rest then 1 else 0) _
                (ih hparts.2)
                (by rw [if_pos htailMem]; exact Q'.eqv_refl 1)
            change 0 + weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, (1 : Q'))))
                source target ≈ 1
            exact Q'.eqv_trans _ (0 + 1) _
              (Q'.add_eqv_congr_left 0 _ _ htail)
              (Q'.eqv_of_eq (Q'.zero_add' 1))
          · have hnotmem : (source, target) ∉ edge :: rest := by
              intro hmem
              rcases List.mem_cons.mp hmem with hedge | hrest
              · exact hne hedge
              · exact htailMem hrest
            rw [if_neg hnotmem]
            have htail :
                weightedDirectedEdgeLoad
                    (rest.map (fun traversed => (traversed, (1 : Q'))))
                    source target ≈ 0 :=
              Q'.eqv_trans _
                (if (source, target) ∈ rest then 1 else 0) _
                (ih hparts.2)
                (by rw [if_neg htailMem]; exact Q'.eqv_refl 0)
            change 0 + weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, (1 : Q'))))
                source target ≈ 0
            exact Q'.eqv_trans _ (0 + 0) _
              (Q'.add_eqv_congr_left 0 _ _ htail)
              (Q'.eqv_of_eq (Q'.zero_add' 0))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) ?_
  by_cases hmem : (source, target) ∈ edges
  · rw [if_pos hmem]
    exact Q'.le_refl' 1
  · rw [if_neg hmem]
    decide

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity_le_one_of_nodup
    {w : Q'} {hw : (0 : Q') <= w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (source target : Nat)
    (hnodup : (PositiveKernelChainIn.directedEdges
      (routing.path left right hleft hright)).Nodup) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
        routing left right hleft hright source target <= 1 := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
  exact weightedDirectedEdgeLoad_unitMap_le_one_of_nodup
    (PositiveKernelChainIn.directedEdges
      (routing.path left right hleft hright)) hnodup source target

/-! ## 2. Exact new-endpoint route factors are linear in carrier size -/

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_routeFactorOnPair_le_carrierLength
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            data))
        edge endpointPair <=
      Q'.ofNat
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
  unfold matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
  have hfullPair := (List.mem_filter.mp hendpointPair).1
  rw [dif_pos hfullPair]
  let hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hfullPair
  let routing := matchedEventualTransportedOldAdaptiveNewRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
      data)
  let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
  by_cases hedge : (edge.1, edge.2) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [if_pos hedge]
    have hnodup : (PositiveKernelChainIn.directedEdges path).Nodup := by
      exact
        MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_path_directedEdges_nodup
          data endpointPair hendpointPair
    have hmultiplicity :
        centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
            routing endpointPair.1 endpointPair.2 hfull.1 hfull.2
            edge.1 edge.2 <= 1 :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity_le_one_of_nodup
        routing endpointPair.1 endpointPair.2 hfull.1 hfull.2
        edge.1 edge.2 hnodup
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.ofNat (PositiveKernelChainIn.edgeLength path))
      hmultiplicity
      (Q'.ofNat_le_ofNat (Nat.zero_le _))
    have hlength : PositiveKernelChainIn.edgeLength path <=
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
      exact
        MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_path_edgeLength_le
          data endpointPair hendpointPair
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_one_eqv
            (Q'.ofNat (PositiveKernelChainIn.edgeLength path))))
        (Q'.ofNat_le_ofNat hlength))
  · rw [if_neg hedge]
    exact Q'.ofNat_le_ofNat (Nat.zero_le _)

/-! ## 3. Observable-sized unweighted cross-endpoint congestion -/

def matchedEventualNewEndpointTrafficSimpleAdaptiveRouteFactorSum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            data))
        edge endpointPair)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A -> Q')
    {bound : Q'} (hboundNonnegative : (0 : Q') <= bound) :
    forall items : List A,
      (forall item, item ∈ items -> value item <= bound) ->
      listQSum value items <= Q'.ofNat items.length * bound
  | [], _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail :=
        listQSum_le_length_mul_local value hboundNonnegative tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem))
      have hsum :
          value head + listQSum value tail <=
            bound + Q'.ofNat tail.length * bound :=
        Q'.add_le_add hhead htail
      refine Q'.le_trans' _ _ _ hsum ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + (1 : Q') * bound) _ ?_ ?_
      · exact Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound)

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouteFactorSum_le_endpointCount_mul_carrierLength
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    matchedEventualNewEndpointTrafficSimpleAdaptiveRouteFactorSum data edge <=
      Q'.ofNat
          (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
            trajectory transitionStart physicalScale cutoffOffset).length *
        Q'.ofNat
          (matchedEventualCanonicalVacuumSectorIndices
            trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
  unfold matchedEventualNewEndpointTrafficSimpleAdaptiveRouteFactorSum
  apply listQSum_le_length_mul_local
  · exact Q'.ofNat_le_ofNat (Nat.zero_le _)
  · intro endpointPair hendpointPair
    exact
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_routeFactorOnPair_le_carrierLength
        data edge endpointPair hendpointPair

/-! ## Axiom audit -/

#print axioms weightedDirectedEdgeLoad_unitMap_le_one_of_nodup
#print axioms
  centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity_le_one_of_nodup
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_routeFactorOnPair_le_carrierLength
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouteFactorSum_le_endpointCount_mul_carrierLength

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingLinearCongestion
