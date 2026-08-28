/-
# Exact crossing mass for the adaptive new-endpoint traffic

The global new-block-mass/sector-floor bound forgets which endpoint paths use
which edge.  Detailed balance gives a sharper identity before that loss:
after multiplication by the selected edge-source stationary weight, every
new-endpoint transition-product summand becomes its endpoint stationary-pair
weight times the exact route factor on that edge.

Summing yields an exact edge-local crossing mass.  This is the natural
numerator for a multicommodity-flow comparison with the literal raw-kernel
capacity, and it avoids both the global new-mass replacement and the global
sector-minimum replacement.

No local congestion bound, uniform rate, completed gap, continuum theory, or
Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSourceMassCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSourceMassCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem listQSum_pointwise_eqv_local {A : Type}
    (left right : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> left item ≈ right item) ->
      listQSum left items ≈ listQSum right items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hall =>
      Q'.add_eqv_congr'
        (hall head List.mem_cons_self)
        (listQSum_pointwise_eqv_local left right tail
          (fun item hitem => hall item (List.mem_cons_of_mem head hitem)))

private theorem canonicalListQMaxZero_le_bound_local
    {A : Type} (value : A -> Q') (bound : Q')
    (hbound : (0 : Q') <= bound) : forall items : List A,
      (forall item, item ∈ items -> value item <= bound) ->
        BF4CanonicalFiniteMehlerGramSpectralBudget.listQMaxZero value items <= bound
  | [], _ => hbound
  | head :: tail, hall => by
      unfold BF4CanonicalFiniteMehlerGramSpectralBudget.listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      constructor
      · exact hall head List.mem_cons_self
      · exact canonicalListQMaxZero_le_bound_local value bound hbound tail
          (fun item hitem => hall item (List.mem_cons_of_mem head hitem))

/-! ## 1. The stationary crossing term -/

def matchedEventualNewEndpointTrafficStationaryCrossingRouteTermForRouting
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge endpointPair : Nat × Nat) : Q' :=
  (matchedEventualCanonicalLaterIndexWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair.1 *
      matchedEventualCanonicalLaterIndexWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair.2) *
    matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset routing
      edge endpointPair

def matchedEventualNewEndpointTrafficStationaryCrossingRouteMassForRouting
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge : Nat × Nat) : Q' :=
  listQSum
    (matchedEventualNewEndpointTrafficStationaryCrossingRouteTermForRouting
      trajectory transitionStart physicalScale cutoffOffset routing edge)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 2. Detailed balance identifies every used summand -/

private theorem sourceWeight_mul_prefixEndpointWeight_eqv_stationaryPairWeight_of_edge_mem
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge endpointPair : Nat × Nat)
    (hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (hedge : (edge.1, edge.2) ∈
      PositiveKernelChainIn.directedEdges
        (routing.path endpointPair.1 endpointPair.2
          (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair).1
          (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair).2)) :
    matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset edge.1 *
        matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset routing
          edge endpointPair ≈
      matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair.1 *
        matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair.2 := by
  let hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
  let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
    hfull.1 path (edge.1, edge.2) hedge
  let sourceWeight := centralPhysicalFiniteWeight
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0 edge.1
  let leftWeight := centralPhysicalFiniteWeight
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0 endpointPair.1
  let rightWeight := centralPhysicalFiniteWeight
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0 endpointPair.2
  let product :=
    centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))
      hfull.1 prefixData.pathPrefix
  have hsource : (0 : Q') < sourceWeight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex prefixData.source_mem
  have hratio :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))
      hfull.1 prefixData.pathPrefix
  unfold
    centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
    at hratio
  rw [dif_pos prefixData.source_mem] at hratio
  have hproduct : product ≈ Q'.divPos leftWeight sourceWeight hsource :=
    Q'.eqv_symm hratio
  have hcancel : sourceWeight * product ≈ leftWeight := by
    refine Q'.eqv_trans _ (product * sourceWeight) _ ?_ ?_
    · exact Q'.mul_comm_eqv sourceWeight product
    refine Q'.eqv_trans _
      (Q'.divPos leftWeight sourceWeight hsource * sourceWeight) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ sourceWeight hproduct
    · exact Q'.divPos_mul_eqv leftWeight sourceWeight hsource
  unfold
    matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
    matchedEventualCanonicalLaterIndexWeight
  rw [dif_pos hpair, dif_pos hedge]
  change sourceWeight * (product * rightWeight) ≈ leftWeight * rightWeight
  exact Q'.eqv_trans _ ((sourceWeight * product) * rightWeight) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv sourceWeight product rightWeight))
    (Q'.mul_eqv_congr_right _ _ rightWeight hcancel)

theorem matchedEventualNewEndpointTrafficSourceWeight_mul_transitionTerm_eqv_stationaryCrossingRouteTerm
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset edge.1 *
        centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
          routing edge.1 edge.2 endpointPair ≈
      matchedEventualNewEndpointTrafficStationaryCrossingRouteTermForRouting
        trajectory transitionStart physicalScale cutoffOffset routing
        edge endpointPair := by
  have hpair := List.mem_filter.mp hendpointPair |>.1
  let hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
  let sourceWeight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset edge.1
  let prefixWeight :=
    matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset routing
      edge endpointPair
  let routeFactor :=
    matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset routing
      edge endpointPair
  have htransition :=
    matchedEventualNewEndpointTrafficTransitionTermForRouting_eqv_prefixEndpointWeight_mul_routeFactor
      trajectory transitionStart physicalScale cutoffOffset routing
      edge endpointPair
  by_cases hedge : (edge.1, edge.2) ∈
      PositiveKernelChainIn.directedEdges path
  · have hprefix :=
      sourceWeight_mul_prefixEndpointWeight_eqv_stationaryPairWeight_of_edge_mem
        trajectory transitionStart physicalScale cutoffOffset routing
        edge endpointPair hpair hedge
    refine Q'.eqv_trans _ (sourceWeight * (prefixWeight * routeFactor)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left sourceWeight _ _ htransition
    refine Q'.eqv_trans _ ((sourceWeight * prefixWeight) * routeFactor) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv sourceWeight prefixWeight routeFactor)
    unfold matchedEventualNewEndpointTrafficStationaryCrossingRouteTermForRouting
    exact Q'.mul_eqv_congr_right _ _ routeFactor hprefix
  · unfold
      centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      matchedEventualNewEndpointTrafficStationaryCrossingRouteTermForRouting
      matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
    rw [dif_pos hpair, dif_pos hpair, dif_neg hedge, if_neg hedge]
    exact Q'.eqv_trans _ 0 _
      (Q'.mul_zero_eqv sourceWeight)
      (Q'.eqv_symm (Q'.mul_zero_eqv _))

/-! ## 3. The exact edge-local crossing-mass identity -/

theorem matchedEventualNewEndpointTrafficSourceWeight_mul_load_eqv_stationaryCrossingRouteMass
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge : Nat × Nat) :
    matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset edge.1 *
        matchedEventualNewEndpointTrafficLoadOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset routing edge ≈
      matchedEventualNewEndpointTrafficStationaryCrossingRouteMassForRouting
        trajectory transitionStart physicalScale cutoffOffset routing edge := by
  let sourceWeight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset edge.1
  let transitionTerm :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      routing edge.1 edge.2
  let crossingTerm :=
    matchedEventualNewEndpointTrafficStationaryCrossingRouteTermForRouting
      trajectory transitionStart physicalScale cutoffOffset routing edge
  let items := matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset
  unfold matchedEventualNewEndpointTrafficLoadOnPairForRouting
    matchedEventualNewEndpointTrafficStationaryCrossingRouteMassForRouting
  exact Q'.eqv_trans _
    (listQSum (fun endpointPair => sourceWeight * transitionTerm endpointPair)
      items) _
    (Q'.eqv_symm (listQSum_mul_left sourceWeight transitionTerm items))
    (listQSum_pointwise_eqv_local
      (fun endpointPair => sourceWeight * transitionTerm endpointPair)
      crossingTerm items
      (fun endpointPair hendpointPair =>
        matchedEventualNewEndpointTrafficSourceWeight_mul_transitionTerm_eqv_stationaryCrossingRouteTerm
          trajectory transitionStart physicalScale cutoffOffset routing
          edge endpointPair hendpointPair))

def matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  matchedEventualNewEndpointTrafficStationaryCrossingRouteMassForRouting
    trajectory transitionStart physicalScale cutoffOffset
    (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
      trajectory transitionStart physicalScale cutoffOffset)
    edge

theorem matchedEventualActivatedDeletedSupportSourceWeight_mul_exactAdaptiveNewEndpointLoad_eqv_crossingRouteMass
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset edge.1 *
        matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge ≈
      matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass
        trajectory transitionStart physicalScale cutoffOffset edge :=
  matchedEventualNewEndpointTrafficSourceWeight_mul_load_eqv_stationaryCrossingRouteMass
    trajectory transitionStart physicalScale cutoffOffset
    (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
      trajectory transitionStart physicalScale cutoffOffset)
    edge

/-! ## 4. Local crossing mass pays exact normalized debt -/

structure MatchedEventualActivatedDeletedSupportExactAdaptiveCrossingRawCapacityAllowanceAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type 1 where
  allowance : Q'
  allowance_nonnegative : (0 : Q') <= allowance
  crossing_capacity_payment : forall edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      (0 : Q') < HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0
          edge.1 edge.2 ->
      matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass
            trajectory transitionStart physicalScale cutoffOffset edge <=
        allowance *
          matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
            trajectory transitionStart physicalScale cutoffOffset edge

theorem MatchedEventualActivatedDeletedSupportExactAdaptiveCrossingRawCapacityAllowanceAt.exactAdaptiveDebtOnPair_le_allowance
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportExactAdaptiveCrossingRawCapacityAllowanceAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <=
      data.allowance := by
  let sourceWeight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset edge.1
  let load :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let crossingMass :=
    matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass
      trajectory transitionStart physicalScale cutoffOffset edge
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let conditionalCapacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0
      edge.1 edge.2
  let rawCapacity :=
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  have hmembers := (mem_cartesian_iff _ _ edge).mp hedge
  have hsource : (0 : Q') < sourceWeight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hmembers.1
  have hcross : sourceWeight * load ≈ crossingMass :=
    matchedEventualActivatedDeletedSupportSourceWeight_mul_exactAdaptiveNewEndpointLoad_eqv_crossingRouteMass
      trajectory transitionStart physicalScale cutoffOffset edge
  have hraw : sourceWeight * conditionalCapacity ≈ rawCapacity := by
    exact
      matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge_eqv_rawKernelCapacity
        trajectory transitionStart physicalScale cutoffOffset edge hmembers.1
  unfold matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
    matchedEventualCapacityDebtFromLoadOnPair
  dsimp only
  by_cases hcapacity : (0 : Q') < conditionalCapacity
  · rw [dif_pos hcapacity]
    have hleft : sourceWeight * (floor * load) ≈ floor * crossingMass := by
      refine Q'.eqv_trans _ (floor * (sourceWeight * load)) _ ?_ ?_
      · q_ring
      exact Q'.mul_eqv_congr_left floor _ _ hcross
    have hright : data.allowance * rawCapacity ≈
        sourceWeight * (data.allowance * conditionalCapacity) := by
      refine Q'.eqv_trans _
        (data.allowance * (sourceWeight * conditionalCapacity)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left data.allowance _ _
          (Q'.eqv_symm hraw)
      q_ring
    have hsourceScaled :
        sourceWeight * (floor * load) <=
          sourceWeight * (data.allowance * conditionalCapacity) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _
          (data.crossing_capacity_payment edge hedge hcapacity)
          (Q'.le_of_eqv hright))
    have hnumerator : floor * load <=
        data.allowance * conditionalCapacity :=
      Q'.le_of_mul_le_mul_left hsourceScaled hsource
    exact Q'.divPos_le_of_le_mul _ _ hcapacity hnumerator
  · rw [dif_neg hcapacity]
    exact data.allowance_nonnegative

theorem MatchedEventualActivatedDeletedSupportExactAdaptiveCrossingRawCapacityAllowanceAt.exactAdaptiveDebtMaximum_le_allowance
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportExactAdaptiveCrossingRawCapacityAllowanceAt
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      data.allowance := by
  unfold matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
  let debt : Nat × Nat -> Q' :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset
  let pairs : List (Nat × Nat) :=
    matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)
  change BF4CanonicalFiniteMehlerGramSpectralBudget.listQMaxZero debt pairs <=
    data.allowance
  have hall : forall edge, edge ∈ pairs -> debt edge <= data.allowance := by
    intro edge hedge
    exact data.exactAdaptiveDebtOnPair_le_allowance edge hedge
  exact canonicalListQMaxZero_le_bound_local debt data.allowance
    data.allowance_nonnegative pairs hall

/-! ## 5. The local flow condition connects directly to observables -/

structure MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCrossingScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
    trajectory transitionStart physicalScale
  tailAllowance : Q'
  tailAllowance_pos : (0 : Q') < tailAllowance
  margin : Q'
  initial_closure_with_margin :
    (matchedEventualCanonicalRoutedCapacityDebtMaximum
          trajectory transitionStart physicalScale 0 +
        prefixTailTotalBudget
          (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation envelope)
          tailAllowance) + margin <=
      (1 : Q')
  crossingAllowance : Nat -> Q'
  crossingAllowance_nonnegative : forall cutoffOffset,
    (0 : Q') <= crossingAllowance cutoffOffset
  crossing_capacity_payment : forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      (0 : Q') < HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0
          edge.1 edge.2 ->
      matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass
            trajectory transitionStart physicalScale cutoffOffset edge <=
        crossingAllowance cutoffOffset *
          matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
            trajectory transitionStart physicalScale cutoffOffset edge
  total_payment_le_margin : forall cutoffOffset,
    matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        crossingAllowance cutoffOffset <=
      margin

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCrossingScalarPayment.toExactAdaptiveScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCrossingScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment
      trajectory transitionStart physicalScale where
  envelope := data.envelope
  tailAllowance := data.tailAllowance
  tailAllowance_pos := data.tailAllowance_pos
  margin := data.margin
  initial_closure_with_margin := data.initial_closure_with_margin
  payment_le_margin := by
    intro cutoffOffset
    let localAllowance :
        MatchedEventualActivatedDeletedSupportExactAdaptiveCrossingRawCapacityAllowanceAt
          trajectory transitionStart physicalScale cutoffOffset :=
      { allowance := data.crossingAllowance cutoffOffset
        allowance_nonnegative := data.crossingAllowance_nonnegative cutoffOffset
        crossing_capacity_payment := fun edge hedge hcapacity =>
          data.crossing_capacity_payment cutoffOffset edge hedge hcapacity }
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _
        localAllowance.exactAdaptiveDebtMaximum_le_allowance)
      (data.total_payment_le_margin cutoffOffset)

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCrossingScalarPayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCrossingScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toExactAdaptiveScalarPayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler.matchedEventualNewEndpointTrafficSourceWeight_mul_transitionTerm_eqv_stationaryCrossingRouteTerm
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler.matchedEventualNewEndpointTrafficSourceWeight_mul_load_eqv_stationaryCrossingRouteMass
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler.matchedEventualActivatedDeletedSupportSourceWeight_mul_exactAdaptiveNewEndpointLoad_eqv_crossingRouteMass
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler.MatchedEventualActivatedDeletedSupportExactAdaptiveCrossingRawCapacityAllowanceAt.exactAdaptiveDebtOnPair_le_allowance
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler.MatchedEventualActivatedDeletedSupportExactAdaptiveCrossingRawCapacityAllowanceAt.exactAdaptiveDebtMaximum_le_allowance
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler.MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCrossingScalarPayment.toObservableCertificate
