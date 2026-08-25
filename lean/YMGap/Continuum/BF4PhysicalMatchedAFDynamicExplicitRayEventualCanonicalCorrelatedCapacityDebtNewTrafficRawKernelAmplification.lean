/-
# Raw-kernel expansion of matched dynamic new-traffic amplification

The weighted-amplification compiler removes the coarse endpoint count, but
its quotient initially still hides why division by a small endpoint weight is
safe.  On the actual routed path, the edge load is the endpoint stationary
pair weight times path length and directed-edge multiplicity.  Dividing by
the source weight produces the transition-product term; the later debt
normalization then combines that source weight with the conditional
transition to recover the literal raw physical kernel entry.

This module exposes those cancellations on the same actual endpoint list,
mapped current edge, transported route, and matched cutoff.  It supplies no
raw-kernel floor, route-length or multiplicity bound, inverse-square estimate,
continuum theory, or Clay conclusion.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or declaration marked noncomputable is
used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

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

private theorem divPos_eqv_congr_numerator_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (heq : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _
    (Q'.recipPos denominator hdenominator) heq

private theorem nested_divPos_endpoint_factor_cancellation_local
    (floor pairWeight routeFactor sourceWeight conditionalCapacity : Q')
    (hsourceWeight : (0 : Q') < sourceWeight)
    (hconditionalCapacity : (0 : Q') < conditionalCapacity) :
    Q'.divPos
        (floor * Q'.divPos (pairWeight * routeFactor)
          sourceWeight hsourceWeight)
        conditionalCapacity hconditionalCapacity ≈
      pairWeight *
        Q'.divPos (floor * routeFactor)
          (sourceWeight * conditionalCapacity)
          (Q'.mul_pos hsourceWeight hconditionalCapacity) := by
  let inner := Q'.divPos (pairWeight * routeFactor)
    sourceWeight hsourceWeight
  let outer := Q'.divPos (floor * inner)
    conditionalCapacity hconditionalCapacity
  let denominator := sourceWeight * conditionalCapacity
  let raw := Q'.divPos (floor * routeFactor) denominator
    (Q'.mul_pos hsourceWeight hconditionalCapacity)
  have houterCancel : conditionalCapacity * outer ≈ floor * inner := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv conditionalCapacity outer)
      (Q'.divPos_mul_eqv (floor * inner)
        conditionalCapacity hconditionalCapacity)
  have hinnerCancel : inner * sourceWeight ≈ pairWeight * routeFactor :=
    Q'.divPos_mul_eqv (pairWeight * routeFactor)
      sourceWeight hsourceWeight
  have hrawCancel : raw * denominator ≈ floor * routeFactor :=
    Q'.divPos_mul_eqv (floor * routeFactor) denominator
      (Q'.mul_pos hsourceWeight hconditionalCapacity)
  have hleft : denominator * outer ≈ floor * (pairWeight * routeFactor) := by
    dsimp only [denominator]
    refine Q'.eqv_trans _ (sourceWeight *
      (conditionalCapacity * outer)) _ ?_ ?_
    · q_ring
    refine Q'.eqv_trans _ (sourceWeight * (floor * inner)) _
      (Q'.mul_eqv_congr_left sourceWeight _ _ houterCancel) ?_
    refine Q'.eqv_trans _ (floor * (inner * sourceWeight)) _ ?_ ?_
    · q_ring
    exact Q'.mul_eqv_congr_left floor _ _ hinnerCancel
  have hright : denominator * (pairWeight * raw) ≈
      floor * (pairWeight * routeFactor) := by
    dsimp only [denominator]
    refine Q'.eqv_trans _
      (pairWeight * (raw * (sourceWeight * conditionalCapacity))) _ ?_ ?_
    · q_ring
    refine Q'.eqv_trans _ (pairWeight * (floor * routeFactor)) _
      (Q'.mul_eqv_congr_left pairWeight _ _
        (by simpa only [denominator] using hrawCancel)) ?_
    q_ring
  apply Q'.mul_left_cancel_of_pos
    (Q'.mul_pos hsourceWeight hconditionalCapacity)
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

private theorem matchedEventualCapacityDebtFromLoadOnPair_eqv_of_load_local
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) {left right : Q'}
    (heq : left ≈ right) :
    matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge left ≈
      matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge right := by
  unfold matchedEventualCapacityDebtFromLoadOnPair
  by_cases hcapacity : (0 : Q') <
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2
  · rw [dif_pos hcapacity, dif_pos hcapacity]
    exact divPos_eqv_congr_numerator_local hcapacity
      (Q'.mul_eqv_congr_left
        (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale)
        left right heq)
  · rw [dif_neg hcapacity, dif_neg hcapacity]
    exact Q'.eqv_refl 0

private theorem weightedDirectedEdgeLoad_constantMap_eqv_scalarMultiplicity_local
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (load : Q') (source target : State) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, load))) source target ≈
      load * weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, (1 : Q')))) source target := by
  unfold weightedDirectedEdgeLoad
  rw [listQSum_map, listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (fun edge => load *
        weightedDirectedEdgeIndicator (edge, (1 : Q')) source target)
      edges) _ ?_ ?_
  · apply listQSum_congr_on
    intro edge _hedge
    unfold weightedDirectedEdgeIndicator
    by_cases heq : edge = (source, target)
    · rw [if_pos heq, if_pos heq]
      exact Q'.eqv_symm (Q'.mul_one_eqv load)
    · rw [if_neg heq, if_neg heq]
      exact Q'.eqv_symm (Q'.mul_zero_eqv load)
  exact listQSum_mul_left load
    (fun edge =>
      weightedDirectedEdgeIndicator (edge, (1 : Q')) source target)
    edges

private theorem weightedDirectedEdgeLoad_constantMap_eqv_zero_of_not_mem_local
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (load : Q') (source target : State)
    (hnot : (source, target) ∉ edges) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, load))) source target ≈ 0 := by
  unfold weightedDirectedEdgeLoad
  rw [listQSum_map]
  refine Q'.eqv_trans _ (listQSum (fun _ => (0 : Q')) edges) _ ?_ ?_
  · apply listQSum_congr_on
    intro edge hedge
    unfold weightedDirectedEdgeIndicator
    have hne : edge ≠ (source, target) := by
      intro heq
      exact hnot (heq ▸ hedge)
    rw [if_neg hne]
    exact Q'.eqv_refl 0
  exact listQSum_zero edges

private theorem listQMaxZero_mono_on_local
    {State : Type} (left right : State -> Q') :
    forall states : List State,
      (forall state, state ∈ states -> left state <= right state) ->
      listQMaxZero left states <= listQMaxZero right states
  | [], _ => Q'.le_refl' 0
  | state :: states, hall => by
      unfold listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      constructor
      · exact Q'.le_trans' _ _ _
          (hall state List.mem_cons_self)
          (Q'.le_max'_left _ _)
      · exact Q'.le_trans' _ _ _
          (listQMaxZero_mono_on_local left right states
            (fun current hcurrent =>
              hall current (List.mem_cons_of_mem state hcurrent)))
          (Q'.le_max'_right _ _)

/-! ## 1. Literal combinatorial route factor -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) : Q' :=
  let w := trajectory.nome physicalScale
  let hw := Q'.le_of_lt (trajectory.nome_pos physicalScale)
  let K := transitionStart physicalScale + (cutoffOffset + 1)
  let routing := matchedEventualCanonicalTransportedRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
  if hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K then
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
    if (edge.1, edge.2) ∈ PositiveKernelChainIn.directedEdges path then
      Q'.ofNat (PositiveKernelChainIn.edgeLength path) *
        centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
          routing endpointPair.1 endpointPair.2 hfull.1 hfull.2
          edge.1 edge.2
    else 0
  else 0

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
        trajectory transitionStart physicalScale cutoffOffset
        edge endpointPair := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
  by_cases hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
  · rw [dif_pos hpair]
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path :=
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset).path
          endpointPair.1 endpointPair.2 hfull.1 hfull.2
    by_cases hedge : (edge.1, edge.2) ∈
        PositiveKernelChainIn.directedEdges path
    · rw [if_pos hedge]
      exact Q'.mul_nonneg _ _
        (ExpNeg.ofNat_nonneg' _)
        (residualRoutedDirectedEdgeMultiplicity_nonnegative
          (matchedEventualCanonicalTransportedRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset)
          endpointPair.1 endpointPair.2 hfull.1 hfull.2
          edge.1 edge.2)
    · rw [if_neg hedge]
      exact Q'.le_refl' 0
  · rw [dif_neg hpair]
    exact Q'.le_refl' 0

/-! ## 2. The path load factors by endpoint mass and route factor -/

theorem matchedEventualCanonicalTransportedBridgeNewEndpointPathLoad_eqv_stationaryWeight_mul_routeFactor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat)
    (hpair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
          (matchedEventualCanonicalTransportedRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset)
          endpointPair.1 endpointPair.2)
        edge.1 edge.2 ≈
      matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
          trajectory transitionStart physicalScale cutoffOffset
          edge endpointPair := by
  have hparts := List.mem_filter.mp hpair
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hparts.1
  let routing := matchedEventualCanonicalTransportedRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
  let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  let length := Q'.ofNat (PositiveKernelChainIn.edgeLength path)
  let multiplicity :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
      routing endpointPair.1 endpointPair.2 hfull.1 hfull.2
      edge.1 edge.2
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
  rw [dif_pos hfull.1, dif_pos hfull.2]
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
  rw [dif_pos hparts.1]
  change weightedDirectedEdgeLoad
      ((PositiveKernelChainIn.directedEdges path).map
        (fun currentEdge => (currentEdge, weight * length)))
      edge.1 edge.2 ≈
    weight *
      (if (edge.1, edge.2) ∈ PositiveKernelChainIn.directedEdges path then
        length * multiplicity
      else 0)
  by_cases hedge : (edge.1, edge.2) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [if_pos hedge]
    exact Q'.eqv_trans _ ((weight * length) * multiplicity) _
      (weightedDirectedEdgeLoad_constantMap_eqv_scalarMultiplicity_local
        (PositiveKernelChainIn.directedEdges path)
        (weight * length) edge.1 edge.2)
      (Q'.mul_assoc_eqv weight length multiplicity)
  · rw [if_neg hedge]
    exact Q'.eqv_trans _ (0 : Q') _
      (weightedDirectedEdgeLoad_constantMap_eqv_zero_of_not_mem_local
        (PositiveKernelChainIn.directedEdges path)
        (weight * length) edge.1 edge.2 hedge)
      (Q'.eqv_symm (Q'.mul_zero_eqv weight))

/-! ## 3. The transition term is endpoint mass times route/source demand -/

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficTransitionTerm_eqv_stationaryWeightRouteFactor_div_sourceWeight
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair endpointPair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).1
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).2
        endpointPair ≈
      Q'.divPos
          (matchedEventualCanonicalNewEndpointStationaryPairWeight
              trajectory transitionStart physicalScale cutoffOffset endpointPair *
            matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
              trajectory transitionStart physicalScale cutoffOffset
              (matchedEventualCanonicalCurrentPairToNext
                trajectory transitionStart physicalScale cutoffOffset pair)
              endpointPair)
          (centralPhysicalFiniteWeight
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1)) 0
            (matchedEventualCanonicalCurrentPairToNext
              trajectory transitionStart physicalScale cutoffOffset pair).1)
          (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
            ((mem_cartesian_iff _ _ _).mp
              (matchedEventualCanonicalCurrentPairToNext_mem
                trajectory transitionStart physicalScale cutoffOffset pair
                hpair)).1) := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  have hedgeMem := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hsource := (mem_cartesian_iff _ _ edge).mp hedgeMem |>.1
  have hparts := List.mem_filter.mp hendpointPair
  have hrelative :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand_eqv_transitionProduct
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      hsource edge.2 endpointPair hparts.1
  refine Q'.eqv_trans _
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      edge.1 edge.2 endpointPair) _ (Q'.eqv_symm hrelative) ?_
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
  rw [dif_pos hsource]
  exact divPos_eqv_congr_numerator_local
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPathLoad_eqv_stationaryWeight_mul_routeFactor
      trajectory transitionStart physicalScale cutoffOffset
      edge endpointPair hendpointPair)

/-! ## 4. Source-weighted conditional capacity is the raw kernel capacity -/

def matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  centralPhysicalFiniteWeight
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0 edge.1 *
    (HalfPow.half *
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        edge.1 edge.2)

def matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  HalfPow.half *
    centralPhysicalFiniteKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0
      edge.1 edge.2

theorem matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge_eqv_rawKernelCapacity
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hsource : edge.1 ∈ centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0) :
    matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge ≈
      matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
  refine Q'.eqv_trans _
    (HalfPow.half *
      (centralPhysicalFiniteWeight
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0 edge.1 *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0
          edge.1 edge.2)) _ ?_ ?_
  · q_ring
  exact Q'.mul_eqv_congr_left HalfPow.half _ _
    (centralPhysicalFiniteWeight_mul_conditional_eqv_kernel
      hsource edge.2)

/-! ## 5. Endpoint-free raw-kernel amplification -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) : Q' :=
  let capacity :=
    matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  if hcapacity : (0 : Q') < capacity then
    Q'.divPos
      (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
          trajectory transitionStart physicalScale cutoffOffset
          edge endpointPair)
      capacity hcapacity
  else 0

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
        trajectory transitionStart physicalScale cutoffOffset
        edge endpointPair := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
  by_cases hcapacity : (0 : Q') <
      matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge
  · rw [dif_pos hcapacity]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale))
        (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_nonnegative
          trajectory transitionStart physicalScale cutoffOffset
          edge endpointPair))
      (Q'.le_of_lt (Q'.recipPos_pos _ hcapacity))
  · rw [dif_neg hcapacity]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnMappedPair_eqv_stationaryWeight_mul_rawKernelAmplification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair endpointPair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair)
        endpointPair ≈
      matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset pair)
          endpointPair := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  have hedgeMem := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hsource := (mem_cartesian_iff _ _ edge).mp hedgeMem |>.1
  let sourceWeight := centralPhysicalFiniteWeight
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0 edge.1
  let conditionalCapacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0
      edge.1 edge.2
  let pairWeight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  let routeFactor :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
      trajectory transitionStart physicalScale cutoffOffset edge endpointPair
  let transformedLoad := Q'.divPos (pairWeight * routeFactor)
    sourceWeight
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
  have htransition :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficTransitionTerm_eqv_stationaryWeightRouteFactor_div_sourceWeight
      trajectory transitionStart physicalScale cutoffOffset
      pair endpointPair hpair hendpointPair
  refine Q'.eqv_trans _
    (matchedEventualCapacityDebtFromLoadOnPair
      trajectory transitionStart physicalScale (cutoffOffset + 1)
      edge transformedLoad) _ ?_ ?_
  · unfold
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
    exact matchedEventualCapacityDebtFromLoadOnPair_eqv_of_load_local
      trajectory transitionStart physicalScale (cutoffOffset + 1)
      edge htransition
  unfold matchedEventualCapacityDebtFromLoadOnPair
  change (if hcapacity : (0 : Q') < conditionalCapacity then
      Q'.divPos
        (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * transformedLoad)
        conditionalCapacity hcapacity
    else 0) ≈
      pairWeight *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
          trajectory transitionStart physicalScale cutoffOffset
          edge endpointPair
  have hsourceWeight : (0 : Q') < sourceWeight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  by_cases hconditionalCapacity : (0 : Q') < conditionalCapacity
  · rw [dif_pos hconditionalCapacity]
    unfold
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
      matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
    rw [dif_pos (Q'.mul_pos hsourceWeight hconditionalCapacity)]
    exact nested_divPos_endpoint_factor_cancellation_local
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale)
      pairWeight routeFactor sourceWeight conditionalCapacity
      hsourceWeight hconditionalCapacity
  · rw [dif_neg hconditionalCapacity]
    have hconditionalCapacity_le : conditionalCapacity <= (0 : Q') :=
      Int.not_lt.mp hconditionalCapacity
    have hproduct_le : sourceWeight * conditionalCapacity <= (0 : Q') :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ sourceWeight
          hconditionalCapacity_le (Q'.le_of_lt hsourceWeight))
        (Q'.le_of_eqv (Q'.mul_zero_eqv sourceWeight))
    have hproductNot : ¬ (0 : Q') < sourceWeight * conditionalCapacity := by
      intro hpositive
      exact (Int.not_lt_of_ge hproduct_le) hpositive
    unfold
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
      matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
    rw [dif_neg hproductNot]
    exact Q'.eqv_symm (Q'.mul_zero_eqv pairWeight)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnMappedPair_eqv_rawKernelAmplification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair endpointPair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair)
        endpointPair ≈
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair)
        endpointPair := by
  have hweight :=
    matchedEventualCanonicalNewEndpointStationaryPairWeight_pos
      trajectory transitionStart physicalScale cutoffOffset
      endpointPair hendpointPair
  apply Q'.mul_left_cancel_of_pos hweight
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair_eqv_stationaryWeight_mul_amplification
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair)
        endpointPair hendpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnMappedPair_eqv_stationaryWeight_mul_rawKernelAmplification
      trajectory transitionStart physicalScale cutoffOffset
      pair endpointPair hpair hendpointPair)

/-! ## 6. Located raw-kernel amplification maxima on the actual carriers -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximumOnEdge
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
      trajectory transitionStart physicalScale cutoffOffset edge)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (fun pair =>
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair))
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximumOnEdge_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximumOnEdge
  apply listQMaxZero_nonnegative
  intro endpointPair
  exact
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset edge endpointPair

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
  apply listQMaxZero_nonnegative
  intro pair
  exact
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximumOnEdge_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum_le_rawKernelAmplificationMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
  apply listQMaxZero_mono_on_local
  intro pair hpair
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximumOnEdge
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximumOnEdge
  apply listQMaxZero_mono_on_local
  intro endpointPair hendpointPair
  exact Q'.le_of_eqv
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnMappedPair_eqv_rawKernelAmplification
      trajectory transitionStart physicalScale cutoffOffset
      pair endpointPair hpair hendpointPair)

/-! ## 7. Raw-kernel new-block envelope and the existing debt consumer -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  (Q'.ofNat 2 *
      matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset) *
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope_le_rawKernelNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum_le_rawKernelAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset)
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_rawKernelNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_newBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope_le_rawKernelNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope_le_increment_add_merger_amplification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      (Q'.ofNat 2 *
          (slabParametricKCutoffIncrement
              (trajectory.nome physicalScale)
              (matchedEventualCanonicalCurrentCutoff
                transitionStart physicalScale cutoffOffset)
              (matchedEventualCanonicalLaterCutoff
                transitionStart physicalScale cutoffOffset)
              (centralExtent 0) +
            centralPhysicalFiniteNewComponentMergerMass
              (trajectory.nome physicalScale)
              (Q'.le_of_lt (trajectory.nome_pos physicalScale))
              (matchedEventualCanonicalCurrentCutoff
                transitionStart physicalScale cutoffOffset)
              (matchedEventualCanonicalLaterCutoff
                transitionStart physicalScale cutoffOffset) 0)) *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
  have hnew :=
    matchedEventualCanonicalLaterNewBlockMass_le_increment_add_merger
      trajectory transitionStart physicalScale cutoffOffset
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hnew (by decide)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ htwo
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope_le_increment_amplification_of_noMerger
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (hcheck : centralPhysicalFiniteNoComponentMergerCheck
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (matchedEventualCanonicalCurrentCutoff
        transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset) 0 = true) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      (Q'.ofNat 2 *
          slabParametricKCutoffIncrement
            (trajectory.nome physicalScale)
            (matchedEventualCanonicalCurrentCutoff
              transitionStart physicalScale cutoffOffset)
            (matchedEventualCanonicalLaterCutoff
              transitionStart physicalScale cutoffOffset)
            (centralExtent 0)) *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
  have hnew :=
    matchedEventualCanonicalLaterNewBlockMass_le_increment_of_noMerger
      trajectory transitionStart physicalScale cutoffOffset hcheck
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hnew (by decide)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ htwo
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 8. Raw-kernel inverse-square input and contraction to prior consumers -/

structure MatchedEventualCanonicalNewEndpointTrafficRawKernelInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficRawKernelInverseSquareControl.toWeightedControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficRawKernelInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficWeightedInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope_le_rawKernelNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset)
      (control.envelope_le cutoffOffset)

theorem MatchedEventualCanonicalNewEndpointTrafficRawKernelInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficRawKernelInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  control.toWeightedControl.debtMaximum_le cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointPathLoad_eqv_stationaryWeight_mul_routeFactor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficTransitionTerm_eqv_stationaryWeightRouteFactor_div_sourceWeight
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge_eqv_rawKernelCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnMappedPair_eqv_stationaryWeight_mul_rawKernelAmplification
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnMappedPair_eqv_rawKernelAmplification
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum_le_rawKernelAmplificationMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_rawKernelNewBlockDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope_le_increment_add_merger_amplification
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope_le_increment_amplification_of_noMerger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.MatchedEventualCanonicalNewEndpointTrafficRawKernelInverseSquareControl.toWeightedControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification.MatchedEventualCanonicalNewEndpointTrafficRawKernelInverseSquareControl.debtMaximum_le
