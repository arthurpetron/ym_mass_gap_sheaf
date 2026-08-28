/-
# Edge-local amplification for exact adaptive traffic

The exact crossing-mass identity retains the endpoint paths using each later
carrier edge.  This module factors that local numerator into two independently
meaningful quantities:

* the stationary mass of genuinely new endpoint pairs; and
* the largest exact route factor per unit of literal raw-kernel capacity on
  the selected edge.

Unlike the sector-floor fallback, an edge carrying no adaptive route factor
contributes zero even when unrelated kernel entries elsewhere are tiny.  The
resulting new-block envelope exposes the precise analytic producer still
needed: an inverse-square bound on new mass times local route/capacity
amplification.

No such uniform bound, completed gap, continuum theory, or Clay conclusion is
asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCrossingMassCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
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

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem q_right_pos_of_mul_pos_local
    {left right : Q'}
    (hleft : (0 : Q') <= left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum : (0 : Int) <= left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  have hmulNonpos : left.num * right.num <= 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hleftNum hrightNonpos
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

/-! ## 1. Exact local route-factor maxima -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactor_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
          trajectory transitionStart physicalScale cutoffOffset)
        edge endpointPair := by
  unfold matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
  by_cases hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
  · rw [dif_pos hpair]
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path :=
      (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
        trajectory transitionStart physicalScale cutoffOffset).path
          endpointPair.1 endpointPair.2 hfull.1 hfull.2
    by_cases hedge : (edge.1, edge.2) ∈
        PositiveKernelChainIn.directedEdges path
    · rw [if_pos hedge]
      exact Q'.mul_nonneg _ _
        (ExpNeg.ofNat_nonneg' _)
        (residualRoutedDirectedEdgeMultiplicity_nonnegative
          (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
            trajectory transitionStart physicalScale cutoffOffset)
          endpointPair.1 endpointPair.2 hfull.1 hfull.2 edge.1 edge.2)
    · rw [if_neg hedge]
      exact Q'.le_refl' 0
  · rw [dif_neg hpair]
    exact Q'.le_refl' 0

def matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  listQMaxZero
    (matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
        trajectory transitionStart physicalScale cutoffOffset)
      edge)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    (0 : Q') <=
      matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
  apply listQMaxZero_nonnegative
  intro endpointPair
  exact
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactor_nonnegative
      trajectory transitionStart physicalScale cutoffOffset edge endpointPair

theorem matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactor_le_maximumOnEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
          trajectory transitionStart physicalScale cutoffOffset)
        edge endpointPair <=
      matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
  exact le_listQMaxZero_of_mem _ _ hendpointPair

/-! ## 2. Crossing mass is new-pair mass times local route amplification -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass_le_stationaryMass_mul_routeFactorMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass
        trajectory transitionStart physicalScale cutoffOffset edge <=
      matchedEventualCanonicalNewEndpointStationaryMass
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
          trajectory transitionStart physicalScale cutoffOffset edge := by
  let items := matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset
  let weight := fun endpointPair : Nat × Nat =>
    matchedEventualCanonicalLaterIndexWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair.1 *
      matchedEventualCanonicalLaterIndexWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair.2
  let factor :=
    matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
        trajectory transitionStart physicalScale cutoffOffset)
      edge
  let maximum :=
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  have hsum :
      listQSum (fun endpointPair => weight endpointPair * factor endpointPair) items <=
        listQSum (fun endpointPair => weight endpointPair * maximum) items :=
    listQSum_le_termwise_local _ _ items (fun endpointPair hendpointPair =>
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactor_le_maximumOnEdge
          trajectory transitionStart physicalScale cutoffOffset
          edge endpointPair hendpointPair)
        (matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative
          trajectory transitionStart physicalScale cutoffOffset
          endpointPair hendpointPair))
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass
    matchedEventualNewEndpointTrafficStationaryCrossingRouteMassForRouting
    matchedEventualNewEndpointTrafficStationaryCrossingRouteTermForRouting
    matchedEventualCanonicalNewEndpointStationaryMass
  change listQSum (fun endpointPair => weight endpointPair * factor endpointPair) items <=
    listQSum weight items * maximum
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (listQSum_mul_right weight maximum items))

theorem matchedEventualCanonicalNewEndpointStationaryMass_nonnegative_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <= matchedEventualCanonicalNewEndpointStationaryMass
      trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalNewEndpointStationaryMass
  apply listQSum_nonnegative_on
  intro endpointPair hendpointPair
  exact matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative
    trajectory transitionStart physicalScale cutoffOffset
    endpointPair hendpointPair

/-! ## 3. Normalize only by the capacity of the used edge -/

def matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  let rawCapacity :=
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  if hraw : (0 : Q') < rawCapacity then
    Q'.divPos
      (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
        matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
          trajectory transitionStart physicalScale cutoffOffset edge)
      rawCapacity hraw
  else 0

theorem matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    (0 : Q') <=
      matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge
  by_cases hraw : (0 : Q') <
      matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge
  · rw [dif_pos hraw]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale))
        (matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge_nonnegative
          trajectory transitionStart physicalScale cutoffOffset edge))
      (Q'.le_of_lt (Q'.recipPos_pos _ hraw))
  · rw [dif_neg hraw]
    exact Q'.le_refl' 0

def matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1))

theorem matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
  apply listQMaxZero_nonnegative
  intro edge
  exact
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge_nonnegative
      trajectory transitionStart physicalScale cutoffOffset edge

theorem matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass_localRawCapacityPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (hcapacity : (0 : Q') < HalfPow.half *
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        edge.1 edge.2) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass
          trajectory transitionStart physicalScale cutoffOffset edge <=
      (matchedEventualCanonicalNewEndpointStationaryMass
            trajectory transitionStart physicalScale cutoffOffset *
          matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
            trajectory transitionStart physicalScale cutoffOffset) *
        matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
          trajectory transitionStart physicalScale cutoffOffset edge := by
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let crossingMass :=
    matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass
      trajectory transitionStart physicalScale cutoffOffset edge
  let stationaryMass := matchedEventualCanonicalNewEndpointStationaryMass
    trajectory transitionStart physicalScale cutoffOffset
  let routeMaximum :=
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  let rawCapacity :=
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  let localAmplification :=
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  let maximumAmplification :=
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset
  have hmembers := (mem_cartesian_iff _ _ edge).mp hedge
  have hsource :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hmembers.1
  have hrawEq :=
    matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge_eqv_rawKernelCapacity
      trajectory transitionStart physicalScale cutoffOffset edge hmembers.1
  have hweighted : (0 : Q') <
      matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset edge.1 *
        (HalfPow.half * centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0
          edge.1 edge.2) :=
    Q'.mul_pos hsource hcapacity
  have hraw : (0 : Q') < rawCapacity :=
    Q'.pos_of_lt_of_le hweighted (Q'.le_of_eqv hrawEq)
  have hcrossing : crossingMass <= stationaryMass * routeMaximum :=
    matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass_le_stationaryMass_mul_routeFactorMaximum
      trajectory transitionStart physicalScale cutoffOffset edge
  have hfloor : (0 : Q') <= floor :=
    Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)
  have hstationary : (0 : Q') <= stationaryMass :=
    matchedEventualCanonicalNewEndpointStationaryMass_nonnegative_local
      trajectory transitionStart physicalScale cutoffOffset
  have hlocalMaximum : localAmplification <= maximumAmplification := by
    dsimp only [localAmplification, maximumAmplification]
    unfold matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
    exact le_listQMaxZero_of_mem _ _ hedge
  have hlocalCancel : localAmplification * rawCapacity ≈
      floor * routeMaximum := by
    unfold localAmplification
      matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge
    rw [dif_pos hraw]
    exact Q'.divPos_mul_eqv _ _ hraw
  have hscaledCrossing : floor * crossingMass <=
      floor * (stationaryMass * routeMaximum) :=
    Q'.mul_le_mul_of_nonneg_left _ _ floor hcrossing hfloor
  have hampScaled : stationaryMass * localAmplification <=
      stationaryMass * maximumAmplification :=
    Q'.mul_le_mul_of_nonneg_left _ _ stationaryMass
      hlocalMaximum hstationary
  have hrawScaled :
      (stationaryMass * localAmplification) * rawCapacity <=
        (stationaryMass * maximumAmplification) * rawCapacity :=
    Q'.mul_le_mul_of_nonneg_right _ _ rawCapacity hampScaled
      (Q'.le_of_lt hraw)
  have hleftEq : floor * (stationaryMass * routeMaximum) ≈
      (stationaryMass * localAmplification) * rawCapacity := by
    refine Q'.eqv_trans _ (stationaryMass * (floor * routeMaximum)) _ ?_ ?_
    · q_ring
    refine Q'.eqv_trans _ (stationaryMass * (localAmplification * rawCapacity)) _
      (Q'.mul_eqv_congr_left stationaryMass _ _ (Q'.eqv_symm hlocalCancel)) ?_
    q_ring
  exact Q'.le_trans' _ _ _ hscaledCrossing
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleftEq) hrawScaled)

/-! ## 4. The exact adaptive debt inherits the local envelope -/

def matchedEventualActivatedDeletedSupportExactAdaptiveStationaryLocalAmplificationAllowanceAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    MatchedEventualActivatedDeletedSupportExactAdaptiveCrossingRawCapacityAllowanceAt
      trajectory transitionStart physicalScale cutoffOffset where
  allowance :=
    matchedEventualCanonicalNewEndpointStationaryMass
          trajectory transitionStart physicalScale cutoffOffset *
      matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset
  allowance_nonnegative :=
    Q'.mul_nonneg _ _
      (matchedEventualCanonicalNewEndpointStationaryMass_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
  crossing_capacity_payment := by
    intro edge hedge hcapacity
    exact
      matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass_localRawCapacityPayment
        trajectory transitionStart physicalScale cutoffOffset
        edge hedge hcapacity

def matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  (Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
      trajectory transitionStart physicalScale cutoffOffset) *
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_newBlockLocalAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  have hstationary :=
    (matchedEventualActivatedDeletedSupportExactAdaptiveStationaryLocalAmplificationAllowanceAt
      trajectory transitionStart physicalScale cutoffOffset).exactAdaptiveDebtMaximum_le_allowance
  have hmass :=
    matchedEventualCanonicalNewEndpointStationaryMass_le_two_newMass
      trajectory transitionStart physicalScale cutoffOffset
  have hamp :=
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  exact Q'.le_trans' _ _ _ hstationary
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hmass hamp)

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope_le_increment_add_merger_amplification
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope
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
        matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope
  have hnew := matchedEventualCanonicalLaterNewBlockMass_le_increment_add_merger
    trajectory transitionStart physicalScale cutoffOffset
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hnew (by decide)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ htwo
    (matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope_le_increment_amplification_of_noMerger
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (hcheck : centralPhysicalFiniteNoComponentMergerCheck
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (matchedEventualCanonicalCurrentCutoff
        transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset) 0 = true) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      (Q'.ofNat 2 *
          slabParametricKCutoffIncrement
            (trajectory.nome physicalScale)
            (matchedEventualCanonicalCurrentCutoff
              transitionStart physicalScale cutoffOffset)
            (matchedEventualCanonicalLaterCutoff
              transitionStart physicalScale cutoffOffset)
            (centralExtent 0)) *
        matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope
  have hnew := matchedEventualCanonicalLaterNewBlockMass_le_increment_of_noMerger
    trajectory transitionStart physicalScale cutoffOffset hcheck
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hnew (by decide)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ htwo
    (matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass_le_stationaryMass_mul_routeFactorMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveCrossingRouteMass_localRawCapacityPayment
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_newBlockLocalAmplificationEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope_le_increment_add_merger_amplification
