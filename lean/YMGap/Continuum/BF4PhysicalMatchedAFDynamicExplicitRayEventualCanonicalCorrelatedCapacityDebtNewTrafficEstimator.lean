/-
# Factorized estimator for matched dynamic new-endpoint traffic

The exact nonnegative new-traffic debt is still a finite sum hidden inside a
load.  This module distributes the unchanged shared floor and matched
conditional-kernel normalization through that literal complementary endpoint
list.  The debt is exactly the sum of normalized endpoint contributions.

The sum is then bounded by exactly one carrier-cardinality factor times the
located maximum normalized contribution, first on one mapped current edge and
then over the literal current edge carrier.  This exposes two independently
estimable quantities without replacing the observable:

* the number of genuinely new residual endpoint pairs; and
* the largest normalized routed contribution of one such pair to one mapped
  current edge.

An inverse-square estimate on their product compiles into the existing exact-
new-debt, six-leaf traffic, regional, and total-tail controls.  No quantitative
estimate, continuum theory, or Clay conclusion is supplied.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQMaxZero_le_of_member_bound_local
    {State : Type} (value : State -> Q') (bound : Q') :
    forall states : List State,
      (0 : Q') <= bound ->
      (forall state, state ∈ states -> value state <= bound) ->
      listQMaxZero value states <= bound
  | [], hbound, _ => hbound
  | head :: tail, hbound, hall => by
      unfold listQMaxZero
      exact (Q'.max'_le_iff' _ _ _).mpr
        ⟨hall head List.mem_cons_self,
          listQMaxZero_le_of_member_bound_local value bound tail hbound
            (fun state hstate =>
              hall state (List.mem_cons_of_mem head hstate))⟩

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
        (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound)

private theorem listQSum_divPos_eqv_divPos_listQSum_local
    {A : Type} (value : A -> Q') (denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    forall items : List A,
      listQSum
          (fun item => Q'.divPos (value item) denominator hdenominator)
          items ≈
        Q'.divPos (listQSum value items) denominator hdenominator
  | [] => by
      unfold Q'.divPos
      exact Q'.eqv_symm
        (Q'.zero_mul_eqv (Q'.recipPos denominator hdenominator))
  | first :: rest => by
      unfold listQSum
      refine Q'.eqv_trans _
        (Q'.divPos (value first) denominator hdenominator +
          Q'.divPos (listQSum value rest) denominator hdenominator) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (listQSum_divPos_eqv_divPos_listQSum_local
            value denominator hdenominator rest)
      unfold Q'.divPos
      exact Q'.eqv_symm
        (Q'.add_mul_eqv
          (value first) (listQSum value rest)
          (Q'.recipPos denominator hdenominator))

/-! ## 1. Literal normalized contribution of one new endpoint pair -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) : Q' :=
  matchedEventualCapacityDebtFromLoadOnPair
    trajectory transitionStart physicalScale (cutoffOffset + 1) edge
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      edge.1 edge.2 endpointPair)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
        trajectory transitionStart physicalScale cutoffOffset
        edge endpointPair := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
  apply matchedEventualCapacityDebtFromLoadOnPair_nonnegative
  exact residualRoutedPathPairConditionalTransitionProductTerm_nonnegative
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset)
    edge.1 edge.2 endpointPair

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_eqv_sum_terms
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge ≈
      listQSum
        (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
          trajectory transitionStart physicalScale cutoffOffset edge)
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) := by
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))
      0 edge.1 edge.2
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let term :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      edge.1 edge.2
  let items := matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset
  change matchedEventualCapacityDebtFromLoadOnPair
      trajectory transitionStart physicalScale (cutoffOffset + 1) edge
      (listQSum term items) ≈
    listQSum
      (fun item =>
        matchedEventualCapacityDebtFromLoadOnPair
          trajectory transitionStart physicalScale (cutoffOffset + 1) edge
          (term item)) items
  unfold matchedEventualCapacityDebtFromLoadOnPair
  change (if h : (0 : Q') < capacity then
      Q'.divPos (floor * listQSum term items) capacity h
    else 0) ≈
    listQSum
      (fun item => if h : (0 : Q') < capacity then
        Q'.divPos (floor * term item) capacity h
      else 0) items
  by_cases hcapacity : (0 : Q') < capacity
  · simp only [hcapacity, dif_pos]
    have hscaled := listQSum_mul_left floor term items
    have hdiv := listQSum_divPos_eqv_divPos_listQSum_local
      (fun item => floor * term item) capacity hcapacity items
    refine Q'.eqv_trans _
      (Q'.divPos
        (listQSum (fun item => floor * term item) items)
        capacity hcapacity) _ ?_ ?_
    · unfold Q'.divPos
      exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hscaled)
    exact Q'.eqv_symm hdiv
  · simp only [hcapacity]
    exact Q'.eqv_symm (listQSum_zero items)

/-! ## 2. Located endpoint-term maxima and the count-times-maximum bound -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximumOnEdge
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
      trajectory transitionStart physicalScale cutoffOffset edge)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (fun pair =>
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair))
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalTransportedBridgeNewEndpointPairCount
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  Q'.ofNat
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset).length

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalTransportedBridgeNewEndpointPairCount
      trajectory transitionStart physicalScale cutoffOffset *
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximumOnEdge_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximumOnEdge
  apply listQMaxZero_nonnegative
  intro endpointPair
  exact
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset edge endpointPair

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum
  apply listQMaxZero_nonnegative
  intro pair
  exact
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximumOnEdge_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointPairCount_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointPairCount
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalTransportedBridgeNewEndpointPairCount
  exact ExpNeg.ofNat_nonneg' _

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
  exact Q'.mul_nonneg _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairCount_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnMappedPair_le_envelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let items := matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset
  let value :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let edgeMaximum :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximumOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  let totalMaximum :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum
      trajectory transitionStart physicalScale cutoffOffset
  have hedgeMaximum_le : edgeMaximum <= totalMaximum :=
    le_listQMaxZero_of_mem
      (fun currentPair =>
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximumOnEdge
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset currentPair))
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset) hpair
  have hvalue_le : forall endpointPair,
      endpointPair ∈ items -> value endpointPair <= totalMaximum := by
    intro endpointPair hendpointPair
    exact Q'.le_trans' _ _ _
      (le_listQMaxZero_of_mem value items hendpointPair)
      hedgeMaximum_le
  have hsum :
      listQSum value items <= Q'.ofNat items.length * totalMaximum :=
    listQSum_le_length_mul_local value
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
      items hvalue_le
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_eqv_sum_terms
        trajectory transitionStart physicalScale cutoffOffset edge))
    hsum

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_envelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
  · intro pair hpair
    exact
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnMappedPair_le_envelope
        trajectory transitionStart physicalScale cutoffOffset pair hpair

theorem matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum_le_envelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum_le_exactDebtMaximum
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_envelope
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 3. Factorized inverse-square input and contraction to the total tail -/

structure MatchedEventualCanonicalNewEndpointTrafficFactorizedInverseSquareControl
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
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

theorem MatchedEventualCanonicalNewEndpointTrafficFactorizedInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficFactorizedInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_envelope
      trajectory transitionStart physicalScale cutoffOffset)
    (control.envelope_le cutoffOffset)

structure MatchedEventualCanonicalTransportedCapacityDebtFactorizedTrafficInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  newTraffic :
    MatchedEventualCanonicalNewEndpointTrafficFactorizedInverseSquareControl
      trajectory transitionStart physicalScale
  oldTrafficDataCoefficient : Q'
  routeCoefficient : Q'
  oldTrafficDataCoefficient_nonnegative :
    (0 : Q') <= oldTrafficDataCoefficient
  routeCoefficient_nonnegative : (0 : Q') <= routeCoefficient
  oldTrafficData_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      oldTrafficDataCoefficient *
        invSqTerm newTraffic.offset
          newTraffic.offset_at_least_two cutoffOffset
  route_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      routeCoefficient *
        invSqTerm newTraffic.offset
          newTraffic.offset_at_least_two cutoffOffset

def MatchedEventualCanonicalTransportedCapacityDebtFactorizedTrafficInverseSquareControl.toExactTrafficControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalTransportedCapacityDebtFactorizedTrafficInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.newTraffic.offset
  offset_at_least_two := control.newTraffic.offset_at_least_two
  oldTrafficDataCoefficient := control.oldTrafficDataCoefficient
  newTrafficDebtCoefficient := control.newTraffic.coefficient
  routeCoefficient := control.routeCoefficient
  oldTrafficDataCoefficient_nonnegative :=
    control.oldTrafficDataCoefficient_nonnegative
  newTrafficDebtCoefficient_nonnegative :=
    control.newTraffic.coefficient_nonnegative
  routeCoefficient_nonnegative := control.routeCoefficient_nonnegative
  oldTrafficData_le := control.oldTrafficData_le
  newTrafficDebt_le := control.newTraffic.debtMaximum_le
  route_le := control.route_le

structure MatchedEventualCanonicalCapacityDebtFactorizedTrafficRegionalInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  transport :
    MatchedEventualCanonicalTransportedCapacityDebtFactorizedTrafficInverseSquareControl
      trajectory transitionStart physicalScale
  oldNewCoefficient : Q'
  newOldCoefficient : Q'
  newNewCoefficient : Q'
  oldNewCoefficient_nonnegative : (0 : Q') <= oldNewCoefficient
  newOldCoefficient_nonnegative : (0 : Q') <= newOldCoefficient
  newNewCoefficient_nonnegative : (0 : Q') <= newNewCoefficient
  oldNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      oldNewCoefficient *
        invSqTerm transport.newTraffic.offset
          transport.newTraffic.offset_at_least_two cutoffOffset
  newOld_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newOldCoefficient *
        invSqTerm transport.newTraffic.offset
          transport.newTraffic.offset_at_least_two cutoffOffset
  newNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newNewCoefficient *
        invSqTerm transport.newTraffic.offset
          transport.newTraffic.offset_at_least_two cutoffOffset

def MatchedEventualCanonicalCapacityDebtFactorizedTrafficRegionalInverseSquareControl.toExactTrafficRegionalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtFactorizedTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl
      trajectory transitionStart physicalScale where
  transport := control.transport.toExactTrafficControl
  oldNewCoefficient := control.oldNewCoefficient
  newOldCoefficient := control.newOldCoefficient
  newNewCoefficient := control.newNewCoefficient
  oldNewCoefficient_nonnegative := control.oldNewCoefficient_nonnegative
  newOldCoefficient_nonnegative := control.newOldCoefficient_nonnegative
  newNewCoefficient_nonnegative := control.newNewCoefficient_nonnegative
  oldNew_le := control.oldNew_le
  newOld_le := control.newOld_le
  newNew_le := control.newNew_le

def MatchedEventualCanonicalCapacityDebtFactorizedTrafficRegionalInverseSquareControl.toTotalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtFactorizedTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtInverseSquareControl
      trajectory transitionStart physicalScale :=
  control.toExactTrafficRegionalControl.toTotalControl

def MatchedEventualCanonicalCapacityDebtFactorizedTrafficRegionalInverseSquareControl.toTotalDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtFactorizedTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale :=
  control.toTotalControl.toTotalDeficitTail

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_eqv_sum_terms
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnMappedPair_le_envelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_envelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator.matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum_le_envelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator.MatchedEventualCanonicalNewEndpointTrafficFactorizedInverseSquareControl.debtMaximum_le
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator.MatchedEventualCanonicalTransportedCapacityDebtFactorizedTrafficInverseSquareControl.toExactTrafficControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator.MatchedEventualCanonicalCapacityDebtFactorizedTrafficRegionalInverseSquareControl.toTotalControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator.MatchedEventualCanonicalCapacityDebtFactorizedTrafficRegionalInverseSquareControl.toTotalDeficitTail
