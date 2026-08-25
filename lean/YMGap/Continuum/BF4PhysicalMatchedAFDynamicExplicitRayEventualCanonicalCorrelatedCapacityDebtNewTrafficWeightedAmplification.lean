/-
# Weighted-amplification compiler for matched dynamic new traffic

The exact new-traffic debt is a sum of normalized contributions on the actual
complementary endpoint list.  Each listed endpoint lies in the literal later
vacuum sector, so its stationary pair weight is strictly positive.  Division
by that weight therefore defines an exact route/capacity amplification, and
the original normalized contribution is exactly stationary weight times
amplification.

Constructive maxima over the same actual endpoint and current-edge carriers
then bound the exact debt by stationary endpoint mass times one amplification
maximum.  The preceding stationary-mass compiler contracts this further to
twice the later new-block mass, and then to the corrected-slab increment plus
the explicit component-merger residual.  No carrier, route, capacity, nome,
or observable is replaced.

This module supplies no quantitative amplification decay, no uniform
no-merger certificate, no inverse-square estimate, no continuum theory, and
no Clay conclusion.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification

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
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

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

/-! ## 1. Strictly positive stationary weight of every actual new pair -/

def matchedEventualCanonicalNewEndpointStationaryPairWeight
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat) : Q' :=
  matchedEventualCanonicalLaterIndexWeight
      trajectory transitionStart physicalScale cutoffOffset endpointPair.1 *
    matchedEventualCanonicalLaterIndexWeight
      trajectory transitionStart physicalScale cutoffOffset endpointPair.2

theorem matchedEventualCanonicalNewEndpointStationaryPairWeight_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat)
    (hpair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') < matchedEventualCanonicalNewEndpointStationaryPairWeight
      trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  have hparts := List.mem_filter.mp hpair
  have hsector :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hparts.1
  unfold matchedEventualCanonicalNewEndpointStationaryPairWeight
    matchedEventualCanonicalLaterIndexWeight
  exact Q'.mul_pos
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (by
        simpa only [matchedEventualCanonicalLaterCutoff] using hsector.1))
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (by
        simpa only [matchedEventualCanonicalLaterCutoff] using hsector.2))

theorem matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat)
    (hpair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') <= matchedEventualCanonicalNewEndpointStationaryPairWeight
      trajectory transitionStart physicalScale cutoffOffset endpointPair :=
  Q'.le_of_lt
    (matchedEventualCanonicalNewEndpointStationaryPairWeight_pos
      trajectory transitionStart physicalScale cutoffOffset endpointPair hpair)

/-! ## 2. Exact amplification and stationary-weight factorization -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) : Q' :=
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  if hweight : (0 : Q') < weight then
    Q'.divPos
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
        trajectory transitionStart physicalScale cutoffOffset edge endpointPair)
      weight hweight
  else 0

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair
        trajectory transitionStart physicalScale cutoffOffset
        edge endpointPair := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair
  by_cases hweight : (0 : Q') <
      matchedEventualCanonicalNewEndpointStationaryPairWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair
  · rw [dif_pos hweight]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
        edge endpointPair)
      (Q'.le_of_lt (Q'.recipPos_pos _ hweight))
  · rw [dif_neg hweight]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair_eqv_stationaryWeight_mul_amplification
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
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
        trajectory transitionStart physicalScale cutoffOffset
        edge endpointPair ≈
      matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair
          trajectory transitionStart physicalScale cutoffOffset
          edge endpointPair := by
  have hweight :=
    matchedEventualCanonicalNewEndpointStationaryPairWeight_pos
      trajectory transitionStart physicalScale cutoffOffset endpointPair hpair
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair
  rw [dif_pos hweight]
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.divPos_mul_eqv
        (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
          trajectory transitionStart physicalScale cutoffOffset
          edge endpointPair)
        (matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair)
        hweight))
    (Q'.mul_comm_eqv
      (Q'.divPos
        (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
          trajectory transitionStart physicalScale cutoffOffset
          edge endpointPair)
        (matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair)
        hweight)
      (matchedEventualCanonicalNewEndpointStationaryPairWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair))

/-! ## 3. Located amplification maxima on the actual carriers -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximumOnEdge
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair
      trajectory transitionStart physicalScale cutoffOffset edge)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (fun pair =>
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair))
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximumOnEdge_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximumOnEdge
  apply listQMaxZero_nonnegative
  intro endpointPair
  exact
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset edge endpointPair

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
  apply listQMaxZero_nonnegative
  intro pair
  exact
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximumOnEdge_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnMappedPair_le_stationaryWeight_mul_amplificationMaximum
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
        endpointPair <=
      matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let amplification :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair
      trajectory transitionStart physicalScale cutoffOffset edge endpointPair
  let edgeMaximum :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximumOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  let totalMaximum :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset
  have hampEdge : amplification <= edgeMaximum :=
    le_listQMaxZero_of_mem
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationOnPair
        trajectory transitionStart physicalScale cutoffOffset edge)
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)
      hendpointPair
  have hedgeTotal : edgeMaximum <= totalMaximum :=
    le_listQMaxZero_of_mem
      (fun currentPair =>
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximumOnEdge
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset currentPair))
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset)
      hpair
  have hampTotal : amplification <= totalMaximum :=
    Q'.le_trans' _ _ _ hampEdge hedgeTotal
  have hweight0 : (0 : Q') <=
      matchedEventualCanonicalNewEndpointStationaryPairWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair :=
    matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative
      trajectory transitionStart physicalScale cutoffOffset endpointPair
      hendpointPair
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair_eqv_stationaryWeight_mul_amplification
        trajectory transitionStart physicalScale cutoffOffset edge endpointPair
        hendpointPair))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hampTotal hweight0)

/-! ## 4. Exact debt bounded by weighted mass times amplification -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalNewEndpointStationaryMass
      trajectory transitionStart physicalScale cutoffOffset *
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope
    matchedEventualCanonicalNewEndpointStationaryMass
  exact Q'.mul_nonneg _ _
    (listQSum_nonnegative_on _ _
      (fun endpointPair hpair =>
        matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative
          trajectory transitionStart physicalScale cutoffOffset endpointPair
          hpair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnMappedPair_le_stationaryDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let items := matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset
  let term :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset
  let maximum :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset
  have hsum :
      listQSum term items <=
        listQSum (fun endpointPair => weight endpointPair * maximum) items :=
    listQSum_le_termwise_local term
      (fun endpointPair => weight endpointPair * maximum) items
      (fun endpointPair hendpointPair =>
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnMappedPair_le_stationaryWeight_mul_amplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset
          pair endpointPair hpair hendpointPair)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_eqv_sum_terms
        trajectory transitionStart physicalScale cutoffOffset edge)) ?_
  refine Q'.le_trans' _ _ _ hsum ?_
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope
    matchedEventualCanonicalNewEndpointStationaryMass
  change listQSum (fun endpointPair => weight endpointPair * maximum) items <=
    listQSum weight items * maximum
  exact Q'.le_of_eqv (listQSum_mul_right weight maximum items)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_stationaryDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
  · intro pair hpair
    exact
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnMappedPair_le_stationaryDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset pair hpair

/-! ## 5. Contract weighted mass to the exact new block -/

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
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
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope_le_newBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (matchedEventualCanonicalNewEndpointStationaryMass_le_two_newMass
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_newBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_stationaryDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope_le_newBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope_le_increment_add_merger_amplification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
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
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
  have hnew :=
    matchedEventualCanonicalLaterNewBlockMass_le_increment_add_merger
      trajectory transitionStart physicalScale cutoffOffset
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hnew (by decide)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ htwo
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope_le_increment_amplification_of_noMerger
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
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      (Q'.ofNat 2 *
          slabParametricKCutoffIncrement
            (trajectory.nome physicalScale)
            (matchedEventualCanonicalCurrentCutoff
              transitionStart physicalScale cutoffOffset)
            (matchedEventualCanonicalLaterCutoff
              transitionStart physicalScale cutoffOffset)
            (centralExtent 0)) *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
  have hnew :=
    matchedEventualCanonicalLaterNewBlockMass_le_increment_of_noMerger
      trajectory transitionStart physicalScale cutoffOffset hcheck
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hnew (by decide)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ htwo
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 6. Weighted inverse-square input and the unchanged consumers -/

structure MatchedEventualCanonicalNewEndpointTrafficWeightedInverseSquareControl
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
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

theorem MatchedEventualCanonicalNewEndpointTrafficWeightedInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficWeightedInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_newBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (control.envelope_le cutoffOffset)

structure MatchedEventualCanonicalTransportedCapacityDebtWeightedTrafficInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  newTraffic :
    MatchedEventualCanonicalNewEndpointTrafficWeightedInverseSquareControl
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

def MatchedEventualCanonicalTransportedCapacityDebtWeightedTrafficInverseSquareControl.toExactTrafficControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalTransportedCapacityDebtWeightedTrafficInverseSquareControl
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

structure MatchedEventualCanonicalCapacityDebtWeightedTrafficRegionalInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  transport :
    MatchedEventualCanonicalTransportedCapacityDebtWeightedTrafficInverseSquareControl
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

def MatchedEventualCanonicalCapacityDebtWeightedTrafficRegionalInverseSquareControl.toExactTrafficRegionalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtWeightedTrafficRegionalInverseSquareControl
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

def MatchedEventualCanonicalCapacityDebtWeightedTrafficRegionalInverseSquareControl.toTotalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtWeightedTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtInverseSquareControl
      trajectory transitionStart physicalScale :=
  control.toExactTrafficRegionalControl.toTotalControl

def MatchedEventualCanonicalCapacityDebtWeightedTrafficRegionalInverseSquareControl.toTotalDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtWeightedTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale :=
  control.toTotalControl.toTotalDeficitTail

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification.matchedEventualCanonicalNewEndpointStationaryPairWeight_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair_eqv_stationaryWeight_mul_amplification
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnMappedPair_le_stationaryDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_stationaryDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficStationaryDebtEnvelope_le_newBlockDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope_le_increment_add_merger_amplification
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficNewBlockDebtEnvelope_le_increment_amplification_of_noMerger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification.MatchedEventualCanonicalNewEndpointTrafficWeightedInverseSquareControl.debtMaximum_le
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification.MatchedEventualCanonicalCapacityDebtWeightedTrafficRegionalInverseSquareControl.toTotalDeficitTail
