/-
# Observable-connected active-cell payment for matched new traffic

The preceding extrema route bounds the exact new-traffic debt by a product of
new-block mass, a worst routed path, and a worst reciprocal capacity.  That is
a valid fallback, but it discards the correlation between the stationary
weight of one actual endpoint pair and the capacity of the precise edge used
by its precise route.

This module retains that correlation.  A nonnegative allowance is attached to
each literal current-pair/new-endpoint cell.  On an active cell, the allowance
pays the exact stationary-weighted route numerator against that same cell's
source-weighted raw-kernel capacity.  Positive-denominator cancellation then
bounds the exact normalized debt term by the allowance.  Summing allowances
only along each actual endpoint row and taking the existing current-pair
maximum proves the unchanged exact new-traffic debt bound.

Thus no separate lower bound for a global or active capacity minimum, no
separate route maximum, and no replacement of actual endpoint mass by twice a
new-block mass is required on this path.  The row allowance estimate remains
an explicit quantitative field.  No such estimate, inverse-square decay,
no-merger certificate, continuum theory, or Clay conclusion is supplied.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local
    {State : Type} (left right : State -> Q') :
    forall states : List State,
      (forall state, state ∈ states -> left state <= right state) ->
      listQSum left states <= listQSum right states
  | [], _ => Q'.le_refl' 0
  | head :: tail, hall =>
      Q'.add_le_add
        (hall head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun state hstate =>
            hall state (List.mem_cons_of_mem head hstate)))

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

/-! ## 1. The exact stationary-weighted numerator on one literal cell -/

def matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointStationaryPairWeight
      trajectory transitionStart physicalScale cutoffOffset cell.2 *
    (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale *
      matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell)

theorem matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset cell := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
  exact Q'.mul_nonneg _ _
    (matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative
      trajectory transitionStart physicalScale cutoffOffset cell.2
      hendpointPair)
    (Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale))
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset cell.1)
        cell.2))

/-! ## 2. A row-summable allowance which pays each active cell -/

structure MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl
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
  allowance : Nat -> ((Nat × Nat) × (Nat × Nat)) -> Q'
  allowance_nonnegative : forall cutoffOffset cell,
    (0 : Q') <= allowance cutoffOffset cell
  active_payment : forall cutoffOffset cell,
    cell ∈ matchedEventualCanonicalNewEndpointTrafficActiveCells
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset cell <=
      allowance cutoffOffset cell *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
          trajectory transitionStart physicalScale cutoffOffset cell
  row_allowance_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    listQSum
        (fun endpointPair => allowance cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

/-! ## 3. Exact one-cell cancellation -/

theorem MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.debtTermOnMappedPair_le_allowance
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat)
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
      control.allowance cutoffOffset (pair, endpointPair) := by
  let cell : (Nat × Nat) × (Nat × Nat) := (pair, endpointPair)
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let route := matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
    trajectory transitionStart physicalScale cutoffOffset cell
  let capacity := matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
    trajectory transitionStart physicalScale cutoffOffset cell
  let allowance := control.allowance cutoffOffset cell
  have hterm :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnMappedPair_eqv_stationaryWeight_mul_rawKernelAmplification
      trajectory transitionStart physicalScale cutoffOffset
      pair endpointPair hpair hendpointPair
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hterm) ?_
  change weight *
      (if hcapacity : (0 : Q') < capacity then
        Q'.divPos (floor * route) capacity hcapacity
      else 0) <= allowance
  have hallowance0 : (0 : Q') <= allowance :=
    control.allowance_nonnegative cutoffOffset cell
  by_cases hcapacity : (0 : Q') < capacity
  · rw [dif_pos hcapacity]
    have hquotient :
        weight * Q'.divPos (floor * route) capacity hcapacity ≈
          Q'.divPos (weight * (floor * route)) capacity hcapacity := by
      unfold Q'.divPos
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv weight (floor * route)
          (Q'.recipPos capacity hcapacity))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hquotient) ?_
    apply Q'.divPos_le_of_le_mul
    by_cases hroute : (0 : Q') < route
    · have hcell : cell ∈
          matchedEventualCanonicalNewEndpointTrafficActiveCells
            trajectory transitionStart physicalScale cutoffOffset :=
        matchedEventualCanonicalNewEndpointTrafficCell_mem_activeCells
          trajectory transitionStart physicalScale cutoffOffset
          pair endpointPair hpair hendpointPair hroute hcapacity
      exact control.active_payment cutoffOffset cell hcell
    · have hroute0 : (0 : Q') <= route := by
        dsimp only [route, cell]
        exact
          matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_nonnegative
            trajectory transitionStart physicalScale cutoffOffset
            edge endpointPair
      have hrouteLe : route <= (0 : Q') := Int.not_lt.mp hroute
      have hrouteEq : route ≈ (0 : Q') :=
        Q'.eqv_of_le_le hrouteLe hroute0
      have hnumeratorZero : weight * (floor * route) ≈ (0 : Q') := by
        refine Q'.eqv_trans _ (weight * (floor * 0)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left weight _ _
            (Q'.mul_eqv_congr_left floor route 0 hrouteEq)
        refine Q'.eqv_trans _ (weight * 0) _
          (Q'.mul_eqv_congr_left weight _ _
            (Q'.mul_zero_eqv floor)) ?_
        exact Q'.mul_zero_eqv weight
      have hpaid0 : (0 : Q') <= allowance * capacity :=
        Q'.mul_nonneg _ _ hallowance0 (Q'.le_of_lt hcapacity)
      exact Q'.le_trans' _ (0 : Q') _
        (Q'.le_of_eqv hnumeratorZero) hpaid0
  · rw [dif_neg hcapacity]
    exact Q'.le_trans' _ (0 : Q') _
      (Q'.le_of_eqv (Q'.mul_zero_eqv weight)) hallowance0

/-! ## 4. Row sums and the exact current-pair maximum -/

theorem MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.debtOnMappedPair_le_rowAllowance
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) <=
      listQSum
        (fun endpointPair =>
          control.allowance cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let items :=
    matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset
  let term :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let allowance := fun endpointPair =>
    control.allowance cutoffOffset (pair, endpointPair)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_eqv_sum_terms
        trajectory transitionStart physicalScale cutoffOffset edge)) ?_
  exact listQSum_le_termwise_local term allowance items
    (fun endpointPair hendpointPair =>
      control.debtTermOnMappedPair_le_allowance cutoffOffset
        pair endpointPair hpair hendpointPair)

theorem MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.debtOnMappedPair_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  Q'.le_trans' _ _ _
    (control.debtOnMappedPair_le_rowAllowance cutoffOffset pair hpair)
    (control.row_allowance_le cutoffOffset pair hpair)

theorem MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact Q'.mul_nonneg _ _ control.coefficient_nonnegative
      (invSqTerm_nonneg control.offset
        control.offset_at_least_two cutoffOffset)
  · intro pair hpair
    exact control.debtOnMappedPair_le cutoffOffset pair hpair

/-! ## 5. Rejoin the existing exact-traffic compiler -/

def MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.toExactTrafficControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl
        trajectory transitionStart physicalScale)
    (oldTrafficDataCoefficient routeCoefficient : Q')
    (oldTrafficDataCoefficient_nonnegative :
      (0 : Q') <= oldTrafficDataCoefficient)
    (routeCoefficient_nonnegative : (0 : Q') <= routeCoefficient)
    (oldTrafficData_le : forall cutoffOffset : Nat,
      matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset <=
        oldTrafficDataCoefficient *
          invSqTerm control.offset
            control.offset_at_least_two cutoffOffset)
    (route_le : forall cutoffOffset : Nat,
      matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset <=
        routeCoefficient *
          invSqTerm control.offset
            control.offset_at_least_two cutoffOffset) :
    MatchedEventualCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  oldTrafficDataCoefficient := oldTrafficDataCoefficient
  newTrafficDebtCoefficient := control.coefficient
  routeCoefficient := routeCoefficient
  oldTrafficDataCoefficient_nonnegative :=
    oldTrafficDataCoefficient_nonnegative
  newTrafficDebtCoefficient_nonnegative := control.coefficient_nonnegative
  routeCoefficient_nonnegative := routeCoefficient_nonnegative
  oldTrafficData_le := oldTrafficData_le
  newTrafficDebt_le := control.debtMaximum_le
  route_le := route_le

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment.matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment.MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.debtTermOnMappedPair_le_allowance
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment.MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.debtOnMappedPair_le_rowAllowance
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment.MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.debtOnMappedPair_le
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment.MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.debtMaximum_le
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment.MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl.toExactTrafficControl
