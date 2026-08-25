/-
# Active-cell factorization of matched dynamic raw-kernel amplification

The raw-kernel compiler removes the endpoint stationary-weight denominator,
but its located maximum still couples route geometry to reciprocal capacity.
This module filters the literal Cartesian product of mapped current pairs and
actual new endpoint pairs to exactly those cells where both the route factor
and source-weighted conditional capacity are strictly positive.  Those are
precisely the cells on which the raw-kernel amplification can be nonzero.

Separate constructive maxima of the route factor and reciprocal capacity are
then sufficient on this active carrier.  No unused physical edge contributes
to the reciprocal-capacity maximum.  The resulting factorized envelope still
targets the same exact new-debt observable and contracts to the preceding
raw-kernel inverse-square interface.

This module supplies no uniform route bound, raw-kernel floor, inverse-square
estimate, no-merger certificate, continuum theory, or Clay conclusion.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
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
open YMGap.Continuum.SummableInverseSquare

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

/-! ## 1. Literal active route/capacity cells -/

def matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
    trajectory transitionStart physicalScale cutoffOffset
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset cell.1)
    cell.2

def matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
    trajectory transitionStart physicalScale cutoffOffset
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset cell.1)

def matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  let capacity :=
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
      trajectory transitionStart physicalScale cutoffOffset cell
  if hcapacity : (0 : Q') < capacity then
    Q'.recipPos capacity hcapacity
  else 0

def matchedEventualCanonicalNewEndpointTrafficActiveCellB
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Bool :=
  decide
    ((0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
          trajectory transitionStart physicalScale cutoffOffset cell ∧
      (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
          trajectory transitionStart physicalScale cutoffOffset cell)

def matchedEventualCanonicalNewEndpointTrafficActiveCells
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    List ((Nat × Nat) × (Nat × Nat)) :=
  (cartesian
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)).filter
    (matchedEventualCanonicalNewEndpointTrafficActiveCellB
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficCell_mem_activeCells
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
        trajectory transitionStart physicalScale cutoffOffset)
    (hroute : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (hcapacity : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair)) :
    (pair, endpointPair) ∈
      matchedEventualCanonicalNewEndpointTrafficActiveCells
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalNewEndpointTrafficActiveCells
  apply List.mem_filter.mpr
  constructor
  · exact (mem_cartesian_iff _ _ _).mpr ⟨hpair, hendpointPair⟩
  · unfold matchedEventualCanonicalNewEndpointTrafficActiveCellB
    exact decide_eq_true ⟨hroute, hcapacity⟩

/-! ## 2. Independent maxima on exactly the active cells -/

def matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficActiveCells
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficActiveCells
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell
  by_cases hcapacity : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
        trajectory transitionStart physicalScale cutoffOffset cell
  · rw [dif_pos hcapacity]
    exact Q'.le_of_lt (Q'.recipPos_pos _ hcapacity)
  · rw [dif_neg hcapacity]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum
  apply listQMaxZero_nonnegative
  intro cell
  exact
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset cell.1)
      cell.2

theorem matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum
  apply listQMaxZero_nonnegative
  intro cell
  exact
    matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell_nonnegative
      trajectory transitionStart physicalScale cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum
        trajectory transitionStart physicalScale cutoffOffset *
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum
        trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))
    (Q'.mul_nonneg _ _
      (matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

/-! ## 3. Pointwise and maximum factorization -/

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnMappedPair_le_activeFactorizedEnvelope
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
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair)
        endpointPair <=
      matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  let cell : (Nat × Nat) × (Nat × Nat) := (pair, endpointPair)
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let route :=
    matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
      trajectory transitionStart physicalScale cutoffOffset cell
  let capacity :=
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
      trajectory transitionStart physicalScale cutoffOffset cell
  let routeMaximum :=
    matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum
      trajectory transitionStart physicalScale cutoffOffset
  let reciprocalMaximum :=
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum
      trajectory transitionStart physicalScale cutoffOffset
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let bound :=
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset
  have hroute0 : (0 : Q') <= route := by
    dsimp only [route, cell]
    exact
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset edge endpointPair
  have hbound0 : (0 : Q') <= bound :=
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  change (if hcapacity : (0 : Q') < capacity then
      Q'.divPos (floor * route) capacity hcapacity
    else 0) <= bound
  by_cases hroute : (0 : Q') < route
  · by_cases hcapacity : (0 : Q') < capacity
    · rw [dif_pos hcapacity]
      have hcell : cell ∈
          matchedEventualCanonicalNewEndpointTrafficActiveCells
            trajectory transitionStart physicalScale cutoffOffset := by
        exact
          matchedEventualCanonicalNewEndpointTrafficCell_mem_activeCells
            trajectory transitionStart physicalScale cutoffOffset
            pair endpointPair hpair hendpointPair hroute hcapacity
      have hrouteLe : route <= routeMaximum := by
        unfold routeMaximum
        exact le_listQMaxZero_of_mem
          (matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
            trajectory transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalNewEndpointTrafficActiveCells
            trajectory transitionStart physicalScale cutoffOffset)
          hcell
      have hreciprocalLe : Q'.recipPos capacity hcapacity <=
          reciprocalMaximum := by
        unfold reciprocalMaximum
        have hmaximum := le_listQMaxZero_of_mem
          (matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell
            trajectory transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalNewEndpointTrafficActiveCells
            trajectory transitionStart physicalScale cutoffOffset)
          hcell
        simpa only [
          matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell,
          capacity, dif_pos hcapacity] using hmaximum
      have hproduct : route * Q'.recipPos capacity hcapacity <=
          routeMaximum * reciprocalMaximum :=
        Q'.mul_le_mul_of_nonneg hrouteLe hreciprocalLe
          (matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum_nonnegative
            trajectory transitionStart physicalScale cutoffOffset)
          (Q'.le_of_lt (Q'.recipPos_pos capacity hcapacity))
      unfold Q'.divPos
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_assoc_eqv floor route
            (Q'.recipPos capacity hcapacity)))
        (Q'.mul_le_mul_of_nonneg_left _ _ floor hproduct
          (Q'.le_of_lt
            (matchedEventualCanonicalSupportSharedFloor_pos
              trajectory transitionStart physicalScale)))
    · rw [dif_neg hcapacity]
      exact hbound0
  · have hrouteLe : route <= (0 : Q') := Int.not_lt.mp hroute
    have hrouteEq : route ≈ (0 : Q') :=
      Q'.eqv_of_le_le hrouteLe hroute0
    by_cases hcapacity : (0 : Q') < capacity
    · rw [dif_pos hcapacity]
      unfold Q'.divPos
      have hnum : floor * route ≈ (0 : Q') :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left floor route 0 hrouteEq)
          (Q'.mul_zero_eqv floor)
      have hzero :
          (floor * route) * Q'.recipPos capacity hcapacity ≈
            (0 : Q') :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (floor * route) 0
            (Q'.recipPos capacity hcapacity) hnum)
          (Q'.zero_mul_eqv _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero) hbound0
    · rw [dif_neg hcapacity]
      exact hbound0

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum_le_activeFactorizedEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact
      matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
  · intro pair hpair
    unfold
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximumOnEdge
    apply listQMaxZero_le_of_member_bound_local
    · exact
        matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope_nonnegative
          trajectory transitionStart physicalScale cutoffOffset
    · intro endpointPair hendpointPair
      exact
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnMappedPair_le_activeFactorizedEnvelope
          trajectory transitionStart physicalScale cutoffOffset
          pair endpointPair hpair hendpointPair

/-! ## 4. Factorized new-block debt and contraction to prior consumers -/

def matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope
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
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))
    (matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope_le_activeFactorizedNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum_le_activeFactorizedEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_activeFactorizedNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_rawKernelNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope_le_activeFactorizedNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

structure MatchedEventualCanonicalNewEndpointTrafficActiveFactorizedInverseSquareControl
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
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficActiveFactorizedInverseSquareControl.toRawKernelControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveFactorizedInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficRawKernelInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope_le_activeFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset)
      (control.envelope_le cutoffOffset)

theorem MatchedEventualCanonicalNewEndpointTrafficActiveFactorizedInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveFactorizedInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  control.toRawKernelControl.debtMaximum_le cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization.matchedEventualCanonicalNewEndpointTrafficCell_mem_activeCells
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnMappedPair_le_activeFactorizedEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationMaximum_le_activeFactorizedEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelNewBlockDebtEnvelope_le_activeFactorizedNewBlockDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_activeFactorizedNewBlockDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization.MatchedEventualCanonicalNewEndpointTrafficActiveFactorizedInverseSquareControl.toRawKernelControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization.MatchedEventualCanonicalNewEndpointTrafficActiveFactorizedInverseSquareControl.debtMaximum_le
