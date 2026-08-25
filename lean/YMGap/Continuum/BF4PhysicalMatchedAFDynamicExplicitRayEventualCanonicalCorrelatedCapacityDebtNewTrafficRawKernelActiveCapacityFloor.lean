/-
# Located positive capacity floor on the actual active new-traffic cells

The active raw-kernel factorization retains a maximum of reciprocal capacity
over exactly the used route/capacity cells.  This module takes the constructive
positive minimum of capacity on that same filtered list.  Active membership
already carries strict positivity, so no unused edge or nonpositive fallback
entry is inserted into the analytic carrier.

Reciprocal antitonicity bounds the active reciprocal-capacity maximum by the
reciprocal of this located active floor.  The result compiles into both the
actual routed-path envelope and the explicit ambient-path fallback, while
retaining the same exact new-debt observable.

No quantitative persistence of the active floor, route-growth estimate,
new-block-mass decay, inverse-square estimate, no-merger certificate,
continuum theory, or Clay conclusion is supplied.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or declaration marked noncomputable is
used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem recipPos_antitone_local
    {larger smaller : Q'}
    (larger_pos : (0 : Q') < larger)
    (smaller_pos : (0 : Q') < smaller)
    (smaller_le : smaller <= larger) :
    Q'.recipPos larger larger_pos <=
      Q'.recipPos smaller smaller_pos := by
  show (Q'.recipPos larger larger_pos).num *
      ((Q'.recipPos smaller smaller_pos).den : Int) <=
    (Q'.recipPos smaller smaller_pos).num *
      ((Q'.recipPos larger larger_pos).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_den,
    Q'.recipPos_num, Q'.recipPos_den]
  have cross : smaller.num * (larger.den : Int) <=
      larger.num * (smaller.den : Int) := smaller_le
  simpa only [Int.mul_comm] using cross

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

/-! ## 1. Active membership exposes strict route and capacity positivity -/

theorem matchedEventualCanonicalNewEndpointTrafficActiveCell_route_capacity_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hcell : cell ∈
      matchedEventualCanonicalNewEndpointTrafficActiveCells
        trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
          trajectory transitionStart physicalScale cutoffOffset cell ∧
      (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
          trajectory transitionStart physicalScale cutoffOffset cell := by
  have hfiltered := List.mem_filter.mp hcell
  have hactive := hfiltered.2
  unfold matchedEventualCanonicalNewEndpointTrafficActiveCellB at hactive
  exact of_decide_eq_true hactive

/-! ## 2. Positive minimum and reciprocal maximum on the same active list -/

def matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listPositiveMinOne
    (matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficActiveCells
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
  apply listPositiveMinOne_pos
  intro cell hcell
  exact
    (matchedEventualCanonicalNewEndpointTrafficActiveCell_route_capacity_pos
      trajectory transitionStart physicalScale cutoffOffset cell hcell).2

theorem matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_le_capacityOnCell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hcell : cell ∈
      matchedEventualCanonicalNewEndpointTrafficActiveCells
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  unfold matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
  exact listPositiveMinOne_le_of_mem
    (matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficActiveCells
      trajectory transitionStart physicalScale cutoffOffset)
    cell hcell

theorem matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell_le_reciprocalActiveFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hcell : cell ∈
      matchedEventualCanonicalNewEndpointTrafficActiveCells
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell
        trajectory transitionStart physicalScale cutoffOffset cell <=
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset) := by
  have hcapacity :=
    (matchedEventualCanonicalNewEndpointTrafficActiveCell_route_capacity_pos
      trajectory transitionStart physicalScale cutoffOffset cell hcell).2
  unfold
    matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell
  rw [dif_pos hcapacity]
  exact recipPos_antitone_local hcapacity
    (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_le_capacityOnCell
      trajectory transitionStart physicalScale cutoffOffset cell hcell)

theorem matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_le_reciprocalActiveFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset) := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact Q'.le_of_lt
      (Q'.recipPos_pos _
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))
  · intro cell hcell
    exact
      matchedEventualCanonicalNewEndpointTrafficCapacityReciprocalOnCell_le_reciprocalActiveFloor
        trajectory transitionStart physicalScale cutoffOffset cell hcell

/-! ## 3. Observable-connected path/capacity-floor envelopes -/

def matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))
    (Q'.mul_nonneg _ _
      (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
      (Q'.le_of_lt
        (Q'.recipPos_pos _
          (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
            trajectory transitionStart physicalScale cutoffOffset))))

theorem matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope_le_activeCapacityFloorPathEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_le_reciprocalActiveFloor
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
  · exact Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)

def matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope
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
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))
    (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope_le_activeCapacityFloorPathNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope_le_activeCapacityFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_activeCapacityFloorPathNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_pathFactorizedNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope_le_activeCapacityFloorPathNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 4. The explicit ambient-route fallback uses the same active floor -/

def matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorAmbientAmplificationEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope_le_activeCapacityFloorAmbientEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorAmbientAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorAmbientAmplificationEnvelope
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_le_reciprocalActiveFloor
        trajectory transitionStart physicalScale cutoffOffset)
      (Q'.le_of_lt
        (matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale_pos
          trajectory transitionStart physicalScale cutoffOffset))
  · exact Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)

/-! ## 5. Type-level inverse-square interface -/

structure MatchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathInverseSquareControl
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
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathInverseSquareControl.toPathFactorizedControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficPathFactorizedInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope_le_activeCapacityFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset)
      (control.envelope_le cutoffOffset)

theorem MatchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  control.toPathFactorizedControl.debtMaximum_le cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor.matchedEventualCanonicalNewEndpointTrafficActiveCell_route_capacity_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor.matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor.matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_le_reciprocalActiveFloor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor.matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope_le_activeCapacityFloorPathEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_activeCapacityFloorPathNewBlockDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor.matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope_le_activeCapacityFloorAmbientEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor.MatchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathInverseSquareControl.toPathFactorizedControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor.MatchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathInverseSquareControl.debtMaximum_le
