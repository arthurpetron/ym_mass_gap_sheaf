/-
# Old--new used-route sector-capacity fallback

The face-specific path-square fallback is independent of the selected mapped
current row.  It can therefore remain positive on a row unused by every
old--new endpoint route, where no positive capacity conclusion is available.
This module retains the row-local route maximum until activity has been
certified.

Strict positivity of that finite maximum constructively produces a literal
old--new endpoint with positive routed edge occurrence.  The carried positive-
kernel path then places the mapped current edge in the later vacuum sector and
proves its raw kernel entry positive.  Half the later sector edge floor is
therefore below the raw capacity of exactly that row.  If the route maximum is
zero, the desired raw-capacity estimate instead follows from nonnegativity and
does not demand any capacity floor.

The resulting Type-level compilers accept a coarser sector-floor estimate and
return the preceding exact row-local raw-capacity controls.  No claim is made
that every mapped row has positive capacity, and no cutoff-uniform sector-floor
bound, mass decay, inverse-square estimate, no-merger theorem, continuum
theory, or Clay conclusion is supplied.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or declaration marked noncomputable is
used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private def oldNewShellPairDecidable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    Decidable
      (MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold MatchedEventualCanonicalPairInOldNewShell
    MatchedEventualCanonicalIndexInNewShell
  infer_instance

/-! ## 1. A positive finite maximum has a literal positive witness -/

private theorem exists_pos_of_listQMaxZero_pos_local
    {A : Type} (value : A -> Q') : forall items : List A,
      (0 : Q') <
          BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero value items ->
      Exists fun item => item ∈ items ∧ (0 : Q') < value item
  | [], hpositive => by
      unfold BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero at hpositive
      exact absurd hpositive (by decide)
  | head :: tail, hpositive => by
      unfold BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero Q'.max'
        at hpositive
      by_cases hle : value head <=
          BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero value tail
      · rw [if_pos hle] at hpositive
        obtain ⟨item, hitem, hitemPositive⟩ :=
          exists_pos_of_listQMaxZero_pos_local value tail hpositive
        exact ⟨item, List.mem_cons_of_mem head hitem, hitemPositive⟩
      · rw [if_neg hle] at hpositive
        exact ⟨head, List.mem_cons_self, hpositive⟩

/-! ## 2. Positive old--new row traffic certifies the mapped raw edge -/

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactor_pos_mappedEdge_mem_sector_and_kernel_pos
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
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair)) :
    let edge := matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset pair
    edge.1 ∈ centralPhysicalFiniteVacuumSectorIndices
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0 ∧
      edge.2 ∈ centralPhysicalFiniteVacuumSectorIndices
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0 ∧
      (0 : Q') < centralPhysicalFiniteKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0
          edge.1 edge.2 := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  have hedgeCarrier := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hendpointFiltered := List.mem_filter.mp hendpointPair
  have hresidual := hendpointFiltered.1
  let hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hresidual
  let routing := matchedEventualCanonicalTransportedRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
  let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
  have hrouteUnderlying : (0 : Q') <
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
        trajectory transitionStart physicalScale cutoffOffset edge endpointPair := by
    letI := oldNewShellPairDecidable
      trajectory transitionStart physicalScale cutoffOffset endpointPair
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance at hroute
    by_cases hface : MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale cutoffOffset endpointPair
    · rw [if_pos hface] at hroute
      simpa only [edge] using hroute
    · rw [if_neg hface] at hroute
      exact absurd hroute (by decide)
  have hedge : (edge.1, edge.2) ∈
      PositiveKernelChainIn.directedEdges path := by
    unfold
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
      at hrouteUnderlying
    rw [dif_pos hresidual] at hrouteUnderlying
    by_cases hedge : (edge.1, edge.2) ∈
        PositiveKernelChainIn.directedEdges path
    · exact hedge
    · rw [if_neg hedge] at hrouteUnderlying
      exact absurd hrouteUnderlying (by decide)
  have hsupport := PositiveKernelChainIn.directedEdges_mem_support
    hfull.1 path (edge.1, edge.2) hedge
  have hkernel := PositiveKernelChainIn.directedEdges_kernel_pos
    path (edge.1, edge.2) hedge
  exact ⟨hsupport.1, hsupport.2, hkernel⟩

theorem matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactor_pos
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
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair)) :
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  have hdata :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactor_pos_mappedEdge_mem_sector_and_kernel_pos
      trajectory transitionStart physicalScale cutoffOffset pair endpointPair
      hpair hendpointPair hroute
  dsimp only at hdata
  have hfloorEntry :=
    centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0
      edge.1 edge.2 hdata.1 hdata.2.1 hdata.2.2
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
    hfloorEntry (by decide)
  have heq :=
    matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge_eqv_rawKernelCapacity
      trajectory transitionStart physicalScale cutoffOffset edge hdata.1
  have hrawLeSource := Q'.ge_of_eqv heq
  unfold
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
    at hrawLeSource
  unfold
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
  exact Q'.le_trans' _ _ _ hscaled hrawLeSource

theorem matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactorMaximum_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hmaximum : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair) :
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
    at hmaximum
  have hwitness : Exists fun endpointPair : Nat × Nat =>
      endpointPair ∈
          matchedEventualCanonicalTransportedBridgeNewEndpointPairs
            trajectory transitionStart physicalScale cutoffOffset ∧
        (0 : Q') <
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
            trajectory transitionStart physicalScale cutoffOffset
            (pair, endpointPair) := by
    apply exists_pos_of_listQMaxZero_pos_local
      (fun endpointPair =>
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair))
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)
    exact hmaximum
  obtain ⟨endpointPair, hendpointPair, hroute⟩ := hwitness
  exact
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactor_pos
      trajectory transitionStart physicalScale cutoffOffset pair endpointPair
      hpair hendpointPair hroute

/-! ## 3. The inactive-row branch needs no positive capacity premise -/

private theorem matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_nonnegative_local
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
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  have hedge := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hsource := (mem_cartesian_iff _ _ _).mp hedge |>.1
  unfold
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
    matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource))
    (Q'.mul_nonneg _ _ (by decide)
      (centralPhysicalFiniteConditionalKernel_nonnegative
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        edge.1 edge.2))

private theorem scaled_mass_route_le_capacity_of_route_not_pos_local
    (floor mass route coefficientTerm capacity : Q')
    (hrouteNonnegative : (0 : Q') <= route)
    (hrouteNotPositive : ¬ (0 : Q') < route)
    (hcoefficientTermNonnegative : (0 : Q') <= coefficientTerm)
    (hcapacityNonnegative : (0 : Q') <= capacity) :
    floor * (mass * route) <= coefficientTerm * capacity := by
  have hrouteNonpositive : route <= (0 : Q') :=
    Int.not_lt.mp hrouteNotPositive
  have hrouteZero : route ≈ (0 : Q') :=
    Q'.eqv_of_le_le hrouteNonpositive hrouteNonnegative
  have hleftZero : floor * (mass * route) ≈ (0 : Q') := by
    refine Q'.eqv_trans _ (floor * (mass * 0)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left floor _ _
        (Q'.mul_eqv_congr_left mass _ _ hrouteZero)
    refine Q'.eqv_trans _ (floor * 0) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left floor _ _ (Q'.mul_zero_eqv mass)
    · exact Q'.mul_zero_eqv floor
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleftZero)
    (Q'.mul_nonneg _ _ hcoefficientTermNonnegative hcapacityNonnegative)

/-! ## 4. Sector-floor controls compile to exact row-capacity controls -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRouteSectorFloorInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        ((matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
              trajectory transitionStart physicalScale cutoffOffset +
            matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
              trajectory transitionStart physicalScale cutoffOffset) *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRouteSectorFloorInverseSquareControl.toRawCapacityControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRouteSectorFloorInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := by
    intro cutoffOffset pair hpair
    let routeMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
    let coefficientTerm := control.coefficient *
      invSqTerm offset offset_at_least_two cutoffOffset
    have hrouteNonnegative : (0 : Q') <= routeMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset pair
    have hcoefficientTermNonnegative : (0 : Q') <= coefficientTerm :=
      Q'.mul_nonneg _ _ control.coefficient_nonnegative
        (invSqTerm_nonneg offset offset_at_least_two cutoffOffset)
    by_cases hroutePositive : (0 : Q') < routeMaximum
    · have hfloorCapacity :=
        matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactorMaximum_pos
          trajectory transitionStart physicalScale cutoffOffset pair hpair
          hroutePositive
      exact Q'.le_trans' _ _ _
        (control.envelope_le cutoffOffset pair hpair)
        (Q'.mul_le_mul_of_nonneg_left _ _ coefficientTerm
          hfloorCapacity hcoefficientTermNonnegative)
    · exact scaled_mass_route_le_capacity_of_route_not_pos_local
        (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset +
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
            trajectory transitionStart physicalScale cutoffOffset)
        routeMaximum coefficientTerm
        (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair)
        hrouteNonnegative hroutePositive hcoefficientTermNonnegative
        (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitRouteSectorFloor_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRouteSectorFloorInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitRawCapacity_and_otherFaces
    oldNew.toRawCapacityControl newOld newNew cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRouteSectorFloorInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  noMerger : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
      trajectory transitionStart physicalScale cutoffOffset = true
  envelope_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRouteSectorFloorInverseSquareControl.toRawCapacityControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRouteSectorFloorInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  noMerger := control.noMerger
  envelope_le := by
    intro cutoffOffset pair hpair
    let routeMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
    let coefficientTerm := control.coefficient *
      invSqTerm offset offset_at_least_two cutoffOffset
    have hrouteNonnegative : (0 : Q') <= routeMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset pair
    have hcoefficientTermNonnegative : (0 : Q') <= coefficientTerm :=
      Q'.mul_nonneg _ _ control.coefficient_nonnegative
        (invSqTerm_nonneg offset offset_at_least_two cutoffOffset)
    by_cases hroutePositive : (0 : Q') < routeMaximum
    · have hfloorCapacity :=
        matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactorMaximum_pos
          trajectory transitionStart physicalScale cutoffOffset pair hpair
          hroutePositive
      exact Q'.le_trans' _ _ _
        (control.envelope_le cutoffOffset pair hpair)
        (Q'.mul_le_mul_of_nonneg_left _ _ coefficientTerm
          hfloorCapacity hcoefficientTermNonnegative)
    · exact scaled_mass_route_le_capacity_of_route_not_pos_local
        (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset)
        routeMaximum coefficientTerm
        (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair)
        hrouteNonnegative hroutePositive hcoefficientTermNonnegative
        (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerRouteSectorFloor_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRouteSectorFloorInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerRawCapacity_and_otherFaces
    oldNew.toRawCapacityControl newOld newNew cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactor_pos_mappedEdge_mem_sector_and_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor.matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor.matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactorMaximum_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRouteSectorFloorInverseSquareControl.toRawCapacityControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitRouteSectorFloor_and_otherFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRouteSectorFloorInverseSquareControl.toRawCapacityControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerRouteSectorFloor_and_otherFaces
