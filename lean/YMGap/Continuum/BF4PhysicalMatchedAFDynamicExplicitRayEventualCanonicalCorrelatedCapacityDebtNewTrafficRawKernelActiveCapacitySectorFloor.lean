/-
# Sector raw-kernel floor fallback for actual active new-traffic capacity

The active used-cell capacity floor is the sharp observable-connected
denominator.  This module also supplies a coarser explicit fallback.  Strict
positivity of the route factor on an active cell forces the mapped current
edge to occur in the actual positive endpoint route.  The carried positive-
kernel chain proves that the corresponding later raw physical kernel entry is
strictly positive and that both edge endpoints lie in the later vacuum sector.

Half the existing finite vacuum-sector edge floor is therefore below every
active source-weighted capacity, and hence below the active used-cell minimum.
Reciprocal antitonicity compiles this comparison into the same exact new-debt
observable.  The sharper active floor remains available and preferred.

No cutoff-uniform edge-floor bound, new-block-mass decay, inverse-square
estimate, no-merger certificate, continuum theory, or Clay conclusion is
supplied.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
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

private theorem listPositiveMinOne_le_one_local
    {State : Type} (value : State -> Q') :
    forall states : List State,
      listPositiveMinOne value states <= 1
  | [] => Q'.le_refl' 1
  | _head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value tail)

private theorem lower_le_listPositiveMinOne_local
    {State : Type} (value : State -> Q') (lower : Q') :
    forall states : List State,
      lower <= 1 ->
      (forall state, state ∈ states -> lower <= value state) ->
      lower <= listPositiveMinOne value states
  | [], hlower, _ => hlower
  | head :: tail, hlower, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value head <= listPositiveMinOne value tail
      · rw [if_pos hle]
        exact hall head List.mem_cons_self
      · rw [if_neg hle]
        exact lower_le_listPositiveMinOne_local value lower tail hlower
          (fun state hstate =>
            hall state (List.mem_cons_of_mem head hstate))

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

/-! ## 1. An active route carries later-sector raw-kernel positivity -/

theorem matchedEventualCanonicalNewEndpointTrafficActiveCell_mappedEdge_mem_sector_and_kernel_pos
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
    let edge := matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset cell.1
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
    trajectory transitionStart physicalScale cutoffOffset cell.1
  have hactive :=
    matchedEventualCanonicalNewEndpointTrafficActiveCell_route_capacity_pos
      trajectory transitionStart physicalScale cutoffOffset cell hcell
  have hfiltered := List.mem_filter.mp hcell
  have hcartesian := (mem_cartesian_iff _ _ _).mp hfiltered.1
  have hendpointFiltered := List.mem_filter.mp hcartesian.2
  have hresidual := hendpointFiltered.1
  let hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hresidual
  let routing := matchedEventualCanonicalTransportedRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
  let path := routing.path cell.2.1 cell.2.2 hfull.1 hfull.2
  have hroute : (0 : Q') <
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
        trajectory transitionStart physicalScale cutoffOffset edge cell.2 := by
    simpa only [
      matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell,
      edge] using hactive.1
  have hedge : (edge.1, edge.2) ∈
      PositiveKernelChainIn.directedEdges path := by
    unfold
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
      at hroute
    rw [dif_pos hresidual] at hroute
    by_cases hedge : (edge.1, edge.2) ∈
        PositiveKernelChainIn.directedEdges path
    · exact hedge
    · rw [if_neg hedge] at hroute
      exact absurd hroute (by decide)
  have hsupport := PositiveKernelChainIn.directedEdges_mem_support
    hfull.1 path (edge.1, edge.2) hedge
  have hkernel := PositiveKernelChainIn.directedEdges_kernel_pos
    path (edge.1, edge.2) hedge
  exact ⟨hsupport.1, hsupport.2, hkernel⟩

/-! ## 2. The later sector raw-kernel floor bounds every active capacity -/

def matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  HalfPow.half *
    centralPhysicalFiniteVacuumSectorEdgeFloor
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0

theorem matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
  exact Q'.mul_pos (by decide)
    (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0)

theorem matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <= 1 := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
    centralPhysicalFiniteVacuumSectorEdgeFloor
  have hfloor := listPositiveMinOne_le_one_local
    (fun pair => positiveOrOne
      (centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        pair.1 pair.2))
    (centralPhysicalFiniteVacuumSectorPairs
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
    hfloor (by decide)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv HalfPow.half))
      (by decide))

theorem matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnActiveCell
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
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset cell.1
  have hdata :=
    matchedEventualCanonicalNewEndpointTrafficActiveCell_mappedEdge_mem_sector_and_kernel_pos
      trajectory transitionStart physicalScale cutoffOffset cell hcell
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
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
  exact Q'.le_trans' _ _ _ hscaled hrawLeSource

theorem matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_activeCapacityFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
  apply lower_le_listPositiveMinOne_local
  · exact
      matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_one
        trajectory transitionStart physicalScale cutoffOffset
  · intro cell hcell
    exact
      matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnActiveCell
        trajectory transitionStart physicalScale cutoffOffset cell hcell

theorem matchedEventualCanonicalNewEndpointTrafficReciprocalActiveCapacityFloor_le_reciprocalLaterSectorRawKernelCapacityFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset) <=
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset) :=
  recipPos_antitone_local
    (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_activeCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 3. Sector-floor fallback envelope and exact-debt contraction -/

def matchedEventualCanonicalNewEndpointTrafficSectorFloorPathAmplificationEnvelope
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
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope_le_sectorFloorPathEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficSectorFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope
    matchedEventualCanonicalNewEndpointTrafficSectorFloorPathAmplificationEnvelope
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficReciprocalActiveCapacityFloor_le_reciprocalLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
  · exact Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)

def matchedEventualCanonicalNewEndpointTrafficSectorFloorPathNewBlockDebtEnvelope
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
    matchedEventualCanonicalNewEndpointTrafficSectorFloorPathAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope_le_sectorFloorPathNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficSectorFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope
    matchedEventualCanonicalNewEndpointTrafficSectorFloorPathNewBlockDebtEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope_le_sectorFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_sectorFloorPathNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficSectorFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_activeCapacityFloorPathNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope_le_sectorFloorPathNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 4. Type-level inverse-square fallback interface -/

structure MatchedEventualCanonicalNewEndpointTrafficSectorFloorPathInverseSquareControl
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
    matchedEventualCanonicalNewEndpointTrafficSectorFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficSectorFloorPathInverseSquareControl.toActiveCapacityFloorControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficSectorFloorPathInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathNewBlockDebtEnvelope_le_sectorFloorPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset)
      (control.envelope_le cutoffOffset)

theorem MatchedEventualCanonicalNewEndpointTrafficSectorFloorPathInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficSectorFloorPathInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  control.toActiveCapacityFloorControl.debtMaximum_le cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor.matchedEventualCanonicalNewEndpointTrafficActiveCell_mappedEdge_mem_sector_and_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor.matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor.matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnActiveCell
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor.matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_activeCapacityFloor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor.matchedEventualCanonicalNewEndpointTrafficReciprocalActiveCapacityFloor_le_reciprocalLaterSectorRawKernelCapacityFloor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor.matchedEventualCanonicalNewEndpointTrafficActiveCapacityFloorPathAmplificationEnvelope_le_sectorFloorPathEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_sectorFloorPathNewBlockDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor.MatchedEventualCanonicalNewEndpointTrafficSectorFloorPathInverseSquareControl.toActiveCapacityFloorControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor.MatchedEventualCanonicalNewEndpointTrafficSectorFloorPathInverseSquareControl.debtMaximum_le
