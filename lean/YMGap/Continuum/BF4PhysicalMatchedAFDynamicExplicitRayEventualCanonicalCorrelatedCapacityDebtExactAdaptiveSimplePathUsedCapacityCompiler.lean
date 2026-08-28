/-
# Simple-path and used-capacity factorization for exact adaptive traffic

The exact activated/deleted routing is the observable loop-erased routing.
Consequently, every one of its route factors is bounded by the literal later
carrier length.  This module combines that sharp numerator estimate with a
finite minimum taken only over later edges whose exact route-factor maximum is
strictly positive.

The resulting denominator is not the minimum over unrelated positive entries
of the whole sector: inactive edges are removed before the minimum is formed.
It is nevertheless only a fixed-cutoff constructive quantity.  No cutoff-
uniform lower bound on the used-edge capacity floor, inverse-square estimate,
completed gap, continuum theory, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingLinearCongestion

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingLinearCongestion
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQMaxZero_le_bound_local {A : Type}
    (value : A -> Q') (bound : Q') : forall items : List A,
      (0 : Q') <= bound ->
      (forall item, item ∈ items -> value item <= bound) ->
      listQMaxZero value items <= bound
  | [], hbound, _ => hbound
  | head :: tail, hboundNonnegative, hbound => by
      unfold listQMaxZero Q'.max'
      by_cases hle : value head <= listQMaxZero value tail
      · rw [if_pos hle]
        exact listQMaxZero_le_bound_local value bound tail hboundNonnegative
          (fun item hitem => hbound item (List.mem_cons_of_mem head hitem))
      · rw [if_neg hle]
        exact hbound head List.mem_cons_self

private theorem exists_pos_of_listQMaxZero_pos_local {A : Type}
    (value : A -> Q') : forall items : List A,
      (0 : Q') < listQMaxZero value items ->
      Exists fun item => item ∈ items ∧ (0 : Q') < value item
  | [], hpositive => by
      unfold listQMaxZero at hpositive
      exact absurd hpositive (by decide)
  | head :: tail, hpositive => by
      unfold listQMaxZero Q'.max' at hpositive
      by_cases hle : value head <= listQMaxZero value tail
      · rw [if_pos hle] at hpositive
        obtain ⟨item, hitem, hitemPositive⟩ :=
          exists_pos_of_listQMaxZero_pos_local value tail hpositive
        exact ⟨item, List.mem_cons_of_mem head hitem, hitemPositive⟩
      · rw [if_neg hle] at hpositive
        exact ⟨head, List.mem_cons_self, hpositive⟩

private theorem divPos_le_divPos_of_num_le_of_den_le_local
    {numerator upper denominator floor : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hfloor : (0 : Q') < floor)
    (hnumerator : numerator <= upper)
    (hfloorLe : floor <= denominator)
    (hupper : (0 : Q') <= upper) :
    Q'.divPos numerator denominator hdenominator <=
      Q'.divPos upper floor hfloor := by
  let quotient := Q'.divPos upper floor hfloor
  have hquotient : (0 : Q') <= quotient := by
    dsimp only [quotient]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _ hupper
      (Q'.le_of_lt (Q'.recipPos_pos floor hfloor))
  have hscaled : quotient * floor <= quotient * denominator :=
    Q'.mul_le_mul_of_nonneg_left _ _ quotient hfloorLe hquotient
  have hupperScaled : upper <= quotient * denominator :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.divPos_mul_eqv upper floor hfloor))
      hscaled
  exact Q'.divPos_le_of_le_mul numerator denominator hdenominator
    (Q'.le_trans' _ _ _ hnumerator hupperScaled)

/-! ## 1. The exact route-factor maximum is linear in carrier length -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge_le_carrierLength
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge <=
      Q'.ofNat
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
  apply listQMaxZero_le_bound_local
  · exact Q'.ofNat_le_ofNat (Nat.zero_le _)
  intro endpointPair hendpointPair
  simpa only [matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt] using
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_routeFactorOnPair_le_carrierLength
      (matchedEventualActivatedDeletedSupportObservablePathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
      edge endpointPair hendpointPair)

/-! ## 2. Positive exact traffic locates a positive raw capacity -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveRawKernelCapacityOnEdge_pos_of_routeFactorMaximum_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hmaximum : (0 : Q') <
      matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge) :
    (0 : Q') <
      matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
    at hmaximum
  obtain ⟨endpointPair, hendpointPair, hroute⟩ :=
    exists_pos_of_listQMaxZero_pos_local
      (matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
          trajectory transitionStart physicalScale cutoffOffset)
        edge)
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)
      hmaximum
  have hresidual := (List.mem_filter.mp hendpointPair).1
  let hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hresidual
  let routing := matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
    trajectory transitionStart physicalScale cutoffOffset
  let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
  have hedgePath : (edge.1, edge.2) ∈
      PositiveKernelChainIn.directedEdges path := by
    unfold matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting at hroute
    rw [dif_pos hresidual] at hroute
    by_cases hedgePath : (edge.1, edge.2) ∈
        PositiveKernelChainIn.directedEdges path
    · exact hedgePath
    · rw [if_neg hedgePath] at hroute
      exact absurd hroute (by decide)
  have hsupport := PositiveKernelChainIn.directedEdges_mem_support
    hfull.1 path (edge.1, edge.2) hedgePath
  have hkernel := PositiveKernelChainIn.directedEdges_kernel_pos
    path (edge.1, edge.2) hedgePath
  unfold matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
  exact Q'.mul_pos (by decide) hkernel

/-! ## 3. Minimum over exactly the used later edges -/

def matchedEventualActivatedDeletedSupportExactAdaptivePositiveRouteEdges
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    List (Nat × Nat) :=
  (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)).filter
    (fun edge => (0 : Q') <
      matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge)

def matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listPositiveMinOne
    (matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualActivatedDeletedSupportExactAdaptivePositiveRouteEdges
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor
  apply listPositiveMinOne_pos
  intro edge hedge
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptivePositiveRouteEdges
    at hedge
  have hmaximum := of_decide_eq_true (List.mem_filter.mp hedge).2
  exact
    matchedEventualActivatedDeletedSupportExactAdaptiveRawKernelCapacityOnEdge_pos_of_routeFactorMaximum_pos
      trajectory transitionStart physicalScale cutoffOffset edge hmaximum

theorem matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor_le_rawCapacity_of_routeFactorMaximum_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (hmaximum : (0 : Q') <
      matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge) :
    matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor
  apply listPositiveMinOne_le_of_mem
  unfold matchedEventualActivatedDeletedSupportExactAdaptivePositiveRouteEdges
  exact List.mem_filter.mpr ⟨hedge, decide_eq_true hmaximum⟩

/-! ## 4. Exact local amplification through the used-edge floor -/

def matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  Q'.divPos
    (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
      Q'.ofNat
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1)).length)
    (matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope
    Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale))
      (Q'.ofNat_le_ofNat (Nat.zero_le _)))
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset)))

theorem matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge_le_simplePathUsedCapacityEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge <=
      matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  let sharedFloor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let routeMaximum :=
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  let rawCapacity :=
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  let carrierLength := Q'.ofNat
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1)).length
  let usedFloor :=
    matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  have hshared : (0 : Q') <= sharedFloor :=
    Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)
  have hrouteNonnegative : (0 : Q') <= routeMaximum :=
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge_nonnegative
      trajectory transitionStart physicalScale cutoffOffset edge
  have hrouteLength : routeMaximum <= carrierLength :=
    matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge_le_carrierLength
      trajectory transitionStart physicalScale cutoffOffset edge
  have husedFloor : (0 : Q') < usedFloor :=
    matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hupper : (0 : Q') <= sharedFloor * carrierLength :=
    Q'.mul_nonneg _ _ hshared (Q'.ofNat_le_ofNat (Nat.zero_le _))
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope
  by_cases hraw : (0 : Q') < rawCapacity
  · rw [dif_pos hraw]
    by_cases hroute : (0 : Q') < routeMaximum
    · have husedFloorLe : usedFloor <= rawCapacity :=
        matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor_le_rawCapacity_of_routeFactorMaximum_pos
          trajectory transitionStart physicalScale cutoffOffset edge hedge hroute
      exact divPos_le_divPos_of_num_le_of_den_le_local
        hraw husedFloor
        (Q'.mul_le_mul_of_nonneg_left _ _ sharedFloor hrouteLength hshared)
        husedFloorLe hupper
    · have hrouteNonpositive : routeMaximum <= 0 := Int.not_lt.mp hroute
      have hnumerator : sharedFloor * routeMaximum <= 0 :=
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ sharedFloor
            hrouteNonpositive hshared)
          (Q'.le_of_eqv (Q'.mul_zero_eqv sharedFloor))
      have hreciprocal : (0 : Q') <= Q'.recipPos rawCapacity hraw :=
        Q'.le_of_lt (Q'.recipPos_pos rawCapacity hraw)
      have hquotient :
          (sharedFloor * routeMaximum) * Q'.recipPos rawCapacity hraw <= 0 :=
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _
            (Q'.recipPos rawCapacity hraw) hnumerator hreciprocal)
          (Q'.le_of_eqv (Q'.zero_mul_eqv _))
      exact Q'.le_trans' _ _ _ hquotient
        (matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope_nonnegative
          trajectory transitionStart physicalScale cutoffOffset)
  · rw [dif_neg hraw]
    exact
      matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope_nonnegative
        trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum_le_simplePathUsedCapacityEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum
  apply listQMaxZero_le_bound_local
  · exact
      matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
  intro edge hedge
  exact
    matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationOnEdge_le_simplePathUsedCapacityEnvelope
      trajectory transitionStart physicalScale cutoffOffset edge hedge

/-! ## 5. The exact debt reaches the explicit used-capacity product -/

def matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  (Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
      trajectory transitionStart physicalScale cutoffOffset) *
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_simplePathUsedCapacityNewBlockEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  have hdebt :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_newBlockLocalAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset
  have hfactor : (0 : Q') <=
      Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset :=
    Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
  have hamp := Q'.mul_le_mul_of_nonneg_left _ _ _
    (matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum_le_simplePathUsedCapacityEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    hfactor
  exact Q'.le_trans' _ _ _ hdebt hamp

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveRouteFactorMaximumOnEdge_le_carrierLength
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveRawKernelCapacityOnEdge_pos_of_routeFactorMaximum_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveUsedEdgeRawCapacityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum_le_simplePathUsedCapacityEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_simplePathUsedCapacityNewBlockEnvelope
