/-
# Source-weight cancellation for the exact adaptive ceiling

Pathwise detailed balance telescopes every reverse/forward prefix product to
the stationary weight ratio between the endpoint-pair source and the selected
edge source.  Multiplying by the selected source weight therefore recovers
the literal stationary endpoint-pair product.  Summing on the exact new-pair
list bounds the source-weighted adaptive prefix sum by the actual new-endpoint
stationary mass.

This preserves the small new-block mass factor; it does not replace it by a
unit bound.  No lower raw-kernel bound, cutoff-uniform payment, completed gap,
continuum limit, continuum Yang--Mills theory, isolated vacuum, or Clay
conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSourceMassCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem zero_le_mul_of_positive_local
    (left right : Q') (hleft : (0 : Q') < left)
    (hright : (0 : Q') < right) :
    (0 : Q') <= left * right :=
  Q'.le_of_lt (Q'.mul_pos hleft hright)

private theorem listQSum_mono_local {A : Type}
    (lower upper : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> lower item <= upper item) ->
      listQSum lower items <= listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Pointwise source-weight cancellation -/

theorem matchedEventualNewEndpointTrafficSourceWeight_mul_prefixEndpointWeight_le_stationaryPairWeight
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset edge.1 *
        matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset routing
          edge endpointPair <=
      matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair.1 *
        matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset endpointPair.2 := by
  have hbase := List.mem_filter.mp hendpointPair |>.1
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hbase
  let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
  unfold matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
  rw [dif_pos hbase]
  by_cases hedge : (edge.1, edge.2) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [dif_pos hedge]
    let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
      hfull.1 path (edge.1, edge.2) hedge
    have hratio :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        hfull.1 prefixData.pathPrefix
    unfold
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
      at hratio
    rw [dif_pos prefixData.source_mem] at hratio
    let sourceWeight := centralPhysicalFiniteWeight
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0 edge.1
    let leftWeight := centralPhysicalFiniteWeight
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0 endpointPair.1
    let rightWeight := centralPhysicalFiniteWeight
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0 endpointPair.2
    let product :=
      centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        hfull.1 prefixData.pathPrefix
    have hsource : (0 : Q') < sourceWeight :=
      centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        prefixData.source_mem
    have hproduct : product ≈ Q'.divPos leftWeight sourceWeight hsource :=
      Q'.eqv_symm hratio
    have hcancel : sourceWeight * product ≈ leftWeight := by
      refine Q'.eqv_trans _ (product * sourceWeight) _ ?_ ?_
      · exact Q'.mul_comm_eqv sourceWeight product
      refine Q'.eqv_trans _
        (Q'.divPos leftWeight sourceWeight hsource * sourceWeight) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ sourceWeight hproduct
      · exact Q'.divPos_mul_eqv leftWeight sourceWeight hsource
    unfold matchedEventualCanonicalLaterIndexWeight
    change sourceWeight * (product * rightWeight) <=
      leftWeight * rightWeight
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ ((sourceWeight * product) * rightWeight) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv sourceWeight product rightWeight))
        (Q'.mul_eqv_congr_right _ _ rightWeight hcancel))
  · rw [dif_neg hedge]
    have hleft := centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      hfull.1
    have hright := centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      hfull.2
    exact Q'.le_trans' _ 0 _
      (Q'.le_of_eqv
        (Q'.mul_zero_eqv
          (matchedEventualCanonicalLaterIndexWeight
            trajectory transitionStart physicalScale cutoffOffset edge.1)))
      (by
        unfold matchedEventualCanonicalLaterIndexWeight
        exact zero_le_mul_of_positive_local _ _ hleft hright)

/-! ## 2. Sum only the actual new-endpoint stationary mass -/

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.sourceWeight_mul_prefixEndpointWeightSum_le_newEndpointMass
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset edge.1 *
        matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
          paths edge <=
      matchedEventualCanonicalNewEndpointStationaryMass
        trajectory transitionStart physicalScale cutoffOffset := by
  let sourceWeight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset edge.1
  let routing := matchedEventualTransportedOldAdaptiveNewRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
      paths)
  let items := matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset
  let prefixWeight :=
    matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset routing edge
  let stationaryPair := fun endpointPair : Nat × Nat =>
    matchedEventualCanonicalLaterIndexWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair.1 *
      matchedEventualCanonicalLaterIndexWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair.2
  have hsum : listQSum (fun endpointPair =>
        sourceWeight * prefixWeight endpointPair) items <=
      listQSum stationaryPair items := by
    apply listQSum_mono_local
    intro endpointPair hendpointPair
    exact
      matchedEventualNewEndpointTrafficSourceWeight_mul_prefixEndpointWeight_le_stationaryPairWeight
        trajectory transitionStart physicalScale cutoffOffset routing edge
        endpointPair hendpointPair
  have hfactor := listQSum_mul_left sourceWeight prefixWeight items
  unfold matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
    matchedEventualCanonicalNewEndpointStationaryMass
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hfactor)) hsum

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.sourceWeight_mul_weightedCeiling_le_newEndpointMass_mul_carrierLength
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset edge.1 *
        MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
          paths edge <=
      matchedEventualCanonicalNewEndpointStationaryMass
          trajectory transitionStart physicalScale cutoffOffset *
        Q'.ofNat
          (matchedEventualCanonicalVacuumSectorIndices
            trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
  let sourceWeight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset edge.1
  let prefixSum :=
    matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
      paths edge
  let carrierLength := Q'.ofNat
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1)).length
  have hprefix :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.sourceWeight_mul_prefixEndpointWeightSum_le_newEndpointMass
      paths edge
  have hcarrier : (0 : Q') <= carrierLength :=
    Q'.ofNat_le_ofNat (Nat.zero_le _)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ carrierLength
    hprefix hcarrier
  unfold
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
  change sourceWeight * (prefixSum * carrierLength) <=
    matchedEventualCanonicalNewEndpointStationaryMass
        trajectory transitionStart physicalScale cutoffOffset * carrierLength
  exact Q'.le_trans' _ ((sourceWeight * prefixSum) * carrierLength) _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv sourceWeight prefixSum carrierLength)))
    hscaled

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.sourceWeight_mul_weightedCeiling_le_two_newBlockMass_mul_carrierLength
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    matchedEventualCanonicalLaterIndexWeight
          trajectory transitionStart physicalScale cutoffOffset edge.1 *
        MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
          paths edge <=
      (Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
          trajectory transitionStart physicalScale cutoffOffset) *
        Q'.ofNat
          (matchedEventualCanonicalVacuumSectorIndices
            trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
  let carrierLength := Q'.ofNat
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale (cutoffOffset + 1)).length
  have hmass := matchedEventualCanonicalNewEndpointStationaryMass_le_two_newMass
    trajectory transitionStart physicalScale cutoffOffset
  have hcarrier : (0 : Q') <= carrierLength :=
    Q'.ofNat_le_ofNat (Nat.zero_le _)
  exact Q'.le_trans' _
    (matchedEventualCanonicalNewEndpointStationaryMass
        trajectory transitionStart physicalScale cutoffOffset * carrierLength) _
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.sourceWeight_mul_weightedCeiling_le_newEndpointMass_mul_carrierLength
      paths edge)
    (Q'.mul_le_mul_of_nonneg_right _ _ carrierLength hmass hcarrier)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSourceMassCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSourceMassCompiler.matchedEventualNewEndpointTrafficSourceWeight_mul_prefixEndpointWeight_le_stationaryPairWeight
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSourceMassCompiler.MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.sourceWeight_mul_prefixEndpointWeightSum_le_newEndpointMass
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSourceMassCompiler.MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.sourceWeight_mul_weightedCeiling_le_two_newBlockMass_mul_carrierLength
