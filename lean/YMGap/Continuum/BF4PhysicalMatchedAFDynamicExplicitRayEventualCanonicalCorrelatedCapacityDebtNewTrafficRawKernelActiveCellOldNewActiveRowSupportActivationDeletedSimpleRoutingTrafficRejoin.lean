/-
# Rejoin adaptive new traffic with persistent canonical old traffic

The adaptive compiler changes routes only for endpoint pairs involving a new
state.  A full off-ray routed load nevertheless sums over both persistent-old
and new endpoint pairs.  This module partitions that literal endpoint list for
an arbitrary routing, proves that the old part of the simple adaptive hybrid
is exactly the existing canonical transported-old load, and contracts the
full adaptive load to

  canonical persistent-old load + adaptive new-endpoint load.

Consequently an explicit certificate comparing the canonical old load plus
the already proved weighted new ceiling with the same later kernel capacity
controls the full adaptive debt.  On a mapped activated edge, birth avoidance
makes the new term exactly zero and the full load contracts to persistent old
traffic alone.

No such combined capacity certificate is inhabited here.  No all-cutoff
reachability, route coherence, regional tail, continuum limit, or Clay
conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingTrafficRejoin

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact old/new traffic partition for any later routing -/

def matchedEventualOldEndpointTrafficLoadOnPairForRouting
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge : Nat × Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      routing edge.1 edge.2)
    (matchedEventualCanonicalTransportedBridgeOldEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualRoutedConditionalTransitionProductLoadOnPair_eqv_old_add_new_forRouting
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge : Nat × Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
        routing edge ≈
      matchedEventualOldEndpointTrafficLoadOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset routing edge +
        matchedEventualNewEndpointTrafficLoadOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset routing edge := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
    matchedEventualOldEndpointTrafficLoadOnPairForRouting
    matchedEventualNewEndpointTrafficLoadOnPairForRouting
  exact listQSum_filter_partition
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      routing edge.1 edge.2)
    (matchedEventualCanonicalTransportedBridgeEndpointPairOldB
      trajectory transitionStart physicalScale cutoffOffset)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)))

/-! ## 2. The hybrid keeps the exact canonical old traffic -/

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptive_transitionTerm_eq_canonical_of_old
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeOldEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            paths))
        edge.1 edge.2 endpointPair =
      centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset)
        edge.1 edge.2 endpointPair := by
  have hfiltered := List.mem_filter.mp hendpointPair
  have hold :
      endpointPair.1 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset ∧
        endpointPair.2 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset := by
    exact of_decide_eq_true hfiltered.2
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
      hfiltered.1
  have hpath :=
    matchedEventualTransportedOldAdaptiveNewRoutingAtNext_path_eq_transported_of_old
      trajectory transitionStart physicalScale cutoffOffset
      (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
        paths)
      endpointPair.1 endpointPair.2 hfull.1 hfull.2 hold.1 hold.2
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
  rw [dif_pos hfiltered.1, dif_pos hfiltered.1]
  dsimp only
  rw [hpath]
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
  rw [hpath]

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveOldEndpointTrafficLoad_eqv_canonical
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    matchedEventualOldEndpointTrafficLoadOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            paths))
        edge ≈
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold matchedEventualOldEndpointTrafficLoadOnPairForRouting
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
  apply listQSum_congr_on
  intro endpointPair hendpointPair
  exact Q'.eqv_of_eq
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptive_transitionTerm_eq_canonical_of_old
      paths edge endpointPair hendpointPair)

/-! ## 3. Rejoin the full adaptive load to persistent old plus new -/

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRoutedLoad_eqv_canonicalOld_add_new
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
        (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            paths))
        edge ≈
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge +
        matchedEventualNewEndpointTrafficLoadOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset
            (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
              paths))
          edge := by
  exact Q'.eqv_trans _ _ _
    (matchedEventualRoutedConditionalTransitionProductLoadOnPair_eqv_old_add_new_forRouting
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset
        (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
          paths))
      edge)
    (Q'.add_eqv_congr'
      (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveOldEndpointTrafficLoad_eqv_canonical
        paths edge)
      (Q'.eqv_refl _))

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRoutedLoadOnMappedActivated_eqv_canonicalOld
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
        (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            paths))
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) ≈
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  have hrejoin :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRoutedLoad_eqv_canonicalOld_add_new
      paths edge
  have hzero :=
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.toSimpleBirthAvoidingRoutingAt
      paths).load_eqv_zero pair hpair
  exact Q'.eqv_trans _ _ _ hrejoin
    (Q'.eqv_trans _
      (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge + 0) _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hzero)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

/-! ## 4. The combined literal full-capacity certificate -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveOldPlusWeightedCeilingCapacityCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset) : Prop :=
  forall edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
                trajectory transitionStart physicalScale cutoffOffset edge +
            MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
              paths edge) <=
        HalfPow.half *
          centralPhysicalFiniteConditionalKernel
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1))
            0 edge.1 edge.2

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveFullWeightedLoad_capacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveOldPlusWeightedCeilingCapacityCertificate
        paths)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
          (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset
            (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
              paths))
          edge <=
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1))
          0 edge.1 edge.2 := by
  have hrejoin :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRoutedLoad_eqv_canonicalOld_add_new
      paths edge
  have hnew :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedLoad_le_prefixEndpointWeightSum_mul_carrierLength
      paths edge
  have hsum := Q'.add_le_add_left
    (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge)
    _ _ hnew
  have hfull := Q'.le_trans' _ _ _ (Q'.le_of_eqv hrejoin) hsum
  have hfloor : (0 : Q') <=
      matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale :=
    Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale)
    hfull hfloor
  unfold
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveOldPlusWeightedCeilingCapacityCertificate
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
    at certificate
  exact Q'.le_trans' _ _ _ hscaled (certificate edge hedge)

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveFullWeightedDebt_le_one
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveOldPlusWeightedCeilingCapacityCertificate
        paths)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualRoutedCapacityDebtOnPairForRouting
          trajectory transitionStart physicalScale (cutoffOffset + 1)
          (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset
            (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
              paths))
          edge <=
      (1 : Q') := by
  unfold matchedEventualRoutedCapacityDebtOnPairForRouting
  dsimp only
  by_cases hcapacity : (0 : Q') < HalfPow.half *
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        0 edge.1 edge.2
  · rw [dif_pos hcapacity]
    apply Q'.divPos_le_of_le_mul _ _ hcapacity
    exact Q'.le_trans' _ _ _
      (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveFullWeightedLoad_capacity
        paths certificate edge hedge)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.one_mul_eqv
            (HalfPow.half *
              centralPhysicalFiniteConditionalKernel
                (trajectory.nome physicalScale)
                (Q'.le_of_lt (trajectory.nome_pos physicalScale))
                (transitionStart physicalScale + (cutoffOffset + 1))
                0 edge.1 edge.2))))
  · rw [dif_neg hcapacity]
    decide

/-! ## Axiom audit -/

#print axioms
  matchedEventualRoutedConditionalTransitionProductLoadOnPair_eqv_old_add_new_forRouting
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptive_transitionTerm_eq_canonical_of_old
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveOldEndpointTrafficLoad_eqv_canonical
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRoutedLoad_eqv_canonicalOld_add_new
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRoutedLoadOnMappedActivated_eqv_canonicalOld
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveFullWeightedLoad_capacity
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveFullWeightedDebt_le_one

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingTrafficRejoin
