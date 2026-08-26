/-
# Transition-weighted congestion for exact activated-edge detours

The preceding linear-congestion compiler bounds the combinatorial route factor
of every simple new-endpoint detour by the later carrier length.  The physical
load, however, is not an unweighted path count: each occurrence carries the
actual prefix transition product and the stationary weight of the right
endpoint.

This module keeps those factors attached to the same route and selected edge.
It proves an exact factorization of each transition-product summand into

  exact prefix/endpoint weight * exact route factor,

then sums the linear route-factor bound over the literal new-endpoint list.
The result is a bound on the existing adaptive new-endpoint load itself, not a
surrogate statistic.  The remaining capacity comparison is consequently one
explicit weighted sum against the literal later conditional-kernel entry.

No cutoff-uniform capacity, all-cutoff path success, route coherence,
continuum limit, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingLinearCongestion
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingLinearCongestion
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Keep the exact transition weight attached to the selected edge -/

def matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge endpointPair : Nat × Nat) : Q' :=
  if hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) then
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
    if hedge : (edge.1, edge.2) ∈ PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        hfull.1 path (edge.1, edge.2) hedge
      centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1))
          hfull.1 prefixData.pathPrefix *
        centralPhysicalFiniteWeight
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1))
          0 endpointPair.2
    else 0
  else 0

theorem matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge endpointPair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset routing
        edge endpointPair := by
  unfold
    matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
  by_cases hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
  · rw [dif_pos hpair]
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
    by_cases hedge : (edge.1, edge.2) ∈
        PositiveKernelChainIn.directedEdges path
    · rw [dif_pos hedge]
      exact Q'.mul_nonneg _ _
        (residualPathReverseForwardProduct_nonnegative
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1))
          hfull.1
          (PositiveKernelChainIn.prefixAtDirectedEdge
            hfull.1 path (edge.1, edge.2) hedge).pathPrefix)
        (Q'.le_of_lt
          (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hfull.2))
    · rw [dif_neg hedge]
      exact Q'.le_refl' 0
  · rw [dif_neg hpair]
    exact Q'.le_refl' 0

theorem matchedEventualNewEndpointTrafficTransitionTermForRouting_eqv_prefixEndpointWeight_mul_routeFactor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge endpointPair : Nat × Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        routing edge.1 edge.2 endpointPair ≈
      matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset routing
          edge endpointPair *
        matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset routing
          edge endpointPair := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
    matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
    matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
  by_cases hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
  · rw [dif_pos hpair, dif_pos hpair, dif_pos hpair]
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
    by_cases hedge : (edge.1, edge.2) ∈
        PositiveKernelChainIn.directedEdges path
    · rw [dif_pos hedge, dif_pos hedge, if_pos hedge]
      dsimp only
      exact Q'.mul_assoc_eqv _ _ _
    · rw [dif_neg hedge, dif_neg hedge, if_neg hedge]
      exact Q'.eqv_symm (Q'.zero_mul_eqv 0)
  · rw [dif_neg hpair, dif_neg hpair, dif_neg hpair]
    exact Q'.eqv_symm (Q'.zero_mul_eqv 0)

/-! ## 2. Linearize every physically weighted new-endpoint summand -/

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_transitionTerm_le_prefixEndpointWeight_mul_carrierLength
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            data))
        edge.1 edge.2 endpointPair <=
      matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset
            (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
              data))
          edge endpointPair *
        Q'.ofNat
          (matchedEventualCanonicalVacuumSectorIndices
            trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
  let routing := matchedEventualTransportedOldAdaptiveNewRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
      data)
  let weight :=
    matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset routing
      edge endpointPair
  let route := matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
    trajectory transitionStart physicalScale cutoffOffset routing
    edge endpointPair
  have hfactor :
      centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
          routing edge.1 edge.2 endpointPair ≈ weight * route :=
    matchedEventualNewEndpointTrafficTransitionTermForRouting_eqv_prefixEndpointWeight_mul_routeFactor
      trajectory transitionStart physicalScale cutoffOffset routing
      edge endpointPair
  have hroute : route <=
      Q'.ofNat
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1)).length :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_routeFactorOnPair_le_carrierLength
      data edge endpointPair hendpointPair
  have hweight : (0 : Q') <= weight :=
    matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting_nonnegative
      trajectory transitionStart physicalScale cutoffOffset routing
      edge endpointPair
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_left _ _ weight hroute hweight)

/-! ## 3. Sum on the exact observable endpoint list -/

def matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) : Q' :=
  listQSum
    (matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset
        (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
          data))
      edge)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    (0 : Q') <=
      matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
        data edge := by
  unfold
    matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
  apply listQSum_nonnegative_on
  intro endpointPair _hendpointPair
  exact
    matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset
        (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
          data))
      edge endpointPair

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedLoad_le_prefixEndpointWeightSum_mul_carrierLength
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    matchedEventualNewEndpointTrafficLoadOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset
          (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
            data))
        edge <=
      matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
          data edge *
        Q'.ofNat
          (matchedEventualCanonicalVacuumSectorIndices
            trajectory transitionStart physicalScale (cutoffOffset + 1)).length := by
  unfold matchedEventualNewEndpointTrafficLoadOnPairForRouting
  have hsum :
      listQSum
          (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
            (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
              trajectory transitionStart physicalScale cutoffOffset
              (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
                data))
            edge.1 edge.2)
          (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
            trajectory transitionStart physicalScale cutoffOffset) <=
        listQSum
          (fun endpointPair =>
            matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
                trajectory transitionStart physicalScale cutoffOffset
                (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
                  trajectory transitionStart physicalScale cutoffOffset
                  (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
                    data))
                edge endpointPair *
              Q'.ofNat
                (matchedEventualCanonicalVacuumSectorIndices
                  trajectory transitionStart physicalScale
                  (cutoffOffset + 1)).length)
          (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
            trajectory transitionStart physicalScale cutoffOffset) := by
    apply listQSum_mono
    intro endpointPair hendpointPair
    exact
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_transitionTerm_le_prefixEndpointWeight_mul_carrierLength
        data edge endpointPair hendpointPair
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (listQSum_mul_right
        (matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset
            (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
              data))
          edge)
        (Q'.ofNat
          (matchedEventualCanonicalVacuumSectorIndices
            trajectory transitionStart physicalScale (cutoffOffset + 1)).length)
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset)))

/-! ## 4. The remaining literal weighted-capacity certificate

After the preceding linearization, the capacity frontier is no longer an
opaque assertion about the desired adaptive load.  It is the smaller
pointwise comparison between the explicit prefix/endpoint weight sum times the
later carrier length and the literal later conditional-kernel capacity.

The predicate below packages that comparison around the exact deleted-support
simple paths that define the adaptive route.  It does not assert the
comparison uniformly in the cutoff, nor construct the paths. -/

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) : Q' :=
  matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
        paths edge *
    Q'.ofNat
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1)).length

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveWeightedCapacityCertificate
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
          MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
            paths edge <=
        HalfPow.half *
          centralPhysicalFiniteConditionalKernel
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1))
            0 edge.1 edge.2

/-- The explicit weighted ceiling certificate bounds the existing adaptive
new-endpoint load against the same later conditional-kernel capacity. -/
theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedLoad_capacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveWeightedCapacityCertificate
        paths)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualNewEndpointTrafficLoadOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset
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
  have hload :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedLoad_le_prefixEndpointWeightSum_mul_carrierLength
      paths edge
  have hfloor : (0 : Q') <=
      matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale :=
    Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale)
    hload hfloor
  unfold
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveWeightedCapacityCertificate
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
    at certificate
  exact Q'.le_trans' _ _ _ hscaled
    (certificate edge hedge)

/-- The capacity comparison contracts to the existing normalized adaptive
new-endpoint debt, on the same literal later carrier edge. -/
theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedDebt_le_one
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.SimpleAdaptiveWeightedCapacityCertificate
        paths)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualNewEndpointTrafficDebtOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset
            (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
              paths))
          edge <=
      (1 : Q') := by
  unfold matchedEventualNewEndpointTrafficDebtOnPairForRouting
  unfold matchedEventualCapacityDebtFromLoadOnPair
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
      (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedLoad_capacity
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
  matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting_nonnegative
#print axioms
  matchedEventualNewEndpointTrafficTransitionTermForRouting_eqv_prefixEndpointWeight_mul_routeFactor
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveRouting_transitionTerm_le_prefixEndpointWeight_mul_carrierLength
#print axioms
  matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum_nonnegative
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedLoad_le_prefixEndpointWeightSum_mul_carrierLength
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedLoad_capacity
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedDebt_le_one

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion
