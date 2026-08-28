/-
# Exact normalized debt of the constructed new-route ceiling

The normalized transported-reserve compiler still carried a free edge margin.
This module removes that degree of freedom.  It normalizes the literal
constructed new-route ceiling by the same later half-kernel capacity used by
the transported debt.

The only delicate case is a zero denominator.  Every prefix weight is then
zero: membership of the selected edge in any positive route would force the
same conditional-kernel entry to be positive.  Thus normalized ceiling debt
times capacity always recovers the literal ceiling use, including on unloaded
edges.

Consequently the entire all-cutoff reserve frontier contracts to one exact,
observable-connected inequality on every later carrier edge:

  transported debt + constructed-ceiling debt <= 1.

No such combined normalized-debt estimate is inhabited here.  No regional
tail, completed gap, continuum limit, continuum Yang--Mills theory, isolated
vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_eqv_zero_of_pointwise_local
    {State : Type} (value : State -> Q') :
    forall states : List State,
      (forall state, state ∈ states -> value state ≈ (0 : Q')) ->
      listQSum value states ≈ (0 : Q')
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hall => by
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (hall head List.mem_cons_self)
          (listQSum_eqv_zero_of_pointwise_local value tail
            (fun state hstate =>
              hall state (List.mem_cons_of_mem head hstate)))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem mul_eqv_zero_of_left_eqv_zero_local
    (left right : Q') (hleft : left ≈ (0 : Q')) :
    left * right ≈ (0 : Q') :=
  Q'.eqv_trans _ (0 * right) _
    (Q'.mul_eqv_congr_right left 0 right hleft)
    (Q'.zero_mul_eqv right)

private theorem mul_eqv_zero_of_right_eqv_zero_local
    (left right : Q') (hright : right ≈ (0 : Q')) :
    left * right ≈ (0 : Q') :=
  Q'.eqv_trans _ (left * 0) _
    (Q'.mul_eqv_congr_left left right 0 hright)
    (Q'.mul_zero_eqv left)

/-! ## 1. Zero conditional capacity forces every ceiling weight to vanish -/

theorem matchedEventualNewEndpointTrafficPrefixEndpointWeight_eqv_zero_of_conditionalKernel_not_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge endpointPair : Nat × Nat)
    (hkernel : ¬ (0 : Q') <
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        0 edge.1 edge.2) :
    matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset routing
        edge endpointPair ≈ (0 : Q') := by
  unfold matchedEventualNewEndpointTrafficPrefixEndpointWeightOnPairForRouting
  by_cases hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
  · rw [dif_pos hpair]
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
    have hedgeNot : (edge.1, edge.2) ∉
        PositiveKernelChainIn.directedEdges path := by
      intro hedge
      have hraw : (0 : Q') <
          centralPhysicalFiniteKernel
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1))
            0 edge.1 edge.2 :=
        PositiveKernelChainIn.directedEdges_kernel_pos
          path (edge.1, edge.2) hedge
      have hedgeSupport :=
        PositiveKernelChainIn.directedEdges_mem_support
          hfull.1 path (edge.1, edge.2) hedge
      exact hkernel
        (centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
          hedgeSupport.1 hraw)
    rw [dif_neg hedgeNot]
    exact Q'.eqv_refl 0
  · rw [dif_neg hpair]
    exact Q'.eqv_refl 0

theorem matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum_eqv_zero_of_conditionalKernel_not_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat)
    (hkernel : ¬ (0 : Q') <
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        0 edge.1 edge.2) :
    matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
        paths edge ≈ (0 : Q') := by
  unfold matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
  apply listQSum_eqv_zero_of_pointwise_local
  intro endpointPair _hendpointPair
  exact
    matchedEventualNewEndpointTrafficPrefixEndpointWeight_eqv_zero_of_conditionalKernel_not_pos
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset
        (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleNewRouting
          paths))
      edge endpointPair hkernel

theorem matchedEventualNewEndpointTrafficSimpleAdaptiveWeightedCeiling_eqv_zero_of_conditionalKernel_not_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat)
    (hkernel : ¬ (0 : Q') <
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        0 edge.1 edge.2) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
        paths edge ≈
      (0 : Q') := by
  have hsum :=
    matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum_eqv_zero_of_conditionalKernel_not_pos
      paths edge hkernel
  unfold
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
  exact mul_eqv_zero_of_left_eqv_zero_local
    (matchedEventualNewEndpointTrafficSimpleAdaptivePrefixEndpointWeightSum
      paths edge)
    (Q'.ofNat
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1)).length)
    hsum

theorem matchedEventualActivatedDeletedSupportNewCeilingCapacityUse_eqv_zero_of_conditionalKernel_not_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat)
    (hkernel : ¬ (0 : Q') <
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        0 edge.1 edge.2) :
    matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
        trajectory transitionStart physicalScale cutoffOffset paths edge ≈
      (0 : Q') := by
  have hceiling :=
    matchedEventualNewEndpointTrafficSimpleAdaptiveWeightedCeiling_eqv_zero_of_conditionalKernel_not_pos
      paths edge hkernel
  unfold matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
  exact mul_eqv_zero_of_right_eqv_zero_local
    (matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale)
    (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
      paths edge)
    hceiling

/-! ## 2. Exact normalized ceiling debt -/

def matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) : Q' :=
  let capacity :=
    matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  if hcapacity : (0 : Q') < capacity then
    Q'.divPos
      (matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
        trajectory transitionStart physicalScale cutoffOffset paths edge)
      capacity hcapacity
  else
    0

theorem matchedEventualActivatedDeletedSupportNewCeilingDebt_mul_capacity_eqv_use
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset paths edge *
        matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
          trajectory transitionStart physicalScale cutoffOffset edge ≈
      matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
        trajectory transitionStart physicalScale cutoffOffset paths edge := by
  let capacity :=
    matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let use := matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
    trajectory transitionStart physicalScale cutoffOffset paths edge
  by_cases hcapacity : (0 : Q') < capacity
  · unfold matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
    change (if h : (0 : Q') < capacity then
      Q'.divPos use capacity h else 0) * capacity ≈ use
    rw [dif_pos hcapacity]
    exact Q'.divPos_mul_eqv use capacity hcapacity
  · have hkernel : ¬ (0 : Q') <
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1))
          0 edge.1 edge.2 := by
      intro hkernel
      exact hcapacity (Q'.mul_pos (by decide) hkernel)
    have huse : use ≈ (0 : Q') :=
      matchedEventualActivatedDeletedSupportNewCeilingCapacityUse_eqv_zero_of_conditionalKernel_not_pos
        paths edge hkernel
    unfold matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
    change (if h : (0 : Q') < capacity then
      Q'.divPos use capacity h else 0) * capacity ≈ use
    rw [dif_neg hcapacity]
    exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv capacity) (Q'.eqv_symm huse)

/-! ## 3. The sole combined normalized-debt frontier -/

def MatchedEventualActivatedDeletedSupportAllCutoffCombinedNormalizedDebt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      matchedEventualRoutedCapacityDebtOnPairForRouting
            trajectory transitionStart physicalScale (cutoffOffset + 1)
            (matchedEventualCanonicalTransportedRoutingAtNext
              trajectory transitionStart physicalScale cutoffOffset) edge +
          matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
            trajectory transitionStart physicalScale cutoffOffset
            (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
              trajectory transitionStart physicalScale cutoffOffset)
            edge <= (1 : Q')

def MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve.ofCombinedNormalizedDebt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (combined :
      MatchedEventualActivatedDeletedSupportAllCutoffCombinedNormalizedDebt
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve
      trajectory transitionStart physicalScale where
  margin := fun cutoffOffset edge =>
    matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
      edge
  transported_debt_add_margin_le_one := combined
  new_ceiling_le_margin_capacity := by
    intro cutoffOffset edge _hedge
    exact Q'.ge_of_eqv
      (matchedEventualActivatedDeletedSupportNewCeilingDebt_mul_capacity_eqv_use
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
          trajectory transitionStart physicalScale cutoffOffset)
        edge)

def MatchedEventualActivatedDeletedSupportAllCutoffCombinedNormalizedDebt.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (combined :
      MatchedEventualActivatedDeletedSupportAllCutoffCombinedNormalizedDebt
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  (MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve.ofCombinedNormalizedDebt
    combined).toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler.matchedEventualNewEndpointTrafficPrefixEndpointWeight_eqv_zero_of_conditionalKernel_not_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler.matchedEventualActivatedDeletedSupportNewCeilingDebt_mul_capacity_eqv_use
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler.MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve.ofCombinedNormalizedDebt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler.MatchedEventualActivatedDeletedSupportAllCutoffCombinedNormalizedDebt.toObservableCertificate
