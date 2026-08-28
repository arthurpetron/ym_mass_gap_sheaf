/-
# Later canonical debt dominates transported debt on new edges

For every residual endpoint pair involving a genuinely new later state, the
transported routing already selects the later canonical path.  Consequently
its transition-product summand is exactly the canonical summand.  Summing over
new endpoint pairs identifies transported new-endpoint load with the matching
sub-sum of the later canonical load.

All summands are nonnegative, so that sub-sum is bounded by the full later
canonical load.  Monotonicity of same-edge normalized debt then gives the
geometric conclusion:

  transported full debt <= later canonical debt

on every genuinely new later edge.  Combined with the preceding exact zero
old-traffic theorem, this removes transported-route churn from the new-edge
lane of the all-cutoff capacity frontier.

No canonical slack estimate, combined debt bound, regional tail, completed
gap, continuum limit, continuum Yang--Mills theory, isolated vacuum, or Clay
conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_filter_le_local {A : Type}
    (value : A -> Q') (test : A -> Bool)
    (hvalue : forall item, (0 : Q') <= value item) :
    forall xs : List A,
      listQSum value (xs.filter test) <= listQSum value xs
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_local value test hvalue tail
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            ↓reduceIte, listQSum]
          have hmono : listQSum value tail <=
              value head + listQSum value tail := by
            have hscaled := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail)
              (hvalue head)
            rwa [Q'.zero_add'] at hscaled
          exact Q'.le_trans' _ _ _ ih hmono
      | true =>
          simp only [List.filter_cons, htest, ↓reduceIte, listQSum]
          exact Q'.add_le_add_left (value head) _ _ ih

/-! ## 1. New-endpoint summands and loads are canonical -/

theorem matchedEventualCanonicalTransportedNewEndpointTerm_eq_laterCanonical
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset)
        edge.1 edge.2 endpointPair =
      centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        (matchedEventualCanonicalRoutingAt
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        edge.1 edge.2 endpointPair := by
  have hfiltered := List.mem_filter.mp hendpointPair
  have hfullPair := hfiltered.1
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hfullPair
  have hnotOld :=
    matchedEventualCanonicalNewEndpointPair_not_both_embeddedOld
      trajectory transitionStart physicalScale cutoffOffset endpointPair
      hendpointPair
  have hpath :=
    matchedEventualCanonicalTransportedRoutingAtNext_path_eq_laterCanonical_of_not_both_embeddedOld
      trajectory transitionStart physicalScale cutoffOffset
      endpointPair.1 endpointPair.2 hfull.1 hfull.2 hnotOld
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
  simp only [dif_pos hfullPair]
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
  rw [hpath]

def matchedEventualCanonicalLaterNewEndpointTrafficLoadOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      (matchedEventualCanonicalRoutingAt
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      edge.1 edge.2)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair_eqv_laterCanonicalNew
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge ≈
      matchedEventualCanonicalLaterNewEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
  unfold matchedEventualCanonicalLaterNewEndpointTrafficLoadOnPair
  apply listQSum_congr_on
  intro endpointPair hendpointPair
  exact Q'.eqv_of_eq
    (matchedEventualCanonicalTransportedNewEndpointTerm_eq_laterCanonical
      trajectory transitionStart physicalScale cutoffOffset
      edge endpointPair hendpointPair)

theorem matchedEventualCanonicalLaterNewEndpointTrafficLoadOnPair_le_full
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualCanonicalLaterNewEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
        (matchedEventualCanonicalRoutingAt
          trajectory transitionStart physicalScale (cutoffOffset + 1)) edge := by
  unfold matchedEventualCanonicalLaterNewEndpointTrafficLoadOnPair
  unfold matchedEventualCanonicalTransportedBridgeNewEndpointPairs
  unfold
    BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy.centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
  exact listQSum_filter_le_local _ _
    (fun endpointPair =>
      centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm_nonnegative
        (matchedEventualCanonicalRoutingAt
          trajectory transitionStart physicalScale (cutoffOffset + 1))
        edge.1 edge.2 endpointPair)
    _

/-! ## 2. Same-edge normalization is monotone in the load -/

theorem matchedEventualCapacityDebtFromLoadOnPair_mono
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) (lower upper : Q')
    (hload : lower <= upper) :
    matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge lower <=
      matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge upper := by
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let capacity := HalfPow.half *
    BF4PhysicalSpinCubeOffRayResidualConditionalCongestion.centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2
  unfold matchedEventualCapacityDebtFromLoadOnPair
  change (if h : (0 : Q') < capacity then
      Q'.divPos (floor * lower) capacity h else 0) <=
    (if h : (0 : Q') < capacity then
      Q'.divPos (floor * upper) capacity h else 0)
  by_cases hcapacity : (0 : Q') < capacity
  · simp only [hcapacity, dif_pos]
    unfold Q'.divPos
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left lower upper floor hload
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale)))
      (Q'.le_of_lt (Q'.recipPos_pos capacity hcapacity))
  · simp only [hcapacity]
    exact Q'.le_refl' 0

/-! ## 3. Canonical domination on genuinely new edges -/

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_le_laterCanonical
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <=
      matchedEventualCanonicalRoutedCapacityDebtOnPair
        trajectory transitionStart physicalScale (cutoffOffset + 1) edge := by
  have heq :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair_eqv_laterCanonicalNew
      trajectory transitionStart physicalScale cutoffOffset edge
  have hsubset :=
    matchedEventualCanonicalLaterNewEndpointTrafficLoadOnPair_le_full
      trajectory transitionStart physicalScale cutoffOffset edge
  have hload :
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge <=
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
          (matchedEventualCanonicalRoutingAt
            trajectory transitionStart physicalScale (cutoffOffset + 1)) edge :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hsubset
  unfold matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
  change matchedEventualCapacityDebtFromLoadOnPair
      trajectory transitionStart physicalScale (cutoffOffset + 1) edge _ <=
    matchedEventualCapacityDebtFromLoadOnPair
      trajectory transitionStart physicalScale (cutoffOffset + 1) edge _
  exact matchedEventualCapacityDebtFromLoadOnPair_mono
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    edge _ _ hload

theorem matchedEventualRoutedCapacityDebtOnPairForTransportedRouting_le_laterCanonical_of_newEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hnew : edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualRoutedCapacityDebtOnPairForRouting
        trajectory transitionStart physicalScale (cutoffOffset + 1)
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset) edge <=
      matchedEventualCanonicalRoutedCapacityDebtOnPair
        trajectory transitionStart physicalScale (cutoffOffset + 1) edge := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualRoutedCapacityDebtOnPairForTransportedRouting_eqv_newEndpointTrafficDebt_of_newEdge
        trajectory transitionStart physicalScale cutoffOffset edge hnew))
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_le_laterCanonical
      trajectory transitionStart physicalScale cutoffOffset edge)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination.matchedEventualCanonicalTransportedNewEndpointTerm_eq_laterCanonical
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair_eqv_laterCanonicalNew
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination.matchedEventualCapacityDebtFromLoadOnPair_mono
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination.matchedEventualRoutedCapacityDebtOnPairForTransportedRouting_le_laterCanonical_of_newEdge
