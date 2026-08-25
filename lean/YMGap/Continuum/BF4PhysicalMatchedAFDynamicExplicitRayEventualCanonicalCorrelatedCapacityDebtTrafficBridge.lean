/-
# Endpoint-traffic bridge for matched dynamic correlated capacity debt

The mapped-route bridge separates matched cutoff-data drift from route churn,
but its data leaf still contains two causally distinct effects: traffic whose
endpoints both lie in the embedded old carrier changes its physical weights,
while genuinely new endpoint pairs enter the later residual sum.

This module partitions the literal later residual endpoint list by embedded-
old membership.  The same later mapped routing, transition-product summand,
conditional kernel, shared floor, and ordered edge occur on both sides.  The
full bridge debt is therefore exactly the sum of old-endpoint and new-endpoint
traffic debt.  A triangle inequality splits data drift into old-traffic drift
and new traffic.  Together with route churn and the three shell faces, six
independent cutoff estimates contract to the existing total-deficit tail.

No inverse-square estimate, physical-scale uniformity, tail allowance,
continuum theory, or Clay conclusion is supplied.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add_local
    {a b c d : Q'} (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a + -b) <=
      Q'.abs (a + -c) + Q'.abs (c + -b) := by
  have hdecompose : a + -b ≈ (a + -c) + (c + -b) := by
    exact Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a + -c) (c + -b))

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

/-! ## 1. Exact old/new partition of later residual endpoint traffic -/

def matchedEventualCanonicalTransportedBridgeEndpointPairOldB
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (pair : Nat × Nat) : Bool :=
  decide
    (pair.1 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
        trajectory transitionStart physicalScale cutoffOffset ∧
      pair.2 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
        trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalTransportedBridgeOldEndpointPairs
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : List (Nat × Nat) :=
  (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))).filter
    (matchedEventualCanonicalTransportedBridgeEndpointPairOldB
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : List (Nat × Nat) :=
  (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))).filter
    (fun pair =>
      !(matchedEventualCanonicalTransportedBridgeEndpointPairOldB
        trajectory transitionStart physicalScale cutoffOffset pair))

def matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      edge.1 edge.2)
    (matchedEventualCanonicalTransportedBridgeOldEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      edge.1 edge.2)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeRoutedLoadOnPair_eqv_old_add_new
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset) edge ≈
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge +
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
  change listQSum
      (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset)
        edge.1 edge.2)
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))) ≈ _
  exact listQSum_filter_partition
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      edge.1 edge.2)
    (matchedEventualCanonicalTransportedBridgeEndpointPairOldB
      trajectory transitionStart physicalScale cutoffOffset)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)))

/-! ## 2. Exact old/new debts under the same matched capacity -/

def matchedEventualCapacityDebtFromLoadOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) (load : Q') : Q' :=
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2
  if hcapacity : (0 : Q') < capacity then
    Q'.divPos
      (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale * load)
      capacity hcapacity
  else 0

theorem matchedEventualRoutedCapacityDebtOnPairForRouting_eqv_fromLoad
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset))
    (edge : Nat × Nat) :
    matchedEventualRoutedCapacityDebtOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset routing edge ≈
      matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge
        (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
          routing edge) := by
  exact Q'.eqv_refl _

def matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) : Q' :=
  matchedEventualCapacityDebtFromLoadOnPair
    trajectory transitionStart physicalScale (cutoffOffset + 1) edge
    (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge)

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) : Q' :=
  matchedEventualCapacityDebtFromLoadOnPair
    trajectory transitionStart physicalScale (cutoffOffset + 1) edge
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge)

theorem matchedEventualCanonicalTransportedBridgeCapacityDebtOnPair_eqv_old_add_new
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) :
    matchedEventualRoutedCapacityDebtOnPairForRouting
        trajectory transitionStart physicalScale (cutoffOffset + 1)
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset) edge ≈
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge +
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge := by
  let oldLoad :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let newLoad :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))
      0 edge.1 edge.2
  have hload :
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
          (matchedEventualCanonicalTransportedRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset) edge ≈
        oldLoad + newLoad :=
    matchedEventualCanonicalTransportedBridgeRoutedLoadOnPair_eqv_old_add_new
      trajectory transitionStart physicalScale cutoffOffset edge
  change matchedEventualCapacityDebtFromLoadOnPair
      trajectory transitionStart physicalScale (cutoffOffset + 1) edge
      (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset) edge) ≈ _
  unfold
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
  unfold matchedEventualCapacityDebtFromLoadOnPair
  change (if h : (0 : Q') < capacity then
      Q'.divPos
        (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
            (matchedEventualCanonicalTransportedRoutingAtNext
              trajectory transitionStart physicalScale cutoffOffset) edge)
        capacity h
    else 0) ≈
    (if h : (0 : Q') < capacity then
      Q'.divPos
        (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * oldLoad)
        capacity h
    else 0) +
    (if h : (0 : Q') < capacity then
      Q'.divPos
        (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * newLoad)
        capacity h
    else 0)
  by_cases hcapacity : (0 : Q') < capacity
  · simp only [hcapacity, dif_pos]
    unfold Q'.divPos
    refine Q'.eqv_trans _
      ((matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale * (oldLoad + newLoad)) *
        Q'.recipPos capacity hcapacity) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left
          (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale) _ _ hload)
    refine Q'.eqv_trans _
      (((matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * oldLoad) +
          (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * newLoad)) *
        Q'.recipPos capacity hcapacity) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_add_eqv
          (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale) oldLoad newLoad)
    exact Q'.add_mul_eqv
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale * oldLoad)
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale * newLoad)
      (Q'.recipPos capacity hcapacity)
  · simp only [hcapacity]
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))

/-! ## 3. Data drift splits into old traffic and new traffic -/

def matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (pair : Nat × Nat) : Q' :=
  let current := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale cutoffOffset pair
  let laterOld :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair)
  Q'.max' (Q'.abs (current + -laterOld))
    (Q'.abs (laterOld + -current))

def matchedEventualCanonicalTransportedBridgeNewTrafficDeficitOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (pair : Nat × Nat) : Q' :=
  let mappedPair := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let laterOld :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset mappedPair
  let laterFull := matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset) mappedPair
  Q'.max' (Q'.abs (laterOld + -laterFull))
    (Q'.abs (laterFull + -laterOld))

def matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitOnPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalTransportedBridgeNewTrafficDeficitOnPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _) (Q'.le_max'_left _ _)

theorem matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualCanonicalTransportedBridgeNewTrafficDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _) (Q'.le_max'_left _ _)

theorem matchedEventualCanonicalTransportedBridgeDataDeficitOnPair_le_traffic_split
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (pair : Nat × Nat) :
    matchedEventualCanonicalTransportedBridgeDataDeficitOnPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitOnPair
          trajectory transitionStart physicalScale cutoffOffset pair +
        matchedEventualCanonicalTransportedBridgeNewTrafficDeficitOnPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  let current := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale cutoffOffset pair
  let mappedPair := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let laterOld :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset mappedPair
  let laterFull := matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset) mappedPair
  change Q'.max'
      (Q'.abs (current + -laterFull))
      (Q'.abs (laterFull + -current)) <=
    Q'.max'
        (Q'.abs (current + -laterOld))
        (Q'.abs (laterOld + -current)) +
      Q'.max'
        (Q'.abs (laterOld + -laterFull))
        (Q'.abs (laterFull + -laterOld))
  apply (Q'.max'_le_iff' _ _ _).mpr
  constructor
  · exact Q'.le_trans' _ _ _
      (abs_sub_triangle_local current laterFull laterOld)
      (add_le_add_local
        (Q'.le_max'_left _ _) (Q'.le_max'_left _ _))
  · have htriangle := abs_sub_triangle_local laterFull current laterOld
    have hmaxima :
        Q'.abs (laterFull + -laterOld) +
            Q'.abs (laterOld + -current) <=
          Q'.max'
              (Q'.abs (laterOld + -laterFull))
              (Q'.abs (laterFull + -laterOld)) +
            Q'.max'
              (Q'.abs (current + -laterOld))
              (Q'.abs (laterOld + -current)) :=
      add_le_add_local
        (Q'.le_max'_right _ _) (Q'.le_max'_right _ _)
    exact Q'.le_trans' _ _ _ htriangle
      (Q'.le_trans' _ _ _ hmaxima
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem matchedEventualCanonicalTransportedBridgeDataDeficitMaximum_le_traffic_split
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact Q'.zero_le_add _ _
      (matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
  · intro pair hpair
    exact Q'.le_trans' _ _ _
      (matchedEventualCanonicalTransportedBridgeDataDeficitOnPair_le_traffic_split
        trajectory transitionStart physicalScale cutoffOffset pair)
      (add_le_add_local
        (le_listQMaxZero_of_mem
          (matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitOnPair
            trajectory transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalVacuumSectorPairs
            trajectory transitionStart physicalScale cutoffOffset) hpair)
        (le_listQMaxZero_of_mem
          (matchedEventualCanonicalTransportedBridgeNewTrafficDeficitOnPair
            trajectory transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalVacuumSectorPairs
            trajectory transitionStart physicalScale cutoffOffset) hpair))

/-! ## 4. Six cutoff leaves rejoin the one total tail -/

structure MatchedEventualCanonicalTransportedCapacityDebtTrafficInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  oldTrafficDataCoefficient : Q'
  newTrafficCoefficient : Q'
  routeCoefficient : Q'
  oldTrafficDataCoefficient_nonnegative :
    (0 : Q') <= oldTrafficDataCoefficient
  newTrafficCoefficient_nonnegative : (0 : Q') <= newTrafficCoefficient
  routeCoefficient_nonnegative : (0 : Q') <= routeCoefficient
  oldTrafficData_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      oldTrafficDataCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  newTraffic_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newTrafficCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  route_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      routeCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalTransportedCapacityDebtTrafficInverseSquareControl.toBridgeControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalTransportedCapacityDebtTrafficInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  dataCoefficient :=
    control.oldTrafficDataCoefficient + control.newTrafficCoefficient
  routeCoefficient := control.routeCoefficient
  dataCoefficient_nonnegative :=
    Q'.zero_le_add _ _
      control.oldTrafficDataCoefficient_nonnegative
      control.newTrafficCoefficient_nonnegative
  routeCoefficient_nonnegative := control.routeCoefficient_nonnegative
  data_le := fun cutoffOffset => by
    let term := invSqTerm
      control.offset control.offset_at_least_two cutoffOffset
    exact Q'.le_trans' _ _ _
      (matchedEventualCanonicalTransportedBridgeDataDeficitMaximum_le_traffic_split
        trajectory transitionStart physicalScale cutoffOffset)
      (Q'.le_trans' _ _ _
        (add_le_add_local
          (control.oldTrafficData_le cutoffOffset)
          (control.newTraffic_le cutoffOffset))
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.add_mul_eqv
              control.oldTrafficDataCoefficient
              control.newTrafficCoefficient term))))
  route_le := control.route_le

structure MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  transport :
    MatchedEventualCanonicalTransportedCapacityDebtTrafficInverseSquareControl
      trajectory transitionStart physicalScale
  oldNewCoefficient : Q'
  newOldCoefficient : Q'
  newNewCoefficient : Q'
  oldNewCoefficient_nonnegative : (0 : Q') <= oldNewCoefficient
  newOldCoefficient_nonnegative : (0 : Q') <= newOldCoefficient
  newNewCoefficient_nonnegative : (0 : Q') <= newNewCoefficient
  oldNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      oldNewCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset
  newOld_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newOldCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset
  newNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newNewCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset

def MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toBridgeRegionalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl
      trajectory transitionStart physicalScale where
  transport := control.transport.toBridgeControl
  oldNewCoefficient := control.oldNewCoefficient
  newOldCoefficient := control.newOldCoefficient
  newNewCoefficient := control.newNewCoefficient
  oldNewCoefficient_nonnegative := control.oldNewCoefficient_nonnegative
  newOldCoefficient_nonnegative := control.newOldCoefficient_nonnegative
  newNewCoefficient_nonnegative := control.newNewCoefficient_nonnegative
  oldNew_le := control.oldNew_le
  newOld_le := control.newOld_le
  newNew_le := control.newNew_le

def MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toTotalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtInverseSquareControl
      trajectory transitionStart physicalScale :=
  control.toBridgeRegionalControl.toTotalControl

def MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toTotalDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale :=
  control.toTotalControl.toTotalDeficitTail

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge.matchedEventualCanonicalTransportedBridgeRoutedLoadOnPair_eqv_old_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge.matchedEventualCanonicalTransportedBridgeCapacityDebtOnPair_eqv_old_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge.matchedEventualCanonicalTransportedBridgeDataDeficitOnPair_le_traffic_split
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge.matchedEventualCanonicalTransportedBridgeDataDeficitMaximum_le_traffic_split
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge.MatchedEventualCanonicalTransportedCapacityDebtTrafficInverseSquareControl.toBridgeControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge.MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toBridgeRegionalControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge.MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toTotalControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge.MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toTotalDeficitTail
