/-
# Canonical slack pays the two live exact adaptive lanes

After mapped activated edges are eliminated, exact adaptive capacity has two
live edge classes.  This module puts both into the same normalized currency as
the canonical prefix-plus-tail persistence theorem.

On a retained embedded-old edge, transported old debt is bounded by the
current canonical debt plus the exact transported data-deficit maximum.  Thus
the preserved canonical margin only has to pay

  transported data drift + adaptive new-endpoint debt.

On a genuinely new edge, transported old debt is zero, so the same margin only
has to pay adaptive new-endpoint debt.  These two payments, together with the
already-proved automatic activated lane, compile to the literal exact adaptive
capacity certificate.

No payment bound or initial strict closure is inhabited here.  No regional
tail, completed gap, continuum limit, continuum Yang--Mills theory, isolated
vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedTransportedReserveCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add_local
    {a b c d : Q'} (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem listQMaxZero_nonnegative_any_local
    {State : Type} (value : State -> Q') :
    forall states : List State,
      (0 : Q') <= listQMaxZero value states
  | [] => Q'.le_refl' 0
  | _ :: tail =>
      Q'.le_trans' _ _ _
        (listQMaxZero_nonnegative_any_local value tail)
        (Q'.le_max'_right _ _)

/-! ## 1. Exact normalized debts are linear in the shared load -/

def matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  matchedEventualCapacityDebtFromLoadOnPair
    trajectory transitionStart physicalScale (cutoffOffset + 1) edge
    (matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge)

def matchedEventualActivatedDeletedSupportExactAdaptiveFullDebtOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) : Q' :=
  matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
      trajectory transitionStart physicalScale cutoffOffset)
    edge

theorem matchedEventualCapacityDebtFromLoadOnPair_eqv_congr
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) (left right : Q')
    (hload : left ≈ right) :
    matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge left ≈
      matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge right := by
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2
  unfold matchedEventualCapacityDebtFromLoadOnPair
  change (if h : (0 : Q') < capacity then
      Q'.divPos (floor * left) capacity h else 0) ≈
    (if h : (0 : Q') < capacity then
      Q'.divPos (floor * right) capacity h else 0)
  by_cases hcapacity : (0 : Q') < capacity
  · simp only [hcapacity, dif_pos]
    unfold Q'.divPos
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left floor left right hload)
  · simp only [hcapacity]
    exact Q'.eqv_refl 0

theorem matchedEventualCapacityDebtFromLoadOnPair_additive
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) (left right : Q') :
    matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge
        (left + right) ≈
      matchedEventualCapacityDebtFromLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge left +
        matchedEventualCapacityDebtFromLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge right := by
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2
  unfold matchedEventualCapacityDebtFromLoadOnPair
  change (if h : (0 : Q') < capacity then
      Q'.divPos (floor * (left + right)) capacity h else 0) ≈
    (if h : (0 : Q') < capacity then
      Q'.divPos (floor * left) capacity h else 0) +
    (if h : (0 : Q') < capacity then
      Q'.divPos (floor * right) capacity h else 0)
  by_cases hcapacity : (0 : Q') < capacity
  · simp only [hcapacity, dif_pos]
    unfold Q'.divPos
    refine Q'.eqv_trans _
      (((floor * left) + (floor * right)) *
        Q'.recipPos capacity hcapacity) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_add_eqv floor left right)
    · exact Q'.add_mul_eqv
        (floor * left) (floor * right)
        (Q'.recipPos capacity hcapacity)
  · simp only [hcapacity]
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))

theorem matchedEventualActivatedDeletedSupportExactAdaptiveFullDebt_eqv_old_add_new
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveFullDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge ≈
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge +
        matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge := by
  let oldLoad :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let newLoad :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  have hload :=
    matchedEventualActivatedDeletedSupportExactAdaptiveFullLoad_eqv_old_add_new
      trajectory transitionStart physicalScale cutoffOffset edge
  unfold matchedEventualActivatedDeletedSupportExactAdaptiveFullDebtOnPair
  change matchedEventualCapacityDebtFromLoadOnPair
      trajectory transitionStart physicalScale (cutoffOffset + 1) edge
      (matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge) ≈ _
  unfold
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
  exact Q'.eqv_trans _
    (matchedEventualCapacityDebtFromLoadOnPair
      trajectory transitionStart physicalScale (cutoffOffset + 1) edge
      (oldLoad + newLoad)) _
    (matchedEventualCapacityDebtFromLoadOnPair_eqv_congr
      trajectory transitionStart physicalScale (cutoffOffset + 1)
      edge _ _ hload)
    (matchedEventualCapacityDebtFromLoadOnPair_additive
      trajectory transitionStart physicalScale (cutoffOffset + 1)
      edge oldLoad newLoad)

/-! ## 2. Transported old debt is current canonical debt plus data drift -/

theorem matchedEventualCanonicalTransportedBridgeDebt_le_current_add_dataDeficit
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualRoutedCapacityDebtOnPairForRouting
          trajectory transitionStart physicalScale (cutoffOffset + 1)
          (matchedEventualCanonicalTransportedRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset pair +
        matchedEventualCanonicalTransportedBridgeDataDeficitOnPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  let current := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale cutoffOffset pair
  let bridge := matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset pair)
  let deficit := matchedEventualCanonicalTransportedBridgeDataDeficitOnPair
    trajectory transitionStart physicalScale cutoffOffset pair
  have hdiff : bridge + -current <= deficit := by
    exact Q'.le_trans' _ _ _
      (Q'.le_abs_self (bridge + -current))
      (Q'.le_max'_right _ _)
  have hadd := Q'.add_le_add_left current (bridge + -current) deficit hdiff
  exact Q'.le_trans' _ (current + (bridge + -current)) _
    (Q'.le_of_eqv (Q'.add_sub_cancel_eqv bridge current))
    hadd

theorem matchedEventualCanonicalTransportedBridgeOldDebtOnMappedPair_le_current_add_dataMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) <=
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset pair +
        matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let oldLoad :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let fullLoad :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset) edge
  have holdBridge :
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge <=
        matchedEventualRoutedCapacityDebtOnPairForRouting
          trajectory transitionStart physicalScale (cutoffOffset + 1)
          (matchedEventualCanonicalTransportedRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset) edge := by
    unfold
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
    change matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale (cutoffOffset + 1)
        edge oldLoad <=
      matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale (cutoffOffset + 1)
        edge fullLoad
    exact matchedEventualCapacityDebtFromLoadOnPair_mono
      trajectory transitionStart physicalScale (cutoffOffset + 1)
      edge oldLoad fullLoad
      (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair_le_full
        trajectory transitionStart physicalScale cutoffOffset edge)
  have hbridgeCurrent :=
    matchedEventualCanonicalTransportedBridgeDebt_le_current_add_dataDeficit
      trajectory transitionStart physicalScale cutoffOffset pair
  have hdeficitMaximum :
      matchedEventualCanonicalTransportedBridgeDataDeficitOnPair
          trajectory transitionStart physicalScale cutoffOffset pair <=
        matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
    unfold matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
    exact
      BF4CanonicalFiniteMehlerGramSpectralBudget.le_listQMaxZero_of_mem
        _ _ hpair
  exact Q'.le_trans' _ _ _ holdBridge
    (Q'.le_trans' _ _ _ hbridgeCurrent
      (Q'.add_le_add_left
        (matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset pair)
        _ _ hdeficitMaximum))

/-! ## 3. A preserved canonical margin and the two exact payments -/

structure MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
    trajectory transitionStart physicalScale
  tailAllowance : Q'
  tailAllowance_pos : (0 : Q') < tailAllowance
  margin : Q'
  initial_closure_with_margin :
    (matchedEventualCanonicalRoutedCapacityDebtMaximum
          trajectory transitionStart physicalScale 0 +
        prefixTailTotalBudget
          (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation envelope)
          tailAllowance) + margin <=
      (1 : Q')
  retained_payment_le_margin : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
      matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair ∉
        matchedEventualNewEndpointTrafficOldNewFaceActivatedMappedEdges
          trajectory transitionStart physicalScale cutoffOffset ->
        matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
              trajectory transitionStart physicalScale cutoffOffset +
            matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
              trajectory transitionStart physicalScale cutoffOffset
              (matchedEventualCanonicalCurrentPairToNext
                trajectory transitionStart physicalScale cutoffOffset pair) <=
          margin
  new_payment_le_margin : forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
          trajectory transitionStart physicalScale cutoffOffset ->
        matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
            trajectory transitionStart physicalScale cutoffOffset edge <=
          margin

theorem MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment.margin_le_one
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment
        trajectory transitionStart physicalScale) :
    data.margin <= (1 : Q') := by
  let canonicalMaximum :=
    matchedEventualCanonicalRoutedCapacityDebtMaximum
      trajectory transitionStart physicalScale 0
  let totalBudget := prefixTailTotalBudget
    (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation data.envelope)
    data.tailAllowance
  have hmaximum : (0 : Q') <= canonicalMaximum := by
    unfold canonicalMaximum matchedEventualCanonicalRoutedCapacityDebtMaximum
    exact listQMaxZero_nonnegative_any_local _ _
  have hbudget : (0 : Q') <= totalBudget :=
    Q'.le_of_lt
      (prefixTailTotalBudget_pos
        (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation data.envelope)
        data.tailAllowance data.tailAllowance_pos)
  have hprefix : (0 : Q') <= canonicalMaximum + totalBudget :=
    Q'.zero_le_add _ _ hmaximum hbudget
  have hmarginAdd :
      data.margin <= (canonicalMaximum + totalBudget) + data.margin := by
    exact Q'.le_trans' _ (data.margin + (canonicalMaximum + totalBudget)) _
      (Q'.add_le_self_of_nonneg data.margin
        (canonicalMaximum + totalBudget) hprefix)
      (Q'.le_of_eqv
        (Q'.add_comm_eqv data.margin (canonicalMaximum + totalBudget)))
  exact Q'.le_trans' _ _ _ hmarginAdd data.initial_closure_with_margin

/-! ## 4. Normalized debt at most one recovers exact adaptive capacity -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveFullDebt_le_one_implies_capacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (hdebt :
      matchedEventualActivatedDeletedSupportExactAdaptiveFullDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge <=
        (1 : Q')) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge <=
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1))
          0 edge.1 edge.2 := by
  have hdebtZero :
      matchedEventualActivatedDeletedSupportExactAdaptiveFullDebtOnPair
            trajectory transitionStart physicalScale cutoffOffset edge +
          (0 : Q') <= (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))) hdebt
  have hreserve :=
    matchedEventualRoutedCapacityDebtOnPairForRouting_add_margin_le_one_implies_reserve
      trajectory transitionStart physicalScale (cutoffOffset + 1)
      (matchedEventualActivatedDeletedSupportExactAdaptiveRoutingAt
        trajectory transitionStart physicalScale cutoffOffset)
      edge hedge 0 hdebtZero
  let use := matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))
      0 edge.1 edge.2
  have hleft : use + 0 * capacity ≈ use :=
    Q'.eqv_trans _ (use + 0) _
      (Q'.add_eqv_congr_left use (0 * capacity) 0
        (Q'.zero_mul_eqv capacity))
      (Q'.eqv_of_eq (Q'.add_zero' use))
  exact Q'.le_trans' use (use + 0 * capacity) capacity
    (Q'.ge_of_eqv hleft) hreserve

/-! ## 5. Canonical slack compiles both live lanes -/

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment.toRetainedOldCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffRetainedOldEdgeExactAdaptiveCapacity
      trajectory transitionStart physicalScale := by
  intro cutoffOffset edge hedge hold hnotActivated
  rcases List.mem_map.mp hold with ⟨pair, hpair, hmap⟩
  have holdBound :=
    matchedEventualCanonicalTransportedBridgeOldDebtOnMappedPair_le_current_add_dataMaximum
      trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hpayment := data.retained_payment_le_margin
    cutoffOffset pair hpair (by simpa only [hmap] using hnotActivated)
  have hcanonical :=
    matchedEventualCanonicalRoutedCapacityDebtOnPair_add_margin_le_one
      data.envelope data.tailAllowance data.tailAllowance_pos data.margin
      data.initial_closure_with_margin cutoffOffset pair hpair
  let oldDebt :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let newDebt :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let canonicalDebt := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale cutoffOffset pair
  let dataDeficit := matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
    trajectory transitionStart physicalScale cutoffOffset
  have holdBound' : oldDebt <= canonicalDebt + dataDeficit := by
    simpa only [hmap] using holdBound
  have hpayment' : dataDeficit + newDebt <= data.margin := by
    simpa only [hmap] using hpayment
  have hsum : oldDebt + newDebt <= canonicalDebt + data.margin := by
    exact Q'.le_trans' _ ((canonicalDebt + dataDeficit) + newDebt) _
      (Q'.add_le_add_right oldDebt (canonicalDebt + dataDeficit)
        newDebt holdBound')
      (Q'.le_trans' _ (canonicalDebt + (dataDeficit + newDebt)) _
        (Q'.le_of_eqv
          (Q'.add_assoc_eqv canonicalDebt dataDeficit newDebt))
        (Q'.add_le_add_left canonicalDebt
          (dataDeficit + newDebt) data.margin hpayment'))
  have hfullDebt :
      matchedEventualActivatedDeletedSupportExactAdaptiveFullDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge <=
        (1 : Q') := by
    exact Q'.le_trans' _ (oldDebt + newDebt) _
      (Q'.le_of_eqv
        (matchedEventualActivatedDeletedSupportExactAdaptiveFullDebt_eqv_old_add_new
          trajectory transitionStart physicalScale cutoffOffset edge))
      (Q'.le_trans' _ (canonicalDebt + data.margin) _ hsum hcanonical)
  have hcapacity :=
    matchedEventualActivatedDeletedSupportExactAdaptiveFullDebt_le_one_implies_capacity
      trajectory transitionStart physicalScale cutoffOffset edge hedge hfullDebt
  have hload :=
    matchedEventualActivatedDeletedSupportExactAdaptiveFullLoad_eqv_old_add_new
      trajectory transitionStart physicalScale cutoffOffset edge
  have hscaled :
      matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
            trajectory transitionStart physicalScale cutoffOffset edge ≈
        matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          (matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
                trajectory transitionStart physicalScale cutoffOffset edge +
            matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
              trajectory transitionStart physicalScale cutoffOffset edge) :=
    Q'.mul_eqv_congr_left
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale) _ _ hload
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hscaled) hcapacity

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment.toNewEdgeCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeExactAdaptiveCapacity
      trajectory transitionStart physicalScale := by
  intro cutoffOffset edge hedge hnew
  let oldDebt :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let newDebt :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  have holdZero : oldDebt ≈ (0 : Q') :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair_eqv_zero_of_newEdge
      trajectory transitionStart physicalScale cutoffOffset edge hnew
  have hsplit :=
    matchedEventualActivatedDeletedSupportExactAdaptiveFullDebt_eqv_old_add_new
      trajectory transitionStart physicalScale cutoffOffset edge
  have hfullNew :
      matchedEventualActivatedDeletedSupportExactAdaptiveFullDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge ≈
        newDebt :=
    Q'.eqv_trans _ (oldDebt + newDebt) _ hsplit
      (Q'.eqv_trans _ (0 + newDebt) _
        (Q'.add_eqv_congr_right oldDebt 0 newDebt holdZero)
        (Q'.eqv_of_eq (Q'.zero_add' newDebt)))
  have hfullDebt :
      matchedEventualActivatedDeletedSupportExactAdaptiveFullDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge <=
        (1 : Q') :=
    Q'.le_trans' _ newDebt _
      (Q'.le_of_eqv hfullNew)
      (Q'.le_trans' _ data.margin _
        (data.new_payment_le_margin cutoffOffset edge hedge hnew)
        data.margin_le_one)
  have hcapacity :=
    matchedEventualActivatedDeletedSupportExactAdaptiveFullDebt_le_one_implies_capacity
      trajectory transitionStart physicalScale cutoffOffset edge hedge hfullDebt
  have holdLoadZero :
      matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge ≈
        (0 : Q') :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficLoadOnPair_eqv_zero_of_newEdge
      trajectory transitionStart physicalScale cutoffOffset edge hnew
  have hloadSplit :=
    matchedEventualActivatedDeletedSupportExactAdaptiveFullLoad_eqv_old_add_new
      trajectory transitionStart physicalScale cutoffOffset edge
  have hfullNewLoad :
      matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge ≈
        matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge :=
    Q'.eqv_trans _ _ _ hloadSplit
      (Q'.eqv_trans _
        (0 + matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
          trajectory transitionStart physicalScale cutoffOffset edge) _
        (Q'.add_eqv_congr_right _ 0 _ holdLoadZero)
        (Q'.eqv_of_eq (Q'.zero_add' _)))
  have hscaled :
      matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualActivatedDeletedSupportExactAdaptiveFullLoadOnPair
            trajectory transitionStart physicalScale cutoffOffset edge ≈
        matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
            trajectory transitionStart physicalScale cutoffOffset edge :=
    Q'.mul_eqv_congr_left
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale) _ _ hfullNewLoad
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hscaled) hcapacity

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  matchedEventualActivatedDeletedSupportObservableCertificateOfRetainedOldAndNew
    data.toRetainedOldCapacity data.toNewEdgeCapacity

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler.matchedEventualCapacityDebtFromLoadOnPair_additive
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveFullDebt_eqv_old_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler.matchedEventualCanonicalTransportedBridgeDebt_le_current_add_dataDeficit
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler.matchedEventualCanonicalTransportedBridgeOldDebtOnMappedPair_le_current_add_dataMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler.MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment.margin_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveFullDebt_le_one_implies_capacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler.MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment.toRetainedOldCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler.MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment.toNewEdgeCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler.MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment.toObservableCertificate
