/-
# Persistent-old data drift and adaptive-new debt share one exact margin

The preceding canonical-slack compiler bounded transported old traffic by the
current canonical debt plus a deficit comparing the current debt with the
entire later transported debt.  That later debt also contains newly born
endpoint traffic, although the adaptive-new lane pays new traffic separately.

This module removes that overcount.  The exact old/new traffic partition
already defines the symmetric deficit between the current canonical debt and
the later persistent-old debt alone.  The elementary inequality

  laterOld <= current + |laterOld - current|

puts transported old debt below current canonical debt plus precisely that
persistent-old data deficit.  A scalar payment of

  persistent-old data-deficit maximum + adaptive-new debt maximum

then constructs the exact all-cutoff observable capacity certificate.

No bound on either scalar stream or strict initial closure is inhabited here.
No completed physical gap, thermodynamic/continuum limit, continuum
Yang--Mills theory, isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficScalarPaymentCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveActivatedEdgeZeroCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

local infix:50 " ≈ " => Q'.eqv

private theorem listQMaxZero_nonnegative_any_local
    {State : Type} (value : State -> Q') :
    forall states : List State,
      (0 : Q') <=
        BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero value states
  | [] => Q'.le_refl' 0
  | _ :: tail =>
      Q'.le_trans' _ _ _
        (listQMaxZero_nonnegative_any_local value tail)
        (Q'.le_max'_right _ _)

/-! ## 1. Transported old debt needs only persistent-old data drift -/

theorem matchedEventualCanonicalTransportedBridgeOldDebt_le_current_add_oldTrafficDataDeficit
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset pair +
        matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitOnPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  let current := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale cutoffOffset pair
  let laterOld :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair)
  let deficit :=
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitOnPair
      trajectory transitionStart physicalScale cutoffOffset pair
  have hdiff : laterOld + -current <= deficit := by
    exact Q'.le_trans' _ _ _
      (Q'.le_abs_self (laterOld + -current))
      (Q'.le_max'_right _ _)
  have hadd := Q'.add_le_add_left current (laterOld + -current) deficit hdiff
  exact Q'.le_trans' _ (current + (laterOld + -current)) _
    (Q'.le_of_eqv (Q'.add_sub_cancel_eqv laterOld current)) hadd

theorem matchedEventualCanonicalTransportedBridgeOldDebtOnMappedPair_le_current_add_oldTrafficDataMaximum
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
        matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeOldDebt_le_current_add_oldTrafficDataDeficit
      trajectory transitionStart physicalScale cutoffOffset pair)
    (Q'.add_le_add_left
      (matchedEventualCanonicalRoutedCapacityDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      _ _
      (le_listQMaxZero_of_mem
        (matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitOnPair
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalVacuumSectorPairs
          trajectory transitionStart physicalScale cutoffOffset) hpair))

/-! ## 2. One sharper scalar payment constructs both live edge lanes -/

structure MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment
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
  payment_le_margin : forall cutoffOffset,
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
          trajectory transitionStart physicalScale cutoffOffset <=
      margin

theorem MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment.margin_le_one
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment
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

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment.toRetainedOldCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffRetainedOldEdgeExactAdaptiveCapacity
      trajectory transitionStart physicalScale := by
  intro cutoffOffset edge hedge hold _hnotActivated
  rcases List.mem_map.mp hold with ⟨pair, hpair, hmap⟩
  have holdBound :=
    matchedEventualCanonicalTransportedBridgeOldDebtOnMappedPair_le_current_add_oldTrafficDataMaximum
      trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hedgeMaximum :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair_le_maximum
      trajectory transitionStart physicalScale cutoffOffset edge hedge
  have hpayment := data.payment_le_margin cutoffOffset
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
  let oldDataDeficit :=
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
      trajectory transitionStart physicalScale cutoffOffset
  have holdBound' : oldDebt <= canonicalDebt + oldDataDeficit := by
    simpa only [hmap] using holdBound
  have hpayment' : oldDataDeficit + newDebt <= data.margin :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left oldDataDeficit newDebt _ hedgeMaximum)
      hpayment
  have hsum : oldDebt + newDebt <= canonicalDebt + data.margin := by
    exact Q'.le_trans' _ ((canonicalDebt + oldDataDeficit) + newDebt) _
      (Q'.add_le_add_right oldDebt (canonicalDebt + oldDataDeficit)
        newDebt holdBound')
      (Q'.le_trans' _ (canonicalDebt + (oldDataDeficit + newDebt)) _
        (Q'.le_of_eqv
          (Q'.add_assoc_eqv canonicalDebt oldDataDeficit newDebt))
        (Q'.add_le_add_left canonicalDebt
          (oldDataDeficit + newDebt) data.margin hpayment'))
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

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment.toNewEdgeCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment
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
  let newMaximum :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
      trajectory transitionStart physicalScale cutoffOffset
  let oldDataDeficit :=
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
      trajectory transitionStart physicalScale cutoffOffset
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
  have hnewMaximum : newDebt <= newMaximum :=
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair_le_maximum
      trajectory transitionStart physicalScale cutoffOffset edge hedge
  have holdDataNonnegative : (0 : Q') <= oldDataDeficit :=
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  have hmaximumSum : newMaximum <= oldDataDeficit + newMaximum := by
    exact Q'.le_trans' _ (newMaximum + oldDataDeficit) _
      (Q'.add_le_self_of_nonneg newMaximum oldDataDeficit holdDataNonnegative)
      (Q'.le_of_eqv (Q'.add_comm_eqv newMaximum oldDataDeficit))
  have hnewMargin : newDebt <= data.margin :=
    Q'.le_trans' _ newMaximum _ hnewMaximum
      (Q'.le_trans' _ (oldDataDeficit + newMaximum) _
        hmaximumSum (data.payment_le_margin cutoffOffset))
  have hfullDebt :
      matchedEventualActivatedDeletedSupportExactAdaptiveFullDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset edge <=
        (1 : Q') :=
    Q'.le_trans' _ newDebt _
      (Q'.le_of_eqv hfullNew)
      (Q'.le_trans' _ data.margin _ hnewMargin data.margin_le_one)
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

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  matchedEventualActivatedDeletedSupportObservableCertificateOfRetainedOldAndNew
    data.toRetainedOldCapacity data.toNewEdgeCapacity

/-! ## Axiom audit -/

#print axioms
  matchedEventualCanonicalTransportedBridgeOldDebt_le_current_add_oldTrafficDataDeficit
#print axioms
  matchedEventualCanonicalTransportedBridgeOldDebtOnMappedPair_le_current_add_oldTrafficDataMaximum
#print axioms
  MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment.margin_le_one
#print axioms
  MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment.toRetainedOldCapacity
#print axioms
  MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment.toNewEdgeCapacity
#print axioms
  MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficScalarPaymentCompiler
