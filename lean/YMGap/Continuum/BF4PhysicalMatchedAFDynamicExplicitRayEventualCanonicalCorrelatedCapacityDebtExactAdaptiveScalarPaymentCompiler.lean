/-
# One scalar payment stream closes both live adaptive lanes

The exact canonical-slack compiler asks for edgewise adaptive-new debt
payments.  Because every later vacuum carrier is finite, those payments
contract to one located maximum.  At each cutoff the single scalar inequality

  transported data-deficit maximum + adaptive-new debt maximum <= margin

implies both the retained-old payment and the genuinely-new payment.  The two
summands remain independently estimable, so this is also the natural parallel
analytic frontier.

No scalar payment bound or initial strict closure is inhabited here.  No
regional tail, completed gap, continuum limit, continuum Yang--Mills theory,
isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

local infix:50 " ≈ " => Q'.eqv

private theorem listQMaxZero_nonnegative_any_local
    {State : Type} (value : State -> Q') :
    forall states : List State,
      (0 : Q') <= listQMaxZero value states
  | [] => Q'.le_refl' 0
  | _ :: tail =>
      Q'.le_trans' _ _ _
        (listQMaxZero_nonnegative_any_local value tail)
        (Q'.le_max'_right _ _)

/-! ## 1. The literal finite adaptive-new debt maximum -/

def matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1))

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair_le_maximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <=
      matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
  exact le_listQMaxZero_of_mem _ _ hedge

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
  exact listQMaxZero_nonnegative_any_local _ _

/-! ## 2. One scalar sum supplies both edgewise payment fields -/

structure MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment
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
    matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
          trajectory transitionStart physicalScale cutoffOffset <=
      margin

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment.toCanonicalSlackPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveCanonicalSlackPayment
      trajectory transitionStart physicalScale where
  envelope := data.envelope
  tailAllowance := data.tailAllowance
  tailAllowance_pos := data.tailAllowance_pos
  margin := data.margin
  initial_closure_with_margin := data.initial_closure_with_margin
  retained_payment_le_margin := by
    intro cutoffOffset pair hpair _hnotActivated
    have hedge := matchedEventualCanonicalCurrentPairToNext_mem
      trajectory transitionStart physicalScale cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left
        (matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset)
        _ _
        (matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair_le_maximum
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset pair)
          hedge))
      (data.payment_le_margin cutoffOffset)
  new_payment_le_margin := by
    intro cutoffOffset edge hedge _hnew
    let dataDeficit :=
      matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset
    let newMaximum :=
      matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset
    have hnewMaximum :=
      matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair_le_maximum
        trajectory transitionStart physicalScale cutoffOffset edge hedge
    have hdata : (0 : Q') <= dataDeficit :=
      matchedEventualCanonicalTransportedBridgeDataDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
    have hmaximumSum : newMaximum <= dataDeficit + newMaximum := by
      exact Q'.le_trans' _ (newMaximum + dataDeficit) _
        (Q'.add_le_self_of_nonneg newMaximum dataDeficit hdata)
        (Q'.le_of_eqv (Q'.add_comm_eqv newMaximum dataDeficit))
    exact Q'.le_trans' _ newMaximum _ hnewMaximum
      (Q'.le_trans' _ (dataDeficit + newMaximum) _
        hmaximumSum (data.payment_le_margin cutoffOffset))

def MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toCanonicalSlackPayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler.MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment.toCanonicalSlackPayment
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler.MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment.toObservableCertificate
