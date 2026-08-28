/-
# Inverse-square observable closure for edge-local adaptive amplification

The exact adaptive local-amplification envelope is the product of genuinely
new stationary mass and an edge-aware route-factor/raw-capacity maximum.  This
module combines an explicit inverse-square bound on that product with the
parallel transported-data inverse-square bound and contracts both streams to
one cutoff-independent observable margin.

The producer estimate and the strict initial closure remain named fields.  No
regional tail, completed gap, continuum theory, or Clay conclusion is
asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveInverseSquareObservableCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationInverseSquareObservableCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add_local
    {a b c d : Q'} (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

/-! ## 1. Two explicit inverse-square producer streams -/

structure MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
    trajectory transitionStart physicalScale
  tailAllowance : Q'
  tailAllowance_pos : (0 : Q') < tailAllowance
  transport :
    MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl
      trajectory transitionStart physicalScale
  adaptiveCoefficient : Q'
  adaptiveCoefficient_nonnegative : (0 : Q') <= adaptiveCoefficient
  adaptive_envelope_le : forall cutoffOffset,
    matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      adaptiveCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset
  initial_closure_with_inverse_square_margin :
    (matchedEventualCanonicalRoutedCapacityDebtMaximum
          trajectory transitionStart physicalScale 0 +
        prefixTailTotalBudget
          (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation envelope)
          tailAllowance) +
        ((transport.dataCoefficient + adaptiveCoefficient) *
          invSqTerm transport.offset
            transport.offset_at_least_two 0) <=
      (1 : Q')

/-! ## 2. Exact adaptive debt and transported drift share one margin -/

theorem MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment.exactAdaptiveDebt_le_currentTerm
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      data.adaptiveCoefficient *
        invSqTerm data.transport.offset
          data.transport.offset_at_least_two cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_newBlockLocalAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (data.adaptive_envelope_le cutoffOffset)

theorem MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment.total_payment_le_initial_margin
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
          trajectory transitionStart physicalScale cutoffOffset <=
      (data.transport.dataCoefficient + data.adaptiveCoefficient) *
        invSqTerm data.transport.offset
          data.transport.offset_at_least_two 0 := by
  let coefficient :=
    data.transport.dataCoefficient + data.adaptiveCoefficient
  let currentTerm :=
    invSqTerm data.transport.offset
      data.transport.offset_at_least_two cutoffOffset
  let initialTerm :=
    invSqTerm data.transport.offset
      data.transport.offset_at_least_two 0
  have hstreams :
      matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
            trajectory transitionStart physicalScale cutoffOffset +
          matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
            trajectory transitionStart physicalScale cutoffOffset <=
        data.transport.dataCoefficient * currentTerm +
          data.adaptiveCoefficient * currentTerm :=
    add_le_add_local
      (data.transport.data_le cutoffOffset)
      (data.exactAdaptiveDebt_le_currentTerm cutoffOffset)
  have hregroup :
      data.transport.dataCoefficient * currentTerm +
          data.adaptiveCoefficient * currentTerm ≈
        coefficient * currentTerm :=
    Q'.eqv_symm
      (Q'.add_mul_eqv
        data.transport.dataCoefficient data.adaptiveCoefficient currentTerm)
  have hcoefficient : (0 : Q') <= coefficient :=
    Q'.zero_le_add _ _
      data.transport.dataCoefficient_nonnegative
      data.adaptiveCoefficient_nonnegative
  have hterm : currentTerm <= initialTerm :=
    invSqTerm_antitone data.transport.offset
      data.transport.offset_at_least_two (Nat.zero_le cutoffOffset)
  exact Q'.le_trans' _ _ _ hstreams
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hregroup)
      (Q'.mul_le_mul_of_nonneg_left _ _ coefficient hterm hcoefficient))

/-! ## 3. Connected exact observable compiler -/

def MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment.toExactAdaptiveScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment
      trajectory transitionStart physicalScale where
  envelope := data.envelope
  tailAllowance := data.tailAllowance
  tailAllowance_pos := data.tailAllowance_pos
  margin :=
    (data.transport.dataCoefficient + data.adaptiveCoefficient) *
      invSqTerm data.transport.offset
        data.transport.offset_at_least_two 0
  initial_closure_with_margin :=
    data.initial_closure_with_inverse_square_margin
  payment_le_margin := data.total_payment_le_initial_margin

def MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toExactAdaptiveScalarPayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationInverseSquareObservableCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment.exactAdaptiveDebt_le_currentTerm
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment.total_payment_le_initial_margin
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment.toObservableCertificate
