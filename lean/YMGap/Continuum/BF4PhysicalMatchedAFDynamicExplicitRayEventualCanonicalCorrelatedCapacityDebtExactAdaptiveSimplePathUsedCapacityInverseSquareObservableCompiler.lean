/-
# Observable closure from the exact simple-path used-capacity product

This module connects the explicit fixed-cutoff factor

  `2 * new-block mass * shared floor * carrier length / used-edge floor`

to the existing inverse-square observable compiler.  Its producer estimate
and strict initial closure remain named fields.  The adapter only proves that
an inverse-square estimate for the sharper displayed factor supplies the
previous edge-local amplification estimate.

No producer coefficient is inhabited, and no regional tail, completed gap,
continuum theory, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationInverseSquareObservableCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityInverseSquareObservableCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveLocalAmplificationInverseSquareObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

/-! ## 1. The sharper explicit envelope dominates the local one -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope_le_simplePathUsedCapacityNewBlockEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope
  have hfactor : (0 : Q') <=
      Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset :=
    Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (matchedEventualActivatedDeletedSupportExactAdaptiveLocalRawAmplificationMaximum_le_simplePathUsedCapacityEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    hfactor

/-! ## 2. The explicit all-cutoff producer interface -/

structure MatchedEventualActivatedDeletedSupportAllCutoffSimplePathUsedCapacityInverseSquarePayment
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
  explicit_used_capacity_envelope_le : forall cutoffOffset,
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope
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

/-! ## 3. Causal adapter to the exact observable compiler -/

def MatchedEventualActivatedDeletedSupportAllCutoffSimplePathUsedCapacityInverseSquarePayment.toLocalAmplificationInverseSquarePayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffSimplePathUsedCapacityInverseSquarePayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffLocalAmplificationInverseSquarePayment
      trajectory transitionStart physicalScale where
  envelope := data.envelope
  tailAllowance := data.tailAllowance
  tailAllowance_pos := data.tailAllowance_pos
  transport := data.transport
  adaptiveCoefficient := data.adaptiveCoefficient
  adaptiveCoefficient_nonnegative := data.adaptiveCoefficient_nonnegative
  adaptive_envelope_le := by
    intro cutoffOffset
    exact Q'.le_trans' _ _ _
      (matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope_le_simplePathUsedCapacityNewBlockEnvelope
        trajectory transitionStart physicalScale cutoffOffset)
      (data.explicit_used_capacity_envelope_le cutoffOffset)
  initial_closure_with_inverse_square_margin :=
    data.initial_closure_with_inverse_square_margin

def MatchedEventualActivatedDeletedSupportAllCutoffSimplePathUsedCapacityInverseSquarePayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffSimplePathUsedCapacityInverseSquarePayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toLocalAmplificationInverseSquarePayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityInverseSquareObservableCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityInverseSquareObservableCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewBlockLocalAmplificationEnvelope_le_simplePathUsedCapacityNewBlockEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffSimplePathUsedCapacityInverseSquarePayment.toLocalAmplificationInverseSquarePayment
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffSimplePathUsedCapacityInverseSquarePayment.toObservableCertificate
