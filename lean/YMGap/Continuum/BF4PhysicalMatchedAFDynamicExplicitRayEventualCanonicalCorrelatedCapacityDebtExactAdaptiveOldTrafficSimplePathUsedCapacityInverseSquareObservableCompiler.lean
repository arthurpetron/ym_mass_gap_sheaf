/-
# Sharp inverse-square closure from persistent-old drift and used-edge traffic

The exact old/new traffic partition shows that the observable capacity proof
does not need an inverse-square estimate for the full transported data stream.
It needs only:

* persistent-old data drift, and
* the explicit simple-path used-capacity envelope for adaptive-new debt.

This module combines those two estimates at one inverse-square rate and feeds
their common cutoff-zero margin to the sharp old-traffic scalar compiler.
Neither estimate nor the strict initial closure is inhabited here.  No
completed physical gap, thermodynamic/continuum limit, continuum Yang--Mills
theory, isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficScalarPaymentCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficSimplePathUsedCapacityInverseSquareObservableCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficScalarPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
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

/-! ## 1. The two irreducible inverse-square streams -/

structure MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
    trajectory transitionStart physicalScale
  tailAllowance : Q'
  tailAllowance_pos : (0 : Q') < tailAllowance
  offset : Nat
  offset_at_least_two : 2 <= offset
  oldTrafficDataCoefficient : Q'
  oldTrafficDataCoefficient_nonnegative :
    (0 : Q') <= oldTrafficDataCoefficient
  oldTrafficData_le : forall cutoffOffset,
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      oldTrafficDataCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  adaptiveCoefficient : Q'
  adaptiveCoefficient_nonnegative : (0 : Q') <= adaptiveCoefficient
  explicit_used_capacity_envelope_le : forall cutoffOffset,
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      adaptiveCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  initial_closure_with_inverse_square_margin :
    (matchedEventualCanonicalRoutedCapacityDebtMaximum
          trajectory transitionStart physicalScale 0 +
        prefixTailTotalBudget
          (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation envelope)
          tailAllowance) +
        ((oldTrafficDataCoefficient + adaptiveCoefficient) *
          invSqTerm offset offset_at_least_two 0) <=
      (1 : Q')

/-! ## 2. Exact adaptive debt and old drift contract to one margin -/

theorem MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment.exactAdaptiveDebt_le_currentTerm
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      data.adaptiveCoefficient *
        invSqTerm data.offset data.offset_at_least_two cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_simplePathUsedCapacityNewBlockEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (data.explicit_used_capacity_envelope_le cutoffOffset)

theorem MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment.total_payment_le_initial_margin
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
          trajectory transitionStart physicalScale cutoffOffset <=
      (data.oldTrafficDataCoefficient + data.adaptiveCoefficient) *
        invSqTerm data.offset data.offset_at_least_two 0 := by
  let coefficient :=
    data.oldTrafficDataCoefficient + data.adaptiveCoefficient
  let currentTerm :=
    invSqTerm data.offset data.offset_at_least_two cutoffOffset
  let initialTerm :=
    invSqTerm data.offset data.offset_at_least_two 0
  have hstreams :
      matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
            trajectory transitionStart physicalScale cutoffOffset +
          matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
            trajectory transitionStart physicalScale cutoffOffset <=
        data.oldTrafficDataCoefficient * currentTerm +
          data.adaptiveCoefficient * currentTerm :=
    add_le_add_local
      (data.oldTrafficData_le cutoffOffset)
      (data.exactAdaptiveDebt_le_currentTerm cutoffOffset)
  have hregroup :
      data.oldTrafficDataCoefficient * currentTerm +
          data.adaptiveCoefficient * currentTerm ≈
        coefficient * currentTerm :=
    Q'.eqv_symm
      (Q'.add_mul_eqv
        data.oldTrafficDataCoefficient data.adaptiveCoefficient currentTerm)
  have hcoefficient : (0 : Q') <= coefficient :=
    Q'.zero_le_add _ _
      data.oldTrafficDataCoefficient_nonnegative
      data.adaptiveCoefficient_nonnegative
  have hterm : currentTerm <= initialTerm :=
    invSqTerm_antitone data.offset data.offset_at_least_two
      (Nat.zero_le cutoffOffset)
  exact Q'.le_trans' _ _ _ hstreams
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hregroup)
      (Q'.mul_le_mul_of_nonneg_left _ _ coefficient hterm hcoefficient))

/-! ## 3. Connected exact observable compiler -/

def MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment.toOldTrafficScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveOldTrafficScalarPayment
      trajectory transitionStart physicalScale where
  envelope := data.envelope
  tailAllowance := data.tailAllowance
  tailAllowance_pos := data.tailAllowance_pos
  margin :=
    (data.oldTrafficDataCoefficient + data.adaptiveCoefficient) *
      invSqTerm data.offset data.offset_at_least_two 0
  initial_closure_with_margin :=
    data.initial_closure_with_inverse_square_margin
  payment_le_margin := data.total_payment_le_initial_margin

def MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toOldTrafficScalarPayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficSimplePathUsedCapacityInverseSquareObservableCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficSimplePathUsedCapacityInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment.exactAdaptiveDebt_le_currentTerm
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficSimplePathUsedCapacityInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment.total_payment_le_initial_margin
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficSimplePathUsedCapacityInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment.toOldTrafficScalarPayment
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveOldTrafficSimplePathUsedCapacityInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffOldTrafficSimplePathUsedCapacityInverseSquarePayment.toObservableCertificate
