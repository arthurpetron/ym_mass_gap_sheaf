/-
# Inverse-square closure of the exact adaptive observable lane

The exact adaptive proof has two parallel scalar streams at each cutoff:
transported data drift and the canonical sector-floor allowance.  If both are
bounded by inverse-square terms with one common offset, their coefficient sum
times the cutoff-zero inverse-square term is a constant margin for every
cutoff.  This module performs that contraction and feeds it to the exact
observable compiler.

The initial strict closure with that explicit margin remains a named field.
No inverse-square estimate is manufactured here.  No regional tail, completed
gap, continuum theory, isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveMassSplitCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveInverseSquareObservableCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveMassSplitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSectorFloorPaymentCompiler
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

/-! ## 1. Two parallel inverse-square streams -/

structure MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment
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
  adaptive_le : forall cutoffOffset,
    matchedEventualActivatedDeletedSupportSectorFloorAllowance
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

/-! ## 2. Antitonicity contracts every cutoff to one margin -/

theorem MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment.total_payment_le_initial_margin
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualActivatedDeletedSupportSectorFloorAllowance
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
          matchedEventualActivatedDeletedSupportSectorFloorAllowance
            trajectory transitionStart physicalScale cutoffOffset <=
        data.transport.dataCoefficient * currentTerm +
          data.adaptiveCoefficient * currentTerm :=
    add_le_add_local
      (data.transport.data_le cutoffOffset)
      (data.adaptive_le cutoffOffset)
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

/-! ## 3. The connected observable compiler -/

def MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment.toSectorFloorScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorScalarPayment
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
  total_payment_le_margin := data.total_payment_le_initial_margin

def MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toSectorFloorScalarPayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveInverseSquareObservableCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment.total_payment_le_initial_margin
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment.toSectorFloorScalarPayment
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveInverseSquareObservableCompiler.MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorInverseSquarePayment.toObservableCertificate
