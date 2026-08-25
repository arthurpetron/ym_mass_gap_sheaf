/-
# Matched support-debt variation from load and kernel components

At one matched physical scale, the nome is fixed while the cutoff recedes
through offsets beyond the selected transition start.  The exact automatic
support proxy at those offsets is

  (half * supported conditional-kernel floor) /
    (one + routed-load maximum).

This module exposes those numerator and denominator streams at the literal
matched nome and canonical routing.  Summable variation of the denominator,
summable variation of the numerator, and one positive uniform numerator floor
compile to summable variation of the already defined compact support debt.
The final transport uses its proof-bearing equality to the exact matched debt,
so no proxy, routing, carrier, kernel, load, or ray capacity is changed.

The three analytic inputs are not inhabited here.  No persistence, physical
strength band, observable pin, continuum Yang--Mills theory, or Clay
conclusion is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
import YMGap.Continuum.SummableRationalPositiveRatioDebtVariation

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.SummableRationalPositiveRatioDebtVariation
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact matched numerator and denominator streams -/

/-- The fixed-in-offset shared explicit-ray floor at one physical scale. -/
def matchedEventualCanonicalSupportSharedFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat) : Q' :=
  HalfPow.half *
    (eventualExplicitRayCapacity trajectory transitionStart scale).delta

theorem matchedEventualCanonicalSupportSharedFloor_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat) :
    (0 : Q') <
      matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart scale := by
  unfold matchedEventualCanonicalSupportSharedFloor
  exact Q'.mul_pos (by decide)
    (eventualExplicitRayCapacity_delta_pos
      trajectory transitionStart scale)

/-- Half the exact supported conditional-kernel floor on the literal matched
canonical routed support. -/
def matchedEventualCanonicalSupportedKernelNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) : Q' :=
  HalfPow.half *
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
      (matchedEventualCanonicalRoutingAt
        trajectory transitionStart scale offset)

theorem matchedEventualCanonicalSupportedKernelNumerator_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalSupportedKernelNumerator
        trajectory transitionStart scale offset := by
  unfold matchedEventualCanonicalSupportedKernelNumerator
  exact Q'.mul_pos (by decide)
    (centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_pos
      (matchedEventualCanonicalRoutingAt
        trajectory transitionStart scale offset))

/-- One plus the exact maximum routed transition-product load on the same
matched canonical finite carrier. -/
def matchedEventualCanonicalRoutedLoadDenominator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
    (matchedEventualCanonicalRoutingAt
      trajectory transitionStart scale offset)

theorem matchedEventualCanonicalRoutedLoadDenominator_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalRoutedLoadDenominator
        trajectory transitionStart scale offset :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator_pos
    (matchedEventualCanonicalRoutingAt
      trajectory transitionStart scale offset)

/-! ## 2. Exact identification with the existing support debt -/

/-- The generic positive ratio is definitionally the existing exact matched
support-margin lower proxy. -/
theorem matchedEventualCanonicalPositiveRatio_eqv_supportMarginLower
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :
    positiveRatio
        (matchedEventualCanonicalSupportedKernelNumerator
          trajectory transitionStart scale)
        (matchedEventualCanonicalRoutedLoadDenominator
          trajectory transitionStart scale)
        (matchedEventualCanonicalRoutedLoadDenominator_pos
          trajectory transitionStart scale)
        offset ≈
      matchedEventualCanonicalSupportCapacityMarginLower
        trajectory transitionStart scale offset := by
  unfold positiveRatio
    matchedEventualCanonicalSupportedKernelNumerator
    matchedEventualCanonicalRoutedLoadDenominator
    matchedEventualCanonicalSupportCapacityMarginLower
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
  exact Q'.eqv_refl _

/-- The generic ratio debt is exactly the previously defined matched debt
before its compact proof-bearing seal. -/
theorem matchedEventualCanonicalPositiveRatioDebt_eqv_exact
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :
    positiveRatioDebt
        (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart scale)
        (matchedEventualCanonicalSupportedKernelNumerator
          trajectory transitionStart scale)
        (matchedEventualCanonicalRoutedLoadDenominator
          trajectory transitionStart scale)
        (matchedEventualCanonicalSupportedKernelNumerator_pos
          trajectory transitionStart scale)
        (matchedEventualCanonicalRoutedLoadDenominator_pos
          trajectory transitionStart scale)
        offset ≈
      matchedEventualCanonicalCapacityDebt
        (matchedEventualCanonicalSupportMarginLowerProxy
          trajectory transitionStart)
        scale offset := by
  unfold positiveRatioDebt positiveRatio
    matchedEventualCanonicalSupportSharedFloor
    matchedEventualCanonicalSupportedKernelNumerator
    matchedEventualCanonicalRoutedLoadDenominator
    matchedEventualCanonicalCapacityDebt fixedNomeFiniteCapacityDebt
    matchedEventualCanonicalSupportMarginLowerProxy
    matchedEventualCanonicalSupportCapacityMarginLower
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
  exact Q'.eqv_refl _

/-- Consequently the generic ratio debt and the compact support-debt stream
are pointwise the same rational observable. -/
theorem matchedEventualCanonicalPositiveRatioDebt_eqv_compact
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :
    positiveRatioDebt
        (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart scale)
        (matchedEventualCanonicalSupportedKernelNumerator
          trajectory transitionStart scale)
        (matchedEventualCanonicalRoutedLoadDenominator
          trajectory transitionStart scale)
        (matchedEventualCanonicalSupportedKernelNumerator_pos
          trajectory transitionStart scale)
        (matchedEventualCanonicalRoutedLoadDenominator_pos
          trajectory transitionStart scale)
        offset ≈
      matchedEventualCanonicalSupportCapacityDebt
        trajectory transitionStart scale offset :=
  Q'.eqv_trans _ _ _
    (matchedEventualCanonicalPositiveRatioDebt_eqv_exact
      trajectory transitionStart scale offset)
    (Q'.eqv_symm
      (matchedEventualCanonicalSupportCapacityDebt_eqv_exact
        trajectory transitionStart scale offset))

/-! ## 3. The three-input matched contraction -/

/-- At one physical scale, the routed-load variation, supported-kernel
variation, and uniform kernel floor compile to summable variation of the
existing exact compact support debt.  These three inputs may be proved
concurrently because they refer definitionally to the same routing and
carrier. -/
def matchedEventualCanonicalSupportCapacityDebtVariationOfPrimitiveComponents
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat)
    (loadVariation : SummableRationalStepVariation
      (matchedEventualCanonicalRoutedLoadDenominator
        trajectory transitionStart scale))
    (kernelVariation : SummableRationalStepVariation
      (matchedEventualCanonicalSupportedKernelNumerator
        trajectory transitionStart scale))
    (kernelFloor : Q')
    (kernelFloor_pos : (0 : Q') < kernelFloor)
    (kernelFloor_le : forall offset,
      kernelFloor <=
        matchedEventualCanonicalSupportedKernelNumerator
          trajectory transitionStart scale offset) :
    SummableRationalStepVariation
      (matchedEventualCanonicalSupportCapacityDebt
        trajectory transitionStart scale) := by
  let ratioVariation :=
    positiveRatioDebtVariationOfPrimitiveComponents
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart scale)
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart scale)
      (matchedEventualCanonicalSupportedKernelNumerator
        trajectory transitionStart scale)
      (matchedEventualCanonicalRoutedLoadDenominator
        trajectory transitionStart scale)
      (matchedEventualCanonicalSupportedKernelNumerator_pos
        trajectory transitionStart scale)
      (matchedEventualCanonicalRoutedLoadDenominator_pos
        trajectory transitionStart scale)
      loadVariation kernelVariation
      kernelFloor kernelFloor_pos kernelFloor_le
  exact ofPointwiseEqv ratioVariation (fun offset =>
    matchedEventualCanonicalPositiveRatioDebt_eqv_compact
      trajectory transitionStart scale offset)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor.matchedEventualCanonicalSupportSharedFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor.matchedEventualCanonicalSupportedKernelNumerator_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor.matchedEventualCanonicalRoutedLoadDenominator_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor.matchedEventualCanonicalPositiveRatio_eqv_supportMarginLower
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor.matchedEventualCanonicalPositiveRatioDebt_eqv_exact
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor.matchedEventualCanonicalPositiveRatioDebt_eqv_compact
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor.matchedEventualCanonicalSupportCapacityDebtVariationOfPrimitiveComponents
