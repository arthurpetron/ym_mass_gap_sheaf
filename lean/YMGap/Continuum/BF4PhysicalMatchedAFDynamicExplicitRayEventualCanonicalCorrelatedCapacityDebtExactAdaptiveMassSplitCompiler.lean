/-
# Mass/amplification split for the exact adaptive sector-floor payment

The canonical sector-floor allowance is not an opaque cutoff constant.  It
factors exactly as

  later new-block mass
    * (shared floor * (2 * later carrier length) / later sector floor).

The existing moving-base mass theorem then gives two honest analytic routes:
the general corrected-slab increment plus the explicit component-merger
residual, or the corrected-slab increment alone when the executable no-merger
check succeeds.  This module packages neither route as a bound unless the
corresponding product estimate is supplied.

No uniform estimate, no all-cutoff no-merger result, no initial strict closure,
no completed gap, and no continuum or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSectorFloorPaymentCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveMassSplitCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSectorFloorPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Exact mass times amplification factorization -/

def matchedEventualActivatedDeletedSupportSectorFloorAmplification
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    ((Q'.ofNat 2 *
        Q'.ofNat
          (matchedEventualCanonicalVacuumSectorIndices
            trajectory transitionStart physicalScale (cutoffOffset + 1)).length) *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualActivatedDeletedSupportSectorFloorAmplification_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualActivatedDeletedSupportSectorFloorAmplification
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualActivatedDeletedSupportSectorFloorAmplification
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.ofNat_le_ofNat (Nat.zero_le _)))
      (Q'.le_of_lt
        (Q'.recipPos_pos _
          (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
            trajectory transitionStart physicalScale cutoffOffset))))

theorem matchedEventualActivatedDeletedSupportSectorFloorAllowance_eqv_newBlockMass_mul_amplification
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportSectorFloorAllowance
        trajectory transitionStart physicalScale cutoffOffset ≈
      matchedEventualCanonicalLaterNewBlockMass
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualActivatedDeletedSupportSectorFloorAmplification
          trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualActivatedDeletedSupportSectorFloorAllowance
    matchedEventualActivatedDeletedSupportSectorFloorPaymentNumerator
    matchedEventualActivatedDeletedSupportSectorFloorAmplification
    Q'.divPos
  q_ring

/-! ## 2. General merger and executable no-merger bounds -/

theorem matchedEventualActivatedDeletedSupportSectorFloorAllowance_le_increment_add_merger_mul_amplification
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportSectorFloorAllowance
        trajectory transitionStart physicalScale cutoffOffset <=
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
          trajectory transitionStart physicalScale cutoffOffset) *
        matchedEventualActivatedDeletedSupportSectorFloorAmplification
          trajectory transitionStart physicalScale cutoffOffset := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualActivatedDeletedSupportSectorFloorAllowance_eqv_newBlockMass_mul_amplification
        trajectory transitionStart physicalScale cutoffOffset))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalLaterNewBlockMass_le_increment_add_merger
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualActivatedDeletedSupportSectorFloorAmplification_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualActivatedDeletedSupportSectorFloorAllowance_le_increment_mul_amplification_of_noMerger
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (hcheck :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
        trajectory transitionStart physicalScale cutoffOffset = true) :
    matchedEventualActivatedDeletedSupportSectorFloorAllowance
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualActivatedDeletedSupportSectorFloorAmplification
          trajectory transitionStart physicalScale cutoffOffset := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualActivatedDeletedSupportSectorFloorAllowance_eqv_newBlockMass_mul_amplification
        trajectory transitionStart physicalScale cutoffOffset))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalLaterNewBlockMass_le_increment_of_noMerger
        trajectory transitionStart physicalScale cutoffOffset hcheck)
      (matchedEventualActivatedDeletedSupportSectorFloorAmplification_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

/-! ## 3. A common inverse-square target -/

structure MatchedEventualActivatedDeletedSupportSectorFloorAllowanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  allowance_le : forall cutoffOffset,
    matchedEventualActivatedDeletedSupportSectorFloorAllowance
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient * invSqTerm offset offset_at_least_two cutoffOffset

structure MatchedEventualActivatedDeletedSupportSectorFloorMassSplitInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset,
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
          trajectory transitionStart physicalScale cutoffOffset) *
        matchedEventualActivatedDeletedSupportSectorFloorAmplification
          trajectory transitionStart physicalScale cutoffOffset <=
      coefficient * invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualActivatedDeletedSupportSectorFloorMassSplitInverseSquareControl.toAllowanceControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (control :
      MatchedEventualActivatedDeletedSupportSectorFloorMassSplitInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportSectorFloorAllowanceInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  allowance_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualActivatedDeletedSupportSectorFloorAllowance_le_increment_add_merger_mul_amplification
        trajectory transitionStart physicalScale cutoffOffset)
      (control.envelope_le cutoffOffset)

structure MatchedEventualActivatedDeletedSupportSectorFloorNoMergerInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  noMerger : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
      trajectory transitionStart physicalScale cutoffOffset = true
  envelope_le : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualActivatedDeletedSupportSectorFloorAmplification
          trajectory transitionStart physicalScale cutoffOffset <=
      coefficient * invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualActivatedDeletedSupportSectorFloorNoMergerInverseSquareControl.toAllowanceControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (control :
      MatchedEventualActivatedDeletedSupportSectorFloorNoMergerInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportSectorFloorAllowanceInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  allowance_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualActivatedDeletedSupportSectorFloorAllowance_le_increment_mul_amplification_of_noMerger
        trajectory transitionStart physicalScale cutoffOffset
        (control.noMerger cutoffOffset))
      (control.envelope_le cutoffOffset)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveMassSplitCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveMassSplitCompiler.matchedEventualActivatedDeletedSupportSectorFloorAllowance_eqv_newBlockMass_mul_amplification
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveMassSplitCompiler.matchedEventualActivatedDeletedSupportSectorFloorAllowance_le_increment_add_merger_mul_amplification
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveMassSplitCompiler.matchedEventualActivatedDeletedSupportSectorFloorAllowance_le_increment_mul_amplification_of_noMerger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveMassSplitCompiler.MatchedEventualActivatedDeletedSupportSectorFloorMassSplitInverseSquareControl.toAllowanceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveMassSplitCompiler.MatchedEventualActivatedDeletedSupportSectorFloorNoMergerInverseSquareControl.toAllowanceControl
