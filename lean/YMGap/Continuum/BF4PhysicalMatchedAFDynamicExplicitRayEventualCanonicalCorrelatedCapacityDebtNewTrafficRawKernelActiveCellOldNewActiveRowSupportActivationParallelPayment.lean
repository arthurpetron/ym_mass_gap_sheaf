/-
# Parallel payment for persistent and cutoff-activated used support

The exact old--new support split has two independent positive floors.  This
module gives each branch its own observable-connected amplification envelope
and proves that payments for both branches contract to the single unchanged
support-split payment.  Which branch is active at a cutoff is decided only by
the exact rational comparison of the two floors; no external case selection
or surrogate observable enters the compiler.

The result makes the local parallel width exact: two denominator/payment
proofs may be constructed independently, but only one joint precision and one
consecutive-cutoff schedule survive downstream.  It does not inhabit either
payment and does not prove an asymptotic kernel floor.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationParallelPayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArtanhMonotone
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabDyadicJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. One amplification envelope for each exact support branch -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentSupportPathAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportPathAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

/-! ## 2. Two branch payments contract to the one exact support payment -/

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPayment_of_parallelBranchPayments
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset candidate : Nat)
    (hpersistent :
      dyad candidate *
          (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentSupportPathAmplificationEnvelope
              trajectory transitionStart physicalScale cutoffOffset + 1) <=
        invSqTerm offset offset_at_least_two cutoffOffset)
    (hactivated :
      dyad candidate *
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportPathAmplificationEnvelope
              trajectory transitionStart physicalScale cutoffOffset + 1) <=
        invSqTerm offset offset_at_least_two cutoffOffset) :
    dyad candidate *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset + 1) <=
      invSqTerm offset offset_at_least_two cutoffOffset := by
  let persistentFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  let activatedFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  let splitFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  have hpersistentPos : (0 : Q') < persistentFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hactivatedPos : (0 : Q') < activatedFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hsplitPos : (0 : Q') < splitFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  by_cases hle :
      persistentFloor <= activatedFloor
  · have hpersistentSplit : persistentFloor <= splitFloor := by
      dsimp [persistentFloor, activatedFloor, splitFloor] at hle ⊢
      unfold
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
      exact (Q'.le_min'_iff _ _ _).mpr ⟨Q'.le_refl' _, hle⟩
    have hreciprocal :
        Q'.recipPos splitFloor hsplitPos <=
          Q'.recipPos persistentFloor hpersistentPos :=
      recipPos_antitone persistentFloor splitFloor hpersistentPos hsplitPos
        hpersistentSplit
    have henvelope :
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset <=
          matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentSupportPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset := by
      unfold
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
        matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentSupportPathAmplificationEnvelope
      exact Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hreciprocal
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
            trajectory transitionStart physicalScale cutoffOffset))
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale))
    have hdenominator := Q'.add_le_add_right _ _ 1 henvelope
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hdenominator
      (dyad_nonneg candidate)
    exact Q'.le_trans' _ _ _ hscaled hpersistent
  · have hactivatedPersistent : activatedFloor <= persistentFloor :=
      Q'.le_of_not_le hle
    have hactivatedSplit : activatedFloor <= splitFloor := by
      dsimp [persistentFloor, activatedFloor, splitFloor] at hactivatedPersistent ⊢
      unfold
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
      exact (Q'.le_min'_iff _ _ _).mpr
        ⟨hactivatedPersistent, Q'.le_refl' _⟩
    have hreciprocal :
        Q'.recipPos splitFloor hsplitPos <=
          Q'.recipPos activatedFloor hactivatedPos :=
      recipPos_antitone activatedFloor splitFloor hactivatedPos hsplitPos
        hactivatedSplit
    have henvelope :
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset <=
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset := by
      unfold
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportPathAmplificationEnvelope
      exact Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hreciprocal
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
            trajectory transitionStart physicalScale cutoffOffset))
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale))
    have hdenominator := Q'.add_le_add_right _ _ 1 henvelope
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hdenominator
      (dyad_nonneg candidate)
    exact Q'.le_trans' _ _ _ hscaled hactivated

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_parallelSupportBranchPayments
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset candidate : Nat)
    (hincrement :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset <=
        (1 : Q'))
    (hpersistent :
      dyad candidate *
          (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentSupportPathAmplificationEnvelope
              trajectory transitionStart physicalScale cutoffOffset + 1) <=
        invSqTerm offset offset_at_least_two cutoffOffset)
    (hactivated :
      dyad candidate *
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportPathAmplificationEnvelope
              trajectory transitionStart physicalScale cutoffOffset + 1) <=
        invSqTerm offset offset_at_least_two cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset <=
      candidate :=
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_supportSplitPayment
    trajectory transitionStart physicalScale offset offset_at_least_two
    cutoffOffset candidate hincrement
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPayment_of_parallelBranchPayments
      trajectory transitionStart physicalScale offset offset_at_least_two
      cutoffOffset candidate hpersistent hactivated)

/-! ## 3. A record exposing the exact two-lane analytic interface -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabParallelSupportBranchDyadicLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  precisionIntercept : Nat
  increment_le_one : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory transitionStart physicalScale cutoffOffset <=
      (1 : Q')
  persistentSupport_payment : forall cutoffOffset,
    dyad (precisionIntercept + cutoffOffset) *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentSupportPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset + 1) <=
      invSqTerm offset offset_at_least_two cutoffOffset
  activatedSupport_payment : forall cutoffOffset,
    dyad (precisionIntercept + cutoffOffset) *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset + 1) <=
      invSqTerm offset offset_at_least_two cutoffOffset
  start_absorbs_fixed_tail_cost :
    physicalNomeBaseCutoff (trajectory.nome physicalScale) - 1 +
        (precisionIntercept +
          physicalNomeTensorDyadicBurn
            (trajectory.nome physicalScale)
            (plaquetteEdgeCount (centralExtent 0 + 1))) <=
      transitionStart physicalScale

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabParallelSupportBranchDyadicLinearData.toSupportSplitData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (data :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabParallelSupportBranchDyadicLinearData
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSupportSplitDyadicLinearData
      trajectory transitionStart physicalScale offset offset_at_least_two where
  precisionIntercept := data.precisionIntercept
  increment_le_one := data.increment_le_one
  supportSplit_payment := by
    intro cutoffOffset
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPayment_of_parallelBranchPayments
        trajectory transitionStart physicalScale offset offset_at_least_two
        cutoffOffset (data.precisionIntercept + cutoffOffset)
        (data.persistentSupport_payment cutoffOffset)
        (data.activatedSupport_payment cutoffOffset)
  start_absorbs_fixed_tail_cost := data.start_absorbs_fixed_tail_cost

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabParallelSupportBranchDyadicLinearData.toLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (data :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabParallelSupportBranchDyadicLinearData
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData
      trajectory transitionStart physicalScale offset offset_at_least_two :=
  data.toSupportSplitData.toLinearData

/-! ## Axiom audit -/

#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPayment_of_parallelBranchPayments
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_parallelSupportBranchPayments
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabParallelSupportBranchDyadicLinearData.toSupportSplitData
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabParallelSupportBranchDyadicLinearData.toLinearData

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationParallelPayment
