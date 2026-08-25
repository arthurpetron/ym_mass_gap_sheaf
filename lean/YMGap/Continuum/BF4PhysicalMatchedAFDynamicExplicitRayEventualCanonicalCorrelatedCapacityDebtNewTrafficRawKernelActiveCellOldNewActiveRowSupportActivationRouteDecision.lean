/-
# Constructive route decision at the activated-support frontier

The old--new canonical route either avoids every cutoff-activated used row or
it supplies a literal activated row witness.  This module makes that finite
decision executable at each cutoff.

If the activated list is empty, its positive-minimum fallback is exactly one.
The persistent floor is always at most one, so the support-split denominator
contracts to the persistent branch and a persistent payment alone feeds the
unchanged joint precision.  Uniform emptiness therefore gives a checked
canonical persistent-only schedule.

If the list is nonempty, the returned row is active, has no positive current
kernel entry, and has a positive mapped later raw-kernel capacity.  That is the
precise observable-connected activation witness for which an activated-floor
estimate or a local adaptive rerouting is required.

No global avoidance theorem, activated-floor estimate, or adaptive route is
inhabited here.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationParallelPayment

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationRouteDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArtanhMonotone
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowRawKernelFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationParallelPayment
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

private theorem listPositiveMinOne_le_one_local
    {A : Type} (value : A -> Q') : forall items : List A,
      listPositiveMinOne value items <= 1
  | [] => Q'.le_refl' 1
  | _head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value tail)

/-! ## 1. An executable avoided-or-used decision -/

inductive MatchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportUseDecision
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type where
  | avoided
      (activatedPairs_eq_nil :
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
          trajectory transitionStart physicalScale cutoffOffset = [])
  | used
      (pair : Nat × Nat)
      (pair_mem : pair ∈
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
          trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportUseDecision
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportUseDecision
      trajectory transitionStart physicalScale cutoffOffset := by
  let items :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset
  match hitems : items with
  | [] =>
      exact .avoided (by simpa only [items] using hitems)
  | head :: tail =>
      exact .used head (by
        have : head ∈ items := by
          rw [hitems]
          exact List.mem_cons_self
        simpa only [items] using this)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedPair_is_genuine_later_support
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    pair ∈
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
          trajectory transitionStart physicalScale cutoffOffset ∧
      (¬ (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair) ∧
      (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  have hparts :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPair_mem_and_currentKernel_not_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair
  exact ⟨hparts.1, hparts.2,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnActiveCurrentPair_pos
      trajectory transitionStart physicalScale cutoffOffset pair hparts.1⟩

/-! ## 2. Empty activated support contracts to the persistent branch -/

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor_eq_one_of_pairs_eq_nil
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (hempty :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset = []) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset =
      (1 : Q') := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor
  rw [hempty]
  rfl

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathEnvelope_le_persistentEnvelope_of_activatedPairs_eq_nil
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (hempty :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset = []) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentSupportPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  let persistentFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  let splitFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  have hpersistentPos : (0 : Q') < persistentFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hsplitPos : (0 : Q') < splitFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hpersistentOne : persistentFloor <= (1 : Q') := by
    dsimp [persistentFloor]
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor
    exact listPositiveMinOne_le_one_local _ _
  have hactivatedOne :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor_eq_one_of_pairs_eq_nil
      trajectory transitionStart physicalScale cutoffOffset hempty
  have hpersistentSplit : persistentFloor <= splitFloor := by
    dsimp [persistentFloor, splitFloor]
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
    apply (Q'.le_min'_iff _ _ _).mpr
    constructor
    · exact Q'.le_refl' _
    · rw [hactivatedOne]
      exact hpersistentOne
  have hreciprocal :
      Q'.recipPos splitFloor hsplitPos <=
        Q'.recipPos persistentFloor hpersistentPos :=
    recipPos_antitone persistentFloor splitFloor hpersistentPos hsplitPos
      hpersistentSplit
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

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPayment_of_persistentPayment_and_activatedPairs_eq_nil
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset candidate : Nat)
    (hempty :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset = [])
    (hpersistent :
      dyad candidate *
          (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentSupportPathAmplificationEnvelope
              trajectory transitionStart physicalScale cutoffOffset + 1) <=
        invSqTerm offset offset_at_least_two cutoffOffset) :
    dyad candidate *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset + 1) <=
      invSqTerm offset offset_at_least_two cutoffOffset := by
  have henvelope :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathEnvelope_le_persistentEnvelope_of_activatedPairs_eq_nil
      trajectory transitionStart physicalScale cutoffOffset hempty
  have hdenominator := Q'.add_le_add_right _ _ 1 henvelope
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hdenominator
    (dyad_nonneg candidate)
  exact Q'.le_trans' _ _ _ hscaled hpersistent

/-! ## 3. A uniform no-activation route to the existing linear schedule -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabPersistentOnlyDyadicLinearData
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
  activatedSupport_empty : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset = []
  persistentSupport_payment : forall cutoffOffset,
    dyad (precisionIntercept + cutoffOffset) *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentSupportPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset + 1) <=
      invSqTerm offset offset_at_least_two cutoffOffset
  start_absorbs_fixed_tail_cost :
    physicalNomeBaseCutoff (trajectory.nome physicalScale) - 1 +
        (precisionIntercept +
          physicalNomeTensorDyadicBurn
            (trajectory.nome physicalScale)
            (plaquetteEdgeCount (centralExtent 0 + 1))) <=
      transitionStart physicalScale

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabPersistentOnlyDyadicLinearData.toSupportSplitData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (data :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabPersistentOnlyDyadicLinearData
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSupportSplitDyadicLinearData
      trajectory transitionStart physicalScale offset offset_at_least_two where
  precisionIntercept := data.precisionIntercept
  increment_le_one := data.increment_le_one
  supportSplit_payment := by
    intro cutoffOffset
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPayment_of_persistentPayment_and_activatedPairs_eq_nil
        trajectory transitionStart physicalScale offset offset_at_least_two
        cutoffOffset (data.precisionIntercept + cutoffOffset)
        (data.activatedSupport_empty cutoffOffset)
        (data.persistentSupport_payment cutoffOffset)
  start_absorbs_fixed_tail_cost := data.start_absorbs_fixed_tail_cost

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabPersistentOnlyDyadicLinearData.toLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (data :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabPersistentOnlyDyadicLinearData
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData
      trajectory transitionStart physicalScale offset offset_at_least_two :=
  data.toSupportSplitData.toLinearData

/-! ## Axiom audit -/

#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportUseDecision
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedPair_is_genuine_later_support
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor_eq_one_of_pairs_eq_nil
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathEnvelope_le_persistentEnvelope_of_activatedPairs_eq_nil
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPayment_of_persistentPayment_and_activatedPairs_eq_nil
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabPersistentOnlyDyadicLinearData.toSupportSplitData
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabPersistentOnlyDyadicLinearData.toLinearData

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationRouteDecision
