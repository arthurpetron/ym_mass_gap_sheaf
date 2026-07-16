/-
# Three cutoff-uniform finite-law bounds for the signed spatial route

At one arbitrary common representation cutoff, the source and strict target
laws are joined through a triple-uniform source translate, the exact common
box, and one Euclidean-time translate of the target.  Each quantitative edge
is proved independently in this file.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialStageRecoding

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialFiniteBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeStability
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialModulusGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialStageRecoding
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4TimeShiftedCenteredApproximationBridge
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4TimeShiftedTargetCylinderStability
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UniformShiftTargetCylinderStability

/-! ## 1. The centered time-shift edge -/

theorem timeShiftSpinSummedCylinderBoundaryEpsilon_le_standard
    (rootCount distance : Nat) :
    timeShiftSpinSummedCylinderBoundaryEpsilon rootCount distance ≤
      spinSummedCylinderBoundaryEpsilon rootCount distance := by
  unfold timeShiftSpinSummedCylinderBoundaryEpsilon
    spinSummedCylinderBoundaryEpsilon
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.add_le_self_of_nonneg
      (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)
      (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)
      (Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedEffectiveRatio
          anchorDecoratedEffectiveRatio_nonnegative (distance + 2))
        (by decide))
  · exact ExpNeg.ofNat_nonneg' rootCount

theorem timeShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
    (rootCount distance : Nat) :
    timeShiftSpinSummedCylinderBoundaryEpsilon rootCount distance ≤
      spinSummedCylinderBoundaryCoefficient rootCount *
        HalfPow.half ^ distance := by
  exact Q'.le_trans' _ _ _
    (timeShiftSpinSummedCylinderBoundaryEpsilon_le_standard
      rootCount distance)
    (spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      rootCount distance)

theorem couplingParametricK_centeredReceding_timeShift_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff shift : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredRecedingStageBase base stage + shift)
            (timeShiftTargetCylinderEvent shift
              (centeredRecedingStageBase base stage)
              (centeredRecedingStageRoots base stage roots) predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredRecedingStageBase base stage)
            (centeredRecedingCylinderEvent
              base stage roots predicate)) ≤
      timeShiftSpinSummedCylinderBoundaryEpsilon roots.length stage := by
  have hstageRoots := centeredRecedingStageRoots_canonical
    (stage := stage) hroots
  have hside := centeredBoxBase_stage_side base stage
  have hcore := centeredRecedingTimeShiftCanonicalAtoms_core
    (base := base) (stage := stage) (shift := shift) hroots
  have hraw :=
    couplingParametricKTimeShiftFullTargetProbability_abs_sub_source_le
      hcoupling hle cutoff shift
      (centeredRecedingStageBase base stage) hstageRoots predicate
      hside hcore
  simpa only [sourceCylinderEvent,
    centeredRecedingStageRoots_length] using hraw

theorem couplingParametricK_signedSpatial_time_abs_sub_target_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialTimeStageBase base shift stage)
            (cylinderEvent
              (signedSpatialTimeStageRoots base shift stage roots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialTargetStageBase base shift stage)
            (cylinderEvent
              (signedSpatialTargetStageRoots base shift stage roots)
              predicate)) ≤
      timeShiftSpinSummedCylinderBoundaryEpsilon roots.length stage := by
  have htargetRoots := signedSpatialTargetRoots_canonical
    (base := base) (shift := shift) hroots
  have hraw := couplingParametricK_centeredReceding_timeShift_abs_sub_le
    hcoupling hle cutoff shift htargetRoots predicate
    (stage := stage)
  rw [← signedSpatialTargetStageBase_eq_centered,
    ← signedSpatialTargetStageRoots_eq_centered,
    ← signedSpatialTimeCylinderEvent_eq_timeShiftTarget,
    ← signedSpatialTargetCylinderEvent_eq_centered] at hraw
  simpa only [signedSpatialTimeStageBase,
    signedSpatialTargetRoots, List.length_map] using hraw

/-! ## 2. The triple-uniform source edge -/

theorem couplingParametricK_centeredReceding_uniformShift_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredRecedingStageBase base later)
            (centeredRecedingCylinderEvent
              base later roots predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredRecedingStageBase base earlier)
            (centeredRecedingCylinderEvent
              base earlier roots predicate)) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        roots.length earlier := by
  let sourceBase := centeredRecedingStageBase base earlier
  let padding := later - earlier
  let sourceRoots := centeredRecedingStageRoots base earlier roots
  have hsourceRoots : ∀ root, root ∈ sourceRoots →
      root ∈ canonicalSurfacePolymers sourceBase :=
    centeredRecedingStageRoots_canonical hroots
  have hside : centeredBoxBase base + earlier + earlier = sourceBase := by
    dsimp only [sourceBase, centeredRecedingStageBase,
      centeredRecedingStageRadius]
    exact centeredBoxBase_stage_side base earlier
  have hcore : ∀ target,
      target ∈ uniformShiftCylinderCanonicalAtoms
        padding sourceBase sourceRoots hsourceRoots →
      insideShiftedBoxB
        (addUniform (uniformShiftCellLower padding) earlier)
        (centeredBoxBase base)
        (boxPlaquetteAt (uniformPaddedBase padding sourceBase)
          (uniformShiftCanonicalAtomStart target)) = true := by
    dsimp only [padding, sourceBase, sourceRoots]
    exact centeredRecedingUniformShiftCanonicalAtoms_core
      hstage hroots
  have hraw :=
    couplingParametricKUniformShiftFullTargetProbability_abs_sub_source_le_of_bound
      hcoupling
      (uniformShiftTargetCylinderStabilityBound_of_anchor hcoupling hle)
      cutoff padding sourceBase hsourceRoots predicate hside hcore
  dsimp only [padding, sourceBase, sourceRoots] at hraw
  rw [← centeredRecedingStageBase_eq_uniformPadded_between hstage]
    at hraw
  rw [← centeredRecedingCylinderEvent_eq_uniformShift_between
    hstage hroots predicate] at hraw
  simpa only [centeredRecedingCylinderEvent_eq_source_at,
    centeredRecedingStageRoots_length] using hraw

theorem couplingParametricK_signedSpatial_common_abs_sub_source_le_epsilon
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialCommonStageBase base shift stage)
            (cylinderEvent
              (signedSpatialCommonUniformRoots base shift stage roots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialSourceStageBase base stage)
            (cylinderEvent
              (signedSpatialSourceStageRoots base stage roots)
              predicate)) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        roots.length stage := by
  have hstage : stage ≤ stage + (shift + shift + shift) :=
    Nat.le_add_right stage (shift + shift + shift)
  have hraw := couplingParametricK_centeredReceding_uniformShift_abs_sub_le
    hcoupling hle cutoff hstage hroots predicate
  rw [← signedSpatialCommonStageBase_eq_centered,
    ← signedSpatialSourceStageBase_eq_centered,
    ← signedSpatialCommonCylinderEvent_eq_centered hroots predicate,
    ← signedSpatialSourceCylinderEvent_eq_centered] at hraw
  exact hraw

theorem couplingParametricK_signedSpatial_common_abs_sub_source_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialCommonStageBase base shift stage)
            (cylinderEvent
              (signedSpatialCommonUniformRoots base shift stage roots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialSourceStageBase base stage)
            (cylinderEvent
              (signedSpatialSourceStageRoots base stage roots)
              predicate)) ≤
      spinSummedCylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ stage := by
  have hvolume := centeredRecedingVolumeModulus_of_anchor
    (predicate := predicate) hcoupling hle hroots
  have hstage : stage ≤ stage + (shift + shift + shift) :=
    Nat.le_add_right stage (shift + shift + shift)
  have hraw := hvolume.2 cutoff hstage
  rw [← signedSpatialCommonStageBase_eq_centered,
    ← signedSpatialSourceStageBase_eq_centered,
    ← signedSpatialCommonCylinderEvent_eq_centered hroots predicate,
    ← signedSpatialSourceCylinderEvent_eq_centered] at hraw
  exact hraw

/-! ## 3. Ordinary zero-extension from time box to common box -/

theorem couplingParametricK_signedSpatial_common_abs_sub_time_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialCommonStageBase base shift stage)
            (cylinderEvent
              (signedSpatialCommonUniformRoots base shift stage roots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialTimeStageBase base shift stage)
            (cylinderEvent
              (signedSpatialTimeStageRoots base shift stage roots)
              predicate)) ≤
      spinSummedCylinderBoundaryEpsilon roots.length (stage + 1) := by
  let targetBase := signedSpatialTargetBase base shift
  let targetRoots := signedSpatialTargetRoots base shift roots
  have htargetRoots : ∀ root, root ∈ targetRoots →
      root ∈ canonicalSurfacePolymers targetBase :=
    signedSpatialTargetRoots_canonical hroots
  let timeRoots := signedSpatialTimeStageRoots base shift stage roots
  have htimeRoots : ∀ root, root ∈ timeRoots →
      root ∈ canonicalSurfacePolymers
        (signedSpatialTimeStageBase base shift stage) := by
    intro root hroot
    dsimp only [timeRoots] at hroot
    rw [signedSpatialTimeStageRoots_eq_timeShifted] at hroot
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hroot
    apply timeShiftCanonicalRoot_canonical
    rw [signedSpatialTargetStageRoots_eq_centered] at hsource
    exact centeredRecedingStageRoots_canonical htargetRoots source hsource
  have hinside : ∀ root, root ∈ timeRoots →
      PolymerInsideBox
        (centeredFaceQueryInner targetBase stage + shift)
        (signedSpatialTimeStageBase base shift stage) root := by
    have hgeneric := centeredRecedingTimeShiftedRoots_inside_originBox
      (base := targetBase) (stage := stage) (shift := shift)
      htargetRoots
    rw [← signedSpatialTargetStageBase_eq_centered,
      ← signedSpatialTargetStageRoots_eq_centered] at hgeneric
    intro root hroot
    apply hgeneric root
    rw [← signedSpatialTimeStageRoots_eq_timeShifted]
    exact hroot
  have hbox :
      centeredFaceQueryInner targetBase stage + shift + (stage + 1) =
        signedSpatialTimeStageBase base shift stage := by
    simpa only [targetBase, signedSpatialTimeStageBase,
      signedSpatialTargetStageBase_eq_centered] using
      (centeredTimeShiftInner_add_distance targetBase stage shift)
  have hsmall := signedSpatialTimeStageBase_le_common base shift stage
  have hraw :=
    couplingParametricKCompatibleCylinderProbability_cross_volume_abs_sub_le
      hcoupling hle cutoff hsmall timeRoots htimeRoots predicate
      hinside hbox
  have hevent :
      markedCylinderEvent
          (transportedCanonicalCylinderAtoms hsmall timeRoots htimeRoots)
          predicate =
        cylinderEvent
          (signedSpatialCommonUniformRoots base shift stage roots)
          predicate := by
    exact Eq.trans
      (markedTransportedCylinderEvent_eq_target
        hsmall timeRoots htimeRoots predicate)
      (signedSpatialTimeCylinderEvent_transport_eq_commonUniform
        hroots predicate)
  rw [hevent] at hraw
  simpa only [sourceCylinderEvent, timeRoots,
    signedSpatialTimeStageRoots, List.length_map] using hraw

#print axioms timeShiftSpinSummedCylinderBoundaryEpsilon_le_standard
#print axioms timeShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
#print axioms couplingParametricK_centeredReceding_timeShift_abs_sub_le
#print axioms couplingParametricK_signedSpatial_time_abs_sub_target_le
#print axioms couplingParametricK_centeredReceding_uniformShift_abs_sub_le
#print axioms couplingParametricK_signedSpatial_common_abs_sub_source_le_epsilon
#print axioms couplingParametricK_signedSpatial_common_abs_sub_source_le
#print axioms couplingParametricK_signedSpatial_common_abs_sub_time_le

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialFiniteBounds
