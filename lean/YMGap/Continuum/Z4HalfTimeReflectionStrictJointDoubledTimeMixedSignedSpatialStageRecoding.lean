/-
# Exact stage recodings for the signed spatial-law route

This file identifies every named source, target, time-shifted, and common-box
object with the generic finite-volume interfaces used by the quantitative
stability theorems.  No probability estimate is used here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialModulusGeometry

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialStageRecoding

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialLaw
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

def signedSpatialTargetRoots
    (base shift : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (spatialShiftCanonicalRoot shift base)

theorem signedSpatialTargetRoots_canonical
    {base shift : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ signedSpatialTargetRoots base shift roots →
      target ∈ canonicalSurfacePolymers
        (signedSpatialTargetBase base shift) := by
  intro target htarget
  obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp htarget
  exact spatialShiftCanonicalRoot_canonical (hroots root hroot)

def signedSpatialTargetStageRoots
    (base shift stage : Nat) (roots : List (List Nat)) :
    List (List Nat) :=
  roots.map (signedSpatialTargetStageRoot base shift stage)

theorem signedSpatialSourceStageBase_eq_centered
    (base stage : Nat) :
    signedSpatialSourceStageBase base stage =
      centeredRecedingStageBase base stage := rfl

theorem signedSpatialTargetStageBase_eq_centered
    (base shift stage : Nat) :
    signedSpatialTargetStageBase base shift stage =
      centeredRecedingStageBase
        (signedSpatialTargetBase base shift) stage := rfl

theorem signedSpatialCommonStageBase_eq_centered
    (base shift stage : Nat) :
    signedSpatialCommonStageBase base shift stage =
      centeredRecedingStageBase base
        (stage + (shift + shift + shift)) := by
  unfold signedSpatialCommonStageBase signedSpatialSourceStageBase
    centeredRecedingStageBase centeredRecedingStageRadius
    uniformPaddedBase centeredBoxBase
  omega

theorem signedSpatialSourceStageRoots_eq_centered
    (base stage : Nat) (roots : List (List Nat)) :
    signedSpatialSourceStageRoots base stage roots =
      centeredRecedingStageRoots base stage roots := rfl

theorem signedSpatialTargetStageRoots_eq_centered
    (base shift stage : Nat) (roots : List (List Nat)) :
    signedSpatialTargetStageRoots base shift stage roots =
      centeredRecedingStageRoots
        (signedSpatialTargetBase base shift) stage
        (signedSpatialTargetRoots base shift roots) := by
  unfold signedSpatialTargetStageRoots signedSpatialTargetStageRoot
    signedSpatialTargetRoots centeredRecedingStageRoots
    centeredRecedingStageRadius centeredOffsetCylinderRoots
  rw [List.map_map]
  rfl

theorem signedSpatialTimeStageRoots_eq_timeShifted
    (base shift stage : Nat) (roots : List (List Nat)) :
    signedSpatialTimeStageRoots base shift stage roots =
      timeShiftedCylinderRoots shift
        (signedSpatialTargetStageBase base shift stage)
        (signedSpatialTargetStageRoots base shift stage roots) := by
  unfold signedSpatialTimeStageRoots signedSpatialTimeStageRoot
    timeShiftedCylinderRoots signedSpatialTargetStageRoots
  rw [List.map_map]
  rfl

theorem signedSpatialCommonUniformRoots_eq_uniformShifted
    (base shift stage : Nat) (roots : List (List Nat)) :
    signedSpatialCommonUniformRoots base shift stage roots =
      uniformShiftedCylinderRoots (shift + shift + shift)
        (signedSpatialSourceStageBase base stage)
        (signedSpatialSourceStageRoots base stage roots) := by
  unfold signedSpatialCommonUniformRoots signedSpatialCommonUniformRoot
    uniformShiftedCylinderRoots signedSpatialSourceStageRoots
  rw [List.map_map]
  rfl

theorem signedSpatialCommonUniformRoots_eq_centered
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    signedSpatialCommonUniformRoots base shift stage roots =
      centeredRecedingStageRoots base
        (stage + (shift + shift + shift)) roots := by
  have hstage : stage ≤ stage + (shift + shift + shift) :=
    Nat.le_add_right stage (shift + shift + shift)
  have halignment := centeredRecedingStageRoots_eq_uniformShift_between
    hstage hroots
  rw [signedSpatialCommonUniformRoots_eq_uniformShifted,
    signedSpatialSourceStageBase_eq_centered,
    signedSpatialSourceStageRoots_eq_centered]
  unfold uniformShiftedCylinderRoots
  simp only [Nat.add_sub_cancel_left] at halignment
  exact halignment.symm

theorem signedSpatialSourceCylinderEvent_eq_centered
    (base stage : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) :
    cylinderEvent (signedSpatialSourceStageRoots base stage roots)
        predicate =
      centeredRecedingCylinderEvent base stage roots predicate := by
  rw [signedSpatialSourceStageRoots_eq_centered]
  rfl

theorem signedSpatialTargetCylinderEvent_eq_centered
    (base shift stage : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) :
    cylinderEvent
        (signedSpatialTargetStageRoots base shift stage roots) predicate =
      centeredRecedingCylinderEvent
        (signedSpatialTargetBase base shift) stage
        (signedSpatialTargetRoots base shift roots) predicate := by
  rw [signedSpatialTargetStageRoots_eq_centered]
  rfl

theorem signedSpatialTimeCylinderEvent_eq_timeShiftTarget
    (base shift stage : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) :
    cylinderEvent (signedSpatialTimeStageRoots base shift stage roots)
        predicate =
      timeShiftTargetCylinderEvent shift
        (signedSpatialTargetStageBase base shift stage)
        (signedSpatialTargetStageRoots base shift stage roots)
        predicate := by
  rw [signedSpatialTimeStageRoots_eq_timeShifted]
  rfl

theorem signedSpatialCommonCylinderEvent_eq_uniformShiftTarget
    (base shift stage : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) :
    cylinderEvent
        (signedSpatialCommonUniformRoots base shift stage roots) predicate =
      uniformShiftTargetCylinderEvent (shift + shift + shift)
        (signedSpatialSourceStageBase base stage)
        (signedSpatialSourceStageRoots base stage roots) predicate := by
  rw [signedSpatialCommonUniformRoots_eq_uniformShifted]
  rfl

theorem signedSpatialCommonCylinderEvent_eq_centered
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    cylinderEvent
        (signedSpatialCommonUniformRoots base shift stage roots) predicate =
      centeredRecedingCylinderEvent base
        (stage + (shift + shift + shift)) roots predicate := by
  rw [signedSpatialCommonUniformRoots_eq_centered hroots]
  rfl

#print axioms signedSpatialTargetRoots_canonical
#print axioms signedSpatialSourceStageBase_eq_centered
#print axioms signedSpatialTargetStageBase_eq_centered
#print axioms signedSpatialCommonStageBase_eq_centered
#print axioms signedSpatialSourceStageRoots_eq_centered
#print axioms signedSpatialTargetStageRoots_eq_centered
#print axioms signedSpatialTimeStageRoots_eq_timeShifted
#print axioms signedSpatialCommonUniformRoots_eq_uniformShifted
#print axioms signedSpatialCommonUniformRoots_eq_centered
#print axioms signedSpatialSourceCylinderEvent_eq_centered
#print axioms signedSpatialTargetCylinderEvent_eq_centered
#print axioms signedSpatialTimeCylinderEvent_eq_timeShiftTarget
#print axioms signedSpatialCommonCylinderEvent_eq_uniformShiftTarget
#print axioms signedSpatialCommonCylinderEvent_eq_centered

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialStageRecoding
