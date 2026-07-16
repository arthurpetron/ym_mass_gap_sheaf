/-
# Protected geometry for the signed spatial-law comparison

The exact common-box law alignment leaves three quantitative finite-volume
edges.  This file discharges the two geometric inputs needed for the
time-shift edge and for the final ordinary zero-extension edge.  They are
kept independent of every probability estimate and cutoff schedule.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialLaw

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialModulusGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialLaw
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4TimeShiftedCenteredApproximationBridge
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open Dir4

/-! ## 1. Time translation preserves a centered protected core -/

/-- Translating a plaquette in Euclidean time translates the lower corner of
its protected box by exactly the same amount.  This is a Boolean identity,
not merely an implication about coordinates. -/
theorem insideShiftedBoxB_timeShift_centered
    (shift stage inner : Nat) (plaquette : Z4Plaq) :
    insideShiftedBoxB
        (addUniform (timeShiftCellLower shift) stage) inner
        (timeShiftPlaquette shift plaquette) =
      insideShiftedBoxB (uniformNatLower stage) inner plaquette := by
  apply Bool.eq_iff_iff.mpr
  rw [insideShiftedBoxB_true_iff, insideShiftedBoxB_true_iff]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp only [addUniform, timeShiftCellLower, uniformNatLower,
    timeShiftPlaquette, timeShiftVertex, cPlaq, vComp, Nat.zero_add]
  constructor
  · rintro ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
    refine ⟨ha0, ha1, hb0, hb1, hc0, hc1, ?_, ?_⟩
    · have hd0' : shift + stage ≤ shift + d := by
        simpa only [Nat.add_comm] using hd0
      exact Nat.le_of_add_le_add_left hd0'
    · apply Nat.lt_of_add_lt_add_left (n := shift)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hd1
  · rintro ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
    refine ⟨ha0, ha1, hb0, hb1, hc0, hc1, ?_, ?_⟩
    · simpa only [Nat.add_comm] using Nat.add_le_add_left hd0 shift
    · have hshifted := Nat.add_lt_add_left hd1 shift
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hshifted

/-- A time translate of a centered receding stage has protected distance
`stage` from every face of its translated cell. -/
theorem centeredRecedingTimeShiftCanonicalAtoms_core
    {base stage shift : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    let sourceBase := centeredRecedingStageBase base stage
    let sourceRoots := centeredRecedingStageRoots base stage roots
    let hsourceRoots : ∀ root, root ∈ sourceRoots →
        root ∈ canonicalSurfacePolymers sourceBase :=
      centeredRecedingStageRoots_canonical hroots
    ∀ target,
      target ∈ timeShiftCylinderCanonicalAtoms
        shift sourceBase sourceRoots hsourceRoots →
      insideShiftedBoxB
        (addUniform (timeShiftCellLower shift) stage)
        (centeredBoxBase base)
        (boxPlaquetteAt (sourceBase + shift)
          (canonicalAtomStart target)) = true := by
  intro sourceBase sourceRoots hsourceRoots target htarget
  have htargetValue : target.val ∈
      (timeShiftCylinderCanonicalAtoms
        shift sourceBase sourceRoots hsourceRoots).map Subtype.val :=
    List.mem_map.mpr ⟨target, htarget, rfl⟩
  rw [timeShiftCylinderCanonicalAtoms_values] at htargetValue
  unfold timeShiftedCylinderRoots at htargetValue
  obtain ⟨sourceRoot, hsourceRoot, htargetEq⟩ :=
    List.mem_map.mp htargetValue
  have htargetPlaquette :
      boxPlaquetteAt (sourceBase + shift) (canonicalAtomStart target) ∈
        geometricPolymer (sourceBase + shift) target.val :=
    List.mem_map.mpr ⟨canonicalAtomStart target,
      canonicalAtomStart_mem target, rfl⟩
  rw [← htargetEq] at htargetPlaquette
  have htimeSupport := timeShiftCanonicalRoot_sameSupport (shift := shift)
    (hsourceRoots sourceRoot hsourceRoot)
  have hmapped := htimeSupport.1 _ htargetPlaquette
  obtain ⟨sourcePlaquette, hsourcePlaquette, hplaquetteEq⟩ :=
    List.mem_map.mp hmapped
  obtain ⟨sourceFace, hsourceFace, hsourcePlaquetteEq⟩ :=
    List.mem_map.mp hsourcePlaquette
  dsimp only [sourceRoots] at hsourceRoot
  unfold centeredRecedingStageRoots centeredRecedingStageRadius
    centeredOffsetCylinderRoots at hsourceRoot
  obtain ⟨root, hroot, hsourceRootEq⟩ := List.mem_map.mp hsourceRoot
  have hcenteredFace : sourceFace ∈
      centeredOffsetCanonicalRoot (base + stage) base root := by
    rw [hsourceRootEq]
    exact hsourceFace
  have hcore := centeredOffsetCanonicalRoot_inside_receding_core
    (base := base) (earlier := 0) (later := stage)
    (Nat.zero_le stage) (hroots root hroot) hcenteredFace
  dsimp only [sourceBase, centeredRecedingStageBase,
    centeredRecedingStageRadius] at hplaquetteEq hsourcePlaquetteEq hcore ⊢
  rw [← hplaquetteEq, ← hsourcePlaquetteEq]
  rw [insideShiftedBoxB_timeShift_centered]
  simpa only [Nat.sub_zero, Nat.add_zero, addUniform,
    uniformNatLower] using hcore

/-! ## 2. The translated roots remain deep in an ordinary origin box -/

/-- Time-shifting every root of a centered receding stage increases the
origin-box inner side by `shift` while preserving protected distance
`stage + 1`. -/
theorem centeredRecedingTimeShiftedRoots_inside_originBox
    {base stage shift : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    let sourceBase := centeredRecedingStageBase base stage
    let sourceRoots := centeredRecedingStageRoots base stage roots
    ∀ target,
      target ∈ timeShiftedCylinderRoots shift sourceBase sourceRoots →
      PolymerInsideBox (centeredFaceQueryInner base stage + shift)
        (sourceBase + shift) target := by
  intro sourceBase sourceRoots target htarget plaquette hplaquette
  unfold timeShiftedCylinderRoots at htarget
  obtain ⟨sourceRoot, hsourceRoot, htargetEq⟩ :=
    List.mem_map.mp htarget
  have hsourceCanonical :=
    centeredRecedingStageRoots_canonical hroots sourceRoot hsourceRoot
  rw [← htargetEq] at hplaquette
  have htimeSupport := timeShiftCanonicalRoot_sameSupport (shift := shift)
    hsourceCanonical
  have hmapped := htimeSupport.1 plaquette hplaquette
  obtain ⟨sourcePlaquette, hsourcePlaquette, hplaquetteEq⟩ :=
    List.mem_map.mp hmapped
  rw [← hplaquetteEq]
  apply timeShiftPlaquette_mem_box_add
  exact centeredRecedingStageRoots_inside_originBox hroots
    sourceRoot hsourceRoot sourcePlaquette hsourcePlaquette

theorem centeredTimeShiftInner_add_distance
    (base stage shift : Nat) :
    centeredFaceQueryInner base stage + shift + (stage + 1) =
      centeredRecedingStageBase base stage + shift := by
  rw [← centeredFaceQueryInner_add_distance base stage]
  omega

#print axioms insideShiftedBoxB_timeShift_centered
#print axioms centeredRecedingTimeShiftCanonicalAtoms_core
#print axioms centeredRecedingTimeShiftedRoots_inside_originBox
#print axioms centeredTimeShiftInner_add_distance

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialModulusGeometry
