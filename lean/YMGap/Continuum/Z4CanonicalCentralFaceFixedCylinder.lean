/-
# One fixed cylinder chart for the central truncated face event

For truncation floor `m`, take the source box of side `2*m+1` and its central
`p01` plaquette.  Uniform padding by `stage` carries that plaquette to the
central plaquette of the padded target box.  This file gives both plaquettes
explicit numerical face identifiers and proves that face membership is
preserved by canonical-root transport.

Combining that persistent face with the pinned localization theorem shows
that the entire target list of size-`<m` roots pinned at the target face is,
as a finite set, exactly the affine image of one fixed source list.  Hence the
target truncated face event is literally the fixed-chart occurrence event at
every stage.

This is an observable compiler.  It does not yet identify its thermodynamic
limit with an Osterwalder--Schrader same-object autocorrelation.
-/

import YMGap.Continuum.Z4CanonicalFaceEventPinnedLocalization
import YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary

namespace YMGap.Continuum.Z4CanonicalCentralFaceFixedCylinder

set_option autoImplicit false

open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFaceEventCylinderCompiler
open YMGap.Continuum.Z4CanonicalFaceEventPinnedLocalization
open YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

/-! ## 1. An explicitly indexed central plaquette at every padded stage -/

def pinnedFaceSourceBase (sizeFloor : Nat) : Nat :=
  1 + sizeFloor + sizeFloor

def pinnedFaceStageBase (sizeFloor stage : Nat) : Nat :=
  uniformPaddedBase stage (pinnedFaceSourceBase sizeFloor)

def pinnedFacePlaquette (sizeFloor stage : Nat) : Z4Plaq :=
  ((sizeFloor + stage, sizeFloor + stage,
      sizeFloor + stage, sizeFloor + stage), .p01)

theorem pinnedFacePlaquette_mem_box
    (sizeFloor stage : Nat) :
    pinnedFacePlaquette sizeFloor stage ∈
      boxPlaquettes (pinnedFaceStageBase sizeFloor stage) := by
  rw [mem_boxPlaquettes]
  simp only [pinnedFacePlaquette, pinnedFaceStageBase,
    pinnedFaceSourceBase, uniformPaddedBase]
  exact ⟨by omega, by omega, by omega, by omega⟩

def pinnedFaceSingletonRoot (sizeFloor stage : Nat) : List Nat :=
  singletonGeometricRoot (pinnedFaceStageBase sizeFloor stage)
    (pinnedFacePlaquette sizeFloor stage)

def pinnedFaceId (sizeFloor stage : Nat) : Nat :=
  (singletonGeometricRoot_nonempty
    (pinnedFacePlaquette_mem_box sizeFloor stage)).1

theorem pinnedFaceId_mem_singletonRoot
    (sizeFloor stage : Nat) :
    pinnedFaceId sizeFloor stage ∈
      pinnedFaceSingletonRoot sizeFloor stage := by
  exact (singletonGeometricRoot_nonempty
    (pinnedFacePlaquette_mem_box sizeFloor stage)).2

theorem pinnedFaceId_physical (sizeFloor stage : Nat) :
    pinnedFaceId sizeFloor stage ∈
      physicalFaceEdges (pinnedFaceStageBase sizeFloor stage) := by
  exact (mem_geometricSupportIds_iff
    (pinnedFaceStageBase sizeFloor stage)
    [pinnedFacePlaquette sizeFloor stage]
    (pinnedFaceId sizeFloor stage)).1
      (pinnedFaceId_mem_singletonRoot sizeFloor stage) |>.1

theorem boxPlaquetteAt_pinnedFaceId (sizeFloor stage : Nat) :
    boxPlaquetteAt (pinnedFaceStageBase sizeFloor stage)
        (pinnedFaceId sizeFloor stage) =
      pinnedFacePlaquette sizeFloor stage := by
  have hparts := (mem_geometricSupportIds_iff
    (pinnedFaceStageBase sizeFloor stage)
    [pinnedFacePlaquette sizeFloor stage]
    (pinnedFaceId sizeFloor stage)).1
      (pinnedFaceId_mem_singletonRoot sizeFloor stage)
  exact List.mem_singleton.mp hparts.2

theorem uniformShift_pinnedFacePlaquette
    (sizeFloor stage : Nat) :
    uniformShiftPlaquette stage (pinnedFacePlaquette sizeFloor 0) =
      pinnedFacePlaquette sizeFloor stage := by
  simp [pinnedFacePlaquette, uniformShiftPlaquette, uniformShiftVertex]

/-- The chosen target face is at the center of the protected one-cell core,
with margin `sizeFloor` from every face of the shifted source box. -/
theorem pinnedFaceId_in_protected_core
    (sizeFloor stage : Nat) :
    insideShiftedBoxB
      (addUniform (uniformLower stage) sizeFloor) 1
      (boxPlaquetteAt (pinnedFaceStageBase sizeFloor stage)
        (pinnedFaceId sizeFloor stage)) = true := by
  rw [boxPlaquetteAt_pinnedFaceId, insideShiftedBoxB_true_iff]
  simp only [pinnedFacePlaquette, uniformLower, addUniform, cPlaq, vComp]
  exact ⟨by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

/-! ## 2. The pinned face itself is preserved by root transport -/

private theorem physical_of_mem_canonicalRoot
    {base face : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (hface : face ∈ root) :
    face ∈ physicalFaceEdges base :=
  mem_of_mem_sublists (physicalFaceEdges base) root
    (canonicalSurfacePolymer_mem_faceSupports hroot) face hface

theorem pinnedFaceId_mem_uniformShiftCanonicalRoot_iff
    {sizeFloor stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers
      (pinnedFaceSourceBase sizeFloor)) :
    pinnedFaceId sizeFloor stage ∈
        uniformShiftCanonicalRoot stage
          (pinnedFaceSourceBase sizeFloor) root ↔
      pinnedFaceId sizeFloor 0 ∈ root := by
  constructor
  · intro htargetFace
    obtain ⟨sourceFace, hsourceFace, hpoint⟩ :=
      uniformShiftRootMemberSource
        (canonicalSurfacePolymer_mem_faceSupports hroot) htargetFace
    have hcentralPoint :
        uniformShiftPlaquette stage
            (boxPlaquetteAt (pinnedFaceSourceBase sizeFloor)
              (pinnedFaceId sizeFloor 0)) =
          boxPlaquetteAt
            (uniformPaddedBase stage (pinnedFaceSourceBase sizeFloor))
            (pinnedFaceId sizeFloor stage) := by
      rw [show pinnedFaceSourceBase sizeFloor =
          pinnedFaceStageBase sizeFloor 0 by
        simp [pinnedFaceSourceBase, pinnedFaceStageBase, uniformPaddedBase]]
      rw [boxPlaquetteAt_pinnedFaceId,
        uniformShift_pinnedFacePlaquette]
      exact (boxPlaquetteAt_pinnedFaceId sizeFloor stage).symm
    have hsourcePoint :
        boxPlaquetteAt (pinnedFaceSourceBase sizeFloor) sourceFace =
          boxPlaquetteAt (pinnedFaceSourceBase sizeFloor)
            (pinnedFaceId sizeFloor 0) := by
      apply uniformShiftPlaquette_injective stage
      exact hpoint.trans hcentralPoint.symm
    have hsourcePhysical := physical_of_mem_canonicalRoot
      hroot hsourceFace
    have hcentralPhysical : pinnedFaceId sizeFloor 0 ∈
        physicalFaceEdges (pinnedFaceSourceBase sizeFloor) := by
      simpa [pinnedFaceStageBase, uniformPaddedBase] using
        pinnedFaceId_physical sizeFloor 0
    have heq := boxPlaquetteAt_injective_on_physical
      hsourcePhysical hcentralPhysical hsourcePoint
    simpa only [heq] using hsourceFace
  · intro hsourceCentral
    obtain ⟨targetFace, htargetFace, hpoint⟩ :=
      uniformShiftRootMemberTarget
        (canonicalSurfacePolymer_mem_faceSupports hroot) hsourceCentral
    have hcentralPoint :
        uniformShiftPlaquette stage
            (boxPlaquetteAt (pinnedFaceSourceBase sizeFloor)
              (pinnedFaceId sizeFloor 0)) =
          boxPlaquetteAt
            (uniformPaddedBase stage (pinnedFaceSourceBase sizeFloor))
            (pinnedFaceId sizeFloor stage) := by
      rw [show pinnedFaceSourceBase sizeFloor =
          pinnedFaceStageBase sizeFloor 0 by
        simp [pinnedFaceSourceBase, pinnedFaceStageBase, uniformPaddedBase]]
      rw [boxPlaquetteAt_pinnedFaceId,
        uniformShift_pinnedFacePlaquette]
      exact (boxPlaquetteAt_pinnedFaceId sizeFloor stage).symm
    have htargetCanonical := uniformShiftCanonicalRoot_canonical
      (padding := stage) hroot
    have htargetPhysical := physical_of_mem_canonicalRoot
      htargetCanonical htargetFace
    have hcentralPhysical : pinnedFaceId sizeFloor stage ∈
        physicalFaceEdges
          (uniformPaddedBase stage (pinnedFaceSourceBase sizeFloor)) := by
      exact pinnedFaceId_physical sizeFloor stage
    have heq := boxPlaquetteAt_injective_on_physical
      htargetPhysical hcentralPhysical (hpoint.symm.trans hcentralPoint)
    simpa only [heq] using htargetFace

/-! ## 3. Transport preserves the component size exactly -/

theorem uniformShiftCanonicalRoot_length_eq
    {padding base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    (uniformShiftCanonicalRoot padding base root).length = root.length := by
  have htarget := uniformShiftCanonicalRoot_canonical
    (padding := padding) hroot
  have htargetNodup := geometricPolymer_nodup
    (canonicalSurfacePolymer_mem_faceSupports htarget)
  have hsourceNodup := geometricPolymer_nodup
    (canonicalSurfacePolymer_mem_faceSupports hroot)
  have hmappedNodup :
      ((geometricPolymer base root).map
        (uniformShiftPlaquette padding)).Nodup :=
    nodup_map_of_injOn (uniformShiftPlaquette padding)
      (geometricPolymer base root) hsourceNodup
      (fun _ _ _ _ heq => uniformShiftPlaquette_injective padding heq)
  have hlength := sameSupport_length_eq_of_nodup
    (uniformShiftCanonicalRoot_sameSupport hroot)
    htargetNodup hmappedNodup
  calc
    (uniformShiftCanonicalRoot padding base root).length =
        (geometricPolymer (uniformPaddedBase padding base)
          (uniformShiftCanonicalRoot padding base root)).length := by
      exact (List.length_map
        (f := boxPlaquetteAt (uniformPaddedBase padding base))).symm
    _ = ((geometricPolymer base root).map
          (uniformShiftPlaquette padding)).length := hlength
    _ = (geometricPolymer base root).length :=
      List.length_map (f := uniformShiftPlaquette padding)
    _ = root.length :=
      List.length_map (f := boxPlaquetteAt base)

/-! ## 4. Exact fixed-root chart for every truncated target event -/

def pinnedFaceFixedRoots (sizeFloor : Nat) : List (List Nat) :=
  canonicalPinnedBelowSizePolymers
    (pinnedFaceSourceBase sizeFloor)
    (pinnedFaceId sizeFloor 0) sizeFloor

def pinnedFaceStageRoots (sizeFloor stage : Nat) : List (List Nat) :=
  (pinnedFaceFixedRoots sizeFloor).map
    (uniformShiftCanonicalRoot stage (pinnedFaceSourceBase sizeFloor))

theorem mem_pinnedFaceStageRoots_iff
    {sizeFloor stage : Nat} {target : List Nat} :
    target ∈ pinnedFaceStageRoots sizeFloor stage ↔
      target ∈ canonicalPinnedBelowSizePolymers
        (pinnedFaceStageBase sizeFloor stage)
        (pinnedFaceId sizeFloor stage) sizeFloor := by
  constructor
  · intro htarget
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
    have hparts := mem_canonicalPinnedBelowSizePolymers_iff.mp hsource
    rw [← heq]
    apply mem_canonicalPinnedBelowSizePolymers_iff.mpr
    exact ⟨uniformShiftCanonicalRoot_canonical hparts.1,
      (pinnedFaceId_mem_uniformShiftCanonicalRoot_iff hparts.1).2
        hparts.2.1,
      by simpa only [uniformShiftCanonicalRoot_length_eq hparts.1]
        using hparts.2.2⟩
  · intro htarget
    have hparts := mem_canonicalPinnedBelowSizePolymers_iff.mp htarget
    have hsmallFloor : target.length < sizeFloor + 2 := by omega
    have hsource := smallPinnedCanonicalRootSource
      hparts.1 hparts.2.1
      (pinnedFaceId_in_protected_core sizeFloor stage)
      hsmallFloor
    obtain ⟨source, hsourceCanonical, hround⟩ := hsource
    have hsourceCanonical' : source ∈ canonicalSurfacePolymers
        (pinnedFaceSourceBase sizeFloor) := by
      simpa [pinnedFaceSourceBase] using hsourceCanonical
    have hround' : uniformShiftCanonicalRoot stage
        (pinnedFaceSourceBase sizeFloor) source = target := by
      simpa [pinnedFaceSourceBase] using hround
    apply List.mem_map.mpr
    refine ⟨source, ?_, hround'⟩
    apply mem_canonicalPinnedBelowSizePolymers_iff.mpr
    refine ⟨hsourceCanonical', ?_, ?_⟩
    · apply (pinnedFaceId_mem_uniformShiftCanonicalRoot_iff
        (sizeFloor := sizeFloor) (stage := stage)
        hsourceCanonical').1
      rw [hround']
      exact hparts.2.1
    · rw [← uniformShiftCanonicalRoot_length_eq hsourceCanonical',
        hround']
      exact hparts.2.2

/-- The Boolean occurrence predicate used by the face compiler has a simple
root-membership semantics independent of root order. -/
theorem sourceCanonicalFaceCylinderEvent_true_iff
    (roots family : List (List Nat)) :
    sourceCylinderEvent roots canonicalFaceCylinderPredicate family = true ↔
      ∃ root, root ∈ roots ∧ root ∈ family := by
  unfold sourceCylinderEvent cylinderEvent canonicalFaceCylinderPredicate
    familyOccurrenceFingerprint
  constructor
  · intro hevent
    obtain ⟨bit, hbit, htrue⟩ := List.any_eq_true.mp hevent
    obtain ⟨root, hroot, heq⟩ := List.mem_map.mp hbit
    refine ⟨root, hroot, ?_⟩
    unfold familyContainsPolymerB at heq
    exact of_decide_eq_true (heq.trans htrue)
  · rintro ⟨root, hroot, hfamily⟩
    apply List.any_eq_true.mpr
    refine ⟨true, ?_, rfl⟩
    apply List.mem_map.mpr
    refine ⟨root, hroot, ?_⟩
    unfold familyContainsPolymerB
    exact decide_eq_true hfamily

/-- At every stage, the target truncated central-face event is literally the
event represented by the transported fixed source chart. -/
theorem pinnedFaceTruncatedCylinderEvent_eq_fixedStage
    (sizeFloor stage : Nat) (family : List (List Nat)) :
    canonicalFaceTruncatedCylinderEvent
        (pinnedFaceStageBase sizeFloor stage)
        (pinnedFaceId sizeFloor stage) sizeFloor family =
      sourceCylinderEvent (pinnedFaceStageRoots sizeFloor stage)
        canonicalFaceCylinderPredicate family := by
  unfold canonicalFaceTruncatedCylinderEvent
  apply Bool.eq_iff_iff.mpr
  rw [sourceCanonicalFaceCylinderEvent_true_iff,
    sourceCanonicalFaceCylinderEvent_true_iff]
  constructor
  · rintro ⟨root, hroot, hfamily⟩
    exact ⟨root, (mem_pinnedFaceStageRoots_iff).2 hroot, hfamily⟩
  · rintro ⟨root, hroot, hfamily⟩
    exact ⟨root, (mem_pinnedFaceStageRoots_iff).1 hroot, hfamily⟩

def pinnedFaceFixedStrictCylinderVector
    (sizeFloor : Nat) : StrictJointCylinderVector
      (pinnedFaceSourceBase sizeFloor) :=
  canonicalFaceTruncatedStrictCylinderVector
    (pinnedFaceSourceBase sizeFloor)
    (pinnedFaceId sizeFloor 0) sizeFloor

#print axioms pinnedFaceId_physical
#print axioms boxPlaquetteAt_pinnedFaceId
#print axioms pinnedFaceId_in_protected_core
#print axioms pinnedFaceId_mem_uniformShiftCanonicalRoot_iff
#print axioms uniformShiftCanonicalRoot_length_eq
#print axioms mem_pinnedFaceStageRoots_iff
#print axioms sourceCanonicalFaceCylinderEvent_true_iff
#print axioms pinnedFaceTruncatedCylinderEvent_eq_fixedStage

end YMGap.Continuum.Z4CanonicalCentralFaceFixedCylinder
