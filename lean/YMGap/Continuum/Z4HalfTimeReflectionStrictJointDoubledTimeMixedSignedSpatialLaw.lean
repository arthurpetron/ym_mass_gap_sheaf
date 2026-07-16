/-
# Exact spatial-law alignment for the doubled-time signed route

At one signed-centered diagonal stage, the strict target root is obtained by
a spatial shift in its initial chart followed by the chart's centered
receding shift.  Its corner coordinates differ from the corresponding source
stage root by `(3s,3s,3s,2s)`.

One further time shift of size `s` therefore gives the same geometric support
as a uniform shift of the source stage root by `3s`.  The two canonical roots
live in boxes whose sides differ by `s`; transporting the former once by
zero-extension makes the canonical roots literally equal.  This file proves
that fact successively for one plaquette, one root, root lists, Boolean
cylinder events, and arbitrary-cutoff finite laws.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedLawFrontier
import YMGap.Continuum.Z4TimeShiftedCenteredApproximationBridge
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4TimeShiftedCenteredApproximationBridge
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

private theorem sameSupport_map_local
    {left right : List Z4Plaq} (mapP : Z4Plaq → Z4Plaq)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map mapP) (right.map mapP) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.2 source hsource, rfl⟩

private theorem sameSupport_right_eq_local
    {left right target : List Z4Plaq}
    (hsupport : sameSupport (L := z4Chain.toLattice) left right)
    (heq : right = target) :
    sameSupport (L := z4Chain.toLattice) left target := by
  cases heq
  exact hsupport

/-! ## 1. The four stage boxes and their canonical roots -/

def signedSpatialSourceStageBase (base stage : Nat) : Nat :=
  centeredBoxBase (base + stage)

def signedSpatialTargetBase (base shift : Nat) : Nat :=
  uniformPaddedBase shift base

def signedSpatialTargetStageBase
    (base shift stage : Nat) : Nat :=
  centeredBoxBase (signedSpatialTargetBase base shift + stage)

def signedSpatialTimeStageBase
    (base shift stage : Nat) : Nat :=
  signedSpatialTargetStageBase base shift stage + shift

def signedSpatialCommonStageBase
    (base shift stage : Nat) : Nat :=
  uniformPaddedBase (shift + shift + shift)
    (signedSpatialSourceStageBase base stage)

theorem signedSpatialTimeStageBase_le_common
    (base shift stage : Nat) :
    signedSpatialTimeStageBase base shift stage ≤
      signedSpatialCommonStageBase base shift stage := by
  unfold signedSpatialTimeStageBase signedSpatialTargetStageBase
    signedSpatialTargetBase signedSpatialCommonStageBase
    signedSpatialSourceStageBase uniformPaddedBase centeredBoxBase
  omega

def signedSpatialSourceStageRoot
    (base stage : Nat) (root : List Nat) : List Nat :=
  centeredOffsetCanonicalRoot (base + stage) base root

def signedSpatialTargetStageRoot
    (base shift stage : Nat) (root : List Nat) : List Nat :=
  centeredOffsetCanonicalRoot
    (signedSpatialTargetBase base shift + stage)
    (signedSpatialTargetBase base shift)
    (spatialShiftCanonicalRoot shift base root)

def signedSpatialTimeStageRoot
    (base shift stage : Nat) (root : List Nat) : List Nat :=
  timeShiftCanonicalRoot shift
    (signedSpatialTargetStageBase base shift stage)
    (signedSpatialTargetStageRoot base shift stage root)

def signedSpatialCommonUniformRoot
    (base shift stage : Nat) (root : List Nat) : List Nat :=
  uniformShiftCanonicalRoot (shift + shift + shift)
    (signedSpatialSourceStageBase base stage)
    (signedSpatialSourceStageRoot base stage root)

/-! ## 2. Exact plaquette and root alignment -/

/-- Coordinate identity underlying the route:
`time(s) ∘ uniform(base+2s+stage) ∘ spatial(s)` equals
`uniform(3s) ∘ uniform(base+stage)`. -/
theorem time_uniform_spatial_eq_tripleUniform
    (base shift stage : Nat) (plaquette : Z4Plaq) :
    timeShiftPlaquette shift
        (uniformShiftPlaquette
          (signedSpatialTargetBase base shift + stage)
          (spatialShiftPlaquette shift plaquette)) =
      uniformShiftPlaquette (shift + shift + shift)
        (uniformShiftPlaquette (base + stage) plaquette) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp [timeShiftPlaquette, timeShiftVertex,
      uniformShiftPlaquette, uniformShiftVertex,
      spatialShiftPlaquette, spatialShiftVertex,
      signedSpatialTargetBase, uniformPaddedBase,
      Nat.add_comm, Nat.add_left_comm]

/-- After the one necessary zero-extension, the time-shifted strict target
root and the triple-uniformly shifted source root are literally the same
canonical root. -/
theorem signedSpatialTimeRoot_transport_eq_commonUniform
    {base shift stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    transportPolymer
        (signedSpatialTimeStageBase base shift stage)
        (signedSpatialCommonStageBase base shift stage)
        (signedSpatialTimeStageRoot base shift stage root) =
      signedSpatialCommonUniformRoot base shift stage root := by
  have hspatial := spatialShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetStage := centeredOffsetCanonicalRoot_canonical
    (Nat.le_add_right (signedSpatialTargetBase base shift) stage)
    hspatial
  have htime := timeShiftCanonicalRoot_canonical
    (shift := shift) htargetStage
  have hsourceStage := centeredOffsetCanonicalRoot_canonical
    (Nat.le_add_right base stage) hroot
  have huniform := uniformShiftCanonicalRoot_canonical
    (padding := shift + shift + shift) hsourceStage
  have hle := signedSpatialTimeStageBase_le_common
    base shift stage
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    (transportPolymer_mem_canonicalSurfacePolymers hle htime)
    huniform
  have hspatialSupport := spatialShiftCanonicalRoot_sameSupport
    (shift := shift) hroot
  have htargetStageSupport := centeredOffsetCanonicalRoot_sameSupport
    (Nat.le_add_right (signedSpatialTargetBase base shift) stage)
    hspatial
  have htargetNested := sameSupport_trans htargetStageSupport
    (sameSupport_map_local
      (uniformShiftPlaquette
        (signedSpatialTargetBase base shift + stage))
      hspatialSupport)
  have htimeSupport := timeShiftCanonicalRoot_sameSupport
    (shift := shift) htargetStage
  have htimeNested := sameSupport_trans htimeSupport
    (sameSupport_map_local (timeShiftPlaquette shift) htargetNested)
  have htransport := transportPolymer_sameSupport hle
    (canonicalSurfacePolymer_mem_faceSupports htime)
  have hleft := sameSupport_trans (sameSupport_symm htransport)
    htimeNested
  have hsourceStageSupport := centeredOffsetCanonicalRoot_sameSupport
    (Nat.le_add_right base stage) hroot
  have huniformSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := shift + shift + shift) hsourceStage
  have hrightNested := sameSupport_trans huniformSupport
    (sameSupport_map_local
      (uniformShiftPlaquette (shift + shift + shift))
      hsourceStageSupport)
  have hmap :
      (((geometricPolymer base root).map
          (spatialShiftPlaquette shift)).map
          (uniformShiftPlaquette
            (signedSpatialTargetBase base shift + stage))).map
          (timeShiftPlaquette shift) =
        ((geometricPolymer base root).map
          (uniformShiftPlaquette (base + stage))).map
          (uniformShiftPlaquette (shift + shift + shift)) := by
    rw [List.map_map, List.map_map, List.map_map]
    apply List.map_congr_left
    intro plaquette _
    simp only [Function.comp_apply]
    exact time_uniform_spatial_eq_tripleUniform
      base shift stage plaquette
  exact sameSupport_trans
    (sameSupport_right_eq_local hleft hmap)
    (sameSupport_symm hrightNested)

/-! ## 3. Lists, Boolean events, and finite laws -/

def signedSpatialSourceStageRoots
    (base stage : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (signedSpatialSourceStageRoot base stage)

def signedSpatialTimeStageRoots
    (base shift stage : Nat) (roots : List (List Nat)) :
    List (List Nat) :=
  roots.map (signedSpatialTimeStageRoot base shift stage)

def signedSpatialCommonUniformRoots
    (base shift stage : Nat) (roots : List (List Nat)) :
    List (List Nat) :=
  roots.map (signedSpatialCommonUniformRoot base shift stage)

theorem signedSpatialTimeRoots_transport_eq_commonUniform
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    transportedCylinderRoots
        (signedSpatialTimeStageBase base shift stage)
        (signedSpatialCommonStageBase base shift stage)
        (signedSpatialTimeStageRoots base shift stage roots) =
      signedSpatialCommonUniformRoots base shift stage roots := by
  unfold transportedCylinderRoots signedSpatialTimeStageRoots
    signedSpatialCommonUniformRoots
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  exact signedSpatialTimeRoot_transport_eq_commonUniform
    (hroots root hroot)

theorem signedSpatialTimeCylinderEvent_transport_eq_commonUniform
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    targetCylinderEvent
        (signedSpatialTimeStageBase base shift stage)
        (signedSpatialCommonStageBase base shift stage)
        (signedSpatialTimeStageRoots base shift stage roots)
        predicate =
      cylinderEvent
        (signedSpatialCommonUniformRoots base shift stage roots)
        predicate := by
  unfold targetCylinderEvent
  rw [signedSpatialTimeRoots_transport_eq_commonUniform hroots]

theorem couplingParametricK_signedSpatial_commonFiniteLaw_eq
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat)
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff
        (signedSpatialCommonStageBase base shift stage)
        (targetCylinderEvent
          (signedSpatialTimeStageBase base shift stage)
          (signedSpatialCommonStageBase base shift stage)
          (signedSpatialTimeStageRoots base shift stage roots)
          predicate) =
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff
        (signedSpatialCommonStageBase base shift stage)
        (cylinderEvent
          (signedSpatialCommonUniformRoots base shift stage roots)
          predicate) := by
  rw [signedSpatialTimeCylinderEvent_transport_eq_commonUniform
    hroots predicate]

#print axioms signedSpatialTimeStageBase_le_common
#print axioms time_uniform_spatial_eq_tripleUniform
#print axioms signedSpatialTimeRoot_transport_eq_commonUniform
#print axioms signedSpatialTimeRoots_transport_eq_commonUniform
#print axioms signedSpatialTimeCylinderEvent_transport_eq_commonUniform
#print axioms couplingParametricK_signedSpatial_commonFiniteLaw_eq

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialLaw
