/-
# Doubled-time mixed geometry of the translated strict reflection diagonal

After translating a strict cylinder by `shift` and increasing the reflection
radius by the same amount, the reflected lower root is transported only in
the three spatial coordinates.  The unreflected upper root has a different
transport: the same spatial shift together with a Euclidean-time shift by
`2 * shift`.  Thus the translated diagonal has the geometry of a mixed
Osterwalder--Schrader matrix coefficient at doubled time separation.

This file proves that support identity exactly and also fences the tempting
but false whole-event spatial-covariance identification.  It does not assert
covariance of a finite-volume law, equality of probabilities, or a transfer
contraction.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationScheduleAlignment

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

private theorem sameSupport_map_local
    {left right : List Z4Plaq} (reindex : Z4Plaq → Z4Plaq)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map reindex) (right.map reindex) := by
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

/-! ## 1. Canonical re-encoding of a pure spatial translate -/

/-- Re-encode a three-coordinate translate in the same padded box used by a
uniform four-coordinate translate.  Only the ambient box is padded in time;
the geometric support is not moved in time. -/
def spatialShiftCanonicalRoot
    (shift base : Nat) (root : List Nat) : List Nat :=
  geometricSupportIds (uniformPaddedBase shift base)
    ((geometricPolymer base root).map
      (spatialShiftPlaquette shift))

def spatialShiftChain (shift : Nat) {support : List Z4Plaq} :
    {first last : Z4Plaq} →
      ChainIn z4Chain.toLattice support first last →
      ChainIn z4Chain.toLattice
        (support.map (spatialShiftPlaquette shift))
        (spatialShiftPlaquette shift first)
        (spatialShiftPlaquette shift last)
  | _, _, .refl plaquette => .refl _
  | _, _, .step adjacent hnext rest =>
      .step (spatialShiftAdjacent shift adjacent)
        (List.mem_map.mpr ⟨_, hnext, rfl⟩)
        (spatialShiftChain shift rest)

def spatialShiftConnected (shift : Nat) {support : List Z4Plaq}
    (hconnected : connectedIn (L := z4Chain.toLattice) support) :
    connectedIn (L := z4Chain.toLattice)
      (support.map (spatialShiftPlaquette shift)) := by
  intro first last hfirst hlast
  obtain ⟨sourceFirst, hsourceFirst, hfirstEq⟩ :=
    decodeMapMember (spatialShiftPlaquette shift) support first hfirst
  obtain ⟨sourceLast, hsourceLast, hlastEq⟩ :=
    decodeMapMember (spatialShiftPlaquette shift) support last hlast
  rw [← hfirstEq, ← hlastEq]
  exact spatialShiftChain shift
    (hconnected sourceFirst sourceLast hsourceFirst hsourceLast)

theorem spatialShiftCanonicalRoot_sameSupport
    {shift base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (uniformPaddedBase shift base)
        (spatialShiftCanonicalRoot shift base root))
      ((geometricPolymer base root).map
        (spatialShiftPlaquette shift)) := by
  unfold spatialShiftCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  exact spatialShiftPlaquette_mem_padded_box
    (geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)

def spatialShiftCanonicalRoot_nonempty
    {shift base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    Σ' face : Nat, face ∈ spatialShiftCanonicalRoot shift base root := by
  obtain ⟨sourceFace, hsourceFace⟩ :=
    canonicalSurfacePolymers_allNonempty base root hroot
  have hsource : boxPlaquetteAt base sourceFace ∈
      geometricPolymer base root :=
    List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
  have hshifted :
      spatialShiftPlaquette shift (boxPlaquetteAt base sourceFace) ∈
        (geometricPolymer base root).map
          (spatialShiftPlaquette shift) :=
    List.mem_map.mpr ⟨boxPlaquetteAt base sourceFace, hsource, rfl⟩
  have hencoded :=
    (spatialShiftCanonicalRoot_sameSupport hroot).2 _ hshifted
  obtain ⟨targetFace, htargetFace, _⟩ :=
    decodeMapMember
      (boxPlaquetteAt (uniformPaddedBase shift base))
      (spatialShiftCanonicalRoot shift base root)
      (spatialShiftPlaquette shift (boxPlaquetteAt base sourceFace))
      hencoded
  exact ⟨targetFace, htargetFace⟩

def spatialShiftCanonicalRoot_connected
    {shift base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    InternallyConnected
      (faceLinkAdjacentB (uniformPaddedBase shift base))
      (spatialShiftCanonicalRoot shift base root) := by
  unfold spatialShiftCanonicalRoot
  apply geometricSupportIds_connected
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact spatialShiftPlaquette_mem_padded_box
      (geometricPolymer_subset_box
        (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)
  · exact spatialShiftConnected shift
      (numericalConnectedToGeometric
        ((canonicalSurfacePolymers_allConnected base) root hroot))

theorem spatialShiftCanonicalRoot_canonical
    {shift base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    spatialShiftCanonicalRoot shift base root ∈
      canonicalSurfacePolymers (uniformPaddedBase shift base) :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (geometricSupportIds_mem_cutoffOneFaceSupports
      (uniformPaddedBase shift base)
      ((geometricPolymer base root).map
        (spatialShiftPlaquette shift)))
    (spatialShiftCanonicalRoot_nonempty hroot)
    (spatialShiftCanonicalRoot_connected hroot)

/-- Canonical box transport commutes with the pure spatial re-encoding. -/
theorem spatialShiftCanonicalRoot_transport
    {base middle shift : Nat} (hbase : base ≤ middle)
    {root : List Nat} (hroot : root ∈ canonicalSurfacePolymers base) :
    transportPolymer
        (uniformPaddedBase shift base)
        (uniformPaddedBase shift middle)
        (spatialShiftCanonicalRoot shift base root) =
      spatialShiftCanonicalRoot shift middle
        (transportPolymer base middle root) := by
  have hshiftBase := spatialShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htransported := transportPolymer_mem_canonicalSurfacePolymers
    hbase hroot
  have hpadded : uniformPaddedBase shift base ≤
      uniformPaddedBase shift middle := by
    unfold uniformPaddedBase
    omega
  have hleftCanonical := transportPolymer_mem_canonicalSurfacePolymers
    hpadded hshiftBase
  have hrightCanonical := spatialShiftCanonicalRoot_canonical
    (shift := shift) htransported
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    hleftCanonical hrightCanonical
  have hshiftBaseSupport := spatialShiftCanonicalRoot_sameSupport
    (shift := shift) hroot
  have htransportSupport := transportPolymer_sameSupport hbase
    (canonicalSurfacePolymer_mem_faceSupports hroot)
  have hshiftTransportSupport := transportPolymer_sameSupport hpadded
    (canonicalSurfacePolymer_mem_faceSupports hshiftBase)
  have hmiddleShiftSupport := spatialShiftCanonicalRoot_sameSupport
    (shift := shift) htransported
  exact sameSupport_trans (sameSupport_symm hshiftTransportSupport)
    (sameSupport_trans hshiftBaseSupport
      (sameSupport_trans
        (sameSupport_map_local (spatialShiftPlaquette shift)
          htransportSupport)
        (sameSupport_symm hmiddleShiftSupport)))

/-! ## 2. The two transports in the mixed OS pair -/

/-- The literal translate-then-embed map underlying an unreflected strict
upper root at radius `radius`. -/
def strictJointRawUpperQueryPlaquette
    (radius : Nat) (plaquette : Z4Plaq) : Z4Plaq :=
  uniformShiftPlaquette radius (uniformShiftPlaquette 3 plaquette)

/-- The upper member of the translated reflection diagonal: a common spatial
shift and twice the Euclidean-time shift. -/
def strictJointDoubledTimeUpperTransport
    (shift : Nat) (plaquette : Z4Plaq) : Z4Plaq :=
  timeShiftPlaquette (shift + shift)
    (spatialShiftPlaquette shift plaquette)

/-- Exact plaquette-level doubled-time identity. -/
theorem strictJointRawUpperQueryPlaquette_timeShift_doubled
    (radius shift : Nat) (plaquette : Z4Plaq) :
    strictJointRawUpperQueryPlaquette (radius + shift)
        (timeShiftPlaquette shift plaquette) =
      strictJointDoubledTimeUpperTransport shift
        (strictJointRawUpperQueryPlaquette radius plaquette) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp [strictJointRawUpperQueryPlaquette,
      strictJointDoubledTimeUpperTransport,
      uniformShiftPlaquette, uniformShiftVertex,
      spatialShiftPlaquette, spatialShiftVertex,
      timeShiftPlaquette, timeShiftVertex,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-! ## 3. Exact support identity for the upper root -/

theorem centralStrictUpperCanonicalRoot_raw_sameSupport_local
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient radius)
        (centralStrictUpperCanonicalRoot radius base root))
      ((geometricPolymer base root).map
        (strictJointRawUpperQueryPlaquette radius)) := by
  have hsource := uniformShiftCanonicalRoot_sameSupport
    (padding := 3) hroot
  have hupper := centralFaceQueryCanonicalRoot_sameSupport hbase
    (strictQuerySourceRoot_canonical hroot)
  have hmapped := sameSupport_map_local
    (uniformShiftPlaquette radius) hsource
  have hcombined := sameSupport_trans hupper hmapped
  apply sameSupport_right_eq_local hcombined
  calc
    ((geometricPolymer base root).map
        (uniformShiftPlaquette 3)).map
        (uniformShiftPlaquette radius) =
      (geometricPolymer base root).map
        ((uniformShiftPlaquette radius) ∘
          (uniformShiftPlaquette 3)) := List.map_map
    _ = (geometricPolymer base root).map
        (strictJointRawUpperQueryPlaquette radius) := by
      apply List.map_congr_left
      intro plaquette hplaquette
      rfl

/-- The target unreflected upper root is the source upper root transported by
the mixed spatial-plus-doubled-time map.  Together with
`centralStrictLowerCanonicalRoot_timeShift_sameSupport`, this is the exact
geometry of the translated OS diagonal. -/
theorem timeTranslatedStrictJointUpperRoot_has_doubledTime_transport
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient (radius + shift))
        (centralStrictUpperCanonicalRoot (radius + shift) (base + shift)
          (timeShiftCanonicalRoot shift base root)))
      ((geometricPolymer (centralAmbient radius)
          (centralStrictUpperCanonicalRoot radius base root)).map
        (strictJointDoubledTimeUpperTransport shift)) := by
  have htargetBase : strictQueryBase (base + shift) ≤ radius + shift := by
    unfold strictQueryBase uniformPaddedBase at hbase ⊢
    omega
  have htranslatedCanonical := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetRaw :=
    centralStrictUpperCanonicalRoot_raw_sameSupport_local
      htargetBase htranslatedCanonical
  have htime := timeShiftCanonicalRoot_sameSupport
    (shift := shift) hroot
  have htimeMapped := sameSupport_map_local
    (strictJointRawUpperQueryPlaquette (radius + shift)) htime
  have htargetOriginal := sameSupport_trans htargetRaw htimeMapped
  have hsourceRaw :=
    centralStrictUpperCanonicalRoot_raw_sameSupport_local hbase hroot
  have hsourceMapped := sameSupport_map_local
    (strictJointDoubledTimeUpperTransport shift) hsourceRaw
  have hnested :
      ((geometricPolymer base root).map
          (timeShiftPlaquette shift)).map
          (strictJointRawUpperQueryPlaquette (radius + shift)) =
        ((geometricPolymer base root).map
          (strictJointRawUpperQueryPlaquette radius)).map
          (strictJointDoubledTimeUpperTransport shift) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro plaquette hplaquette
    simp only [Function.comp_apply]
    exact strictJointRawUpperQueryPlaquette_timeShift_doubled
      radius shift plaquette
  have htargetCommon := sameSupport_right_eq_local
    htargetOriginal hnested
  exact sameSupport_trans htargetCommon (sameSupport_symm hsourceMapped)

/-! ## 4. Machine fence around the false pure-spatial identification -/

/-- For every nonzero shift, the upper mixed transport is not the pure
spatial transport carried by the reflected lower root. -/
theorem strictJointDoubledTimeUpperTransport_ne_spatialShift
    {shift : Nat} (hshift : 0 < shift) (plaquette : Z4Plaq) :
    strictJointDoubledTimeUpperTransport shift plaquette ≠
      spatialShiftPlaquette shift plaquette := by
  intro hequal
  have htime := congrArg
    (fun target : Z4Plaq => target.1.2.2.2) hequal
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp only [strictJointDoubledTimeUpperTransport,
    spatialShiftPlaquette, spatialShiftVertex,
    timeShiftPlaquette, timeShiftVertex] at htime
  omega

#print axioms strictJointRawUpperQueryPlaquette_timeShift_doubled
#print axioms spatialShiftCanonicalRoot_canonical
#print axioms spatialShiftCanonicalRoot_transport
#print axioms centralStrictUpperCanonicalRoot_raw_sameSupport_local
#print axioms timeTranslatedStrictJointUpperRoot_has_doubledTime_transport
#print axioms strictJointDoubledTimeUpperTransport_ne_spatialShift

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
