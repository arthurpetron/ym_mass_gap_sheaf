/-
# Canonical one-step query geometry in the adjacent-even slab

The one-step reflection identity lives in the even slab of extent `2r+2`.
The strict roots already constructed at radius `r` use the ambient box of
size `2r+2`, so their numerical identifiers cannot be reused as identifiers
for the boundary-complete even slab: that slab uses the one-level larger
ambient box `2r+3`.  This leaf transports both roots into that common ambient
box, proves the complete one-link query geometry, and then re-encodes the
literal geometric reflection canonically.

The ambient reflection identifier below is intentionally distinct from
`slabFaceReflectId`.  The two identifiers index different finite lists.
-/

import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
import YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOneStepParityFence
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepQueryGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOneStepParityFence
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

/-! ## 1. The common adjacent-even ambient box -/

/-- Ambient cutoff containing every face of the boundary-complete adjacent
even slab.  This is one larger than the old strict-root ambient cutoff. -/
def adjacentEvenAmbient (radius : Nat) : Nat :=
  adjacentEvenExtent radius + 1

theorem adjacentEvenExtent_eq_centralAmbient (radius : Nat) :
    adjacentEvenExtent radius = centralAmbient radius := by
  rfl

theorem adjacentEvenExtent_eq_oneStepReflectionExtent (radius : Nat) :
    adjacentEvenExtent radius = oneStepReflectionExtent radius := by
  rfl

theorem centralAmbient_le_adjacentEvenAmbient (radius : Nat) :
    centralAmbient radius ≤ adjacentEvenAmbient radius := by
  unfold adjacentEvenAmbient adjacentEvenExtent centralAmbient
  omega

private theorem strictQueryBase_le_of_succ_fit
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius) :
    strictQueryBase base ≤ radius := by
  unfold strictQueryBase uniformPaddedBase at hfit ⊢
  omega

private theorem adjacentEvenPlaquetteSide_eq_lower_of_time_lt
    {radius : Nat} {plaquette : Z4Plaq}
    (htime : plaquette.1.2.2.2 < adjacentEvenCenter radius) :
    adjacentEvenPlaquetteSide radius plaquette = .lower := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp [adjacentEvenPlaquetteSide, adjacentEvenSpatialSide,
      adjacentEvenTemporalSide, htime]

private theorem adjacentEvenPlaquetteSide_eq_upper_of_center_lt
    {radius : Nat} {plaquette : Z4Plaq}
    (htime : adjacentEvenCenter radius < plaquette.1.2.2.2) :
    adjacentEvenPlaquetteSide radius plaquette = .upper := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  have hnotLower : ¬ d < adjacentEvenCenter radius :=
    Nat.not_lt.mpr (Nat.le_of_lt htime)
  have hnotFixed : d ≠ adjacentEvenCenter radius := Nat.ne_of_gt htime
  cases plane <;>
    simp [adjacentEvenPlaquetteSide, adjacentEvenSpatialSide,
      adjacentEvenTemporalSide, hnotLower, hnotFixed]

/-- Any ambient physical face whose base time is strictly below the even
extent belongs to the boundary-complete even slab. -/
theorem adjacentEvenAmbientFace_mem_slab_of_time_lt
    {radius face : Nat}
    (hface : face ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (htime :
      (boxPlaquetteAt (adjacentEvenAmbient radius) face).1.2.2.2 <
        adjacentEvenExtent radius) :
    boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
  apply (mem_boundaryCompleteSlabPlaquettes _ _).2
  constructor
  · simpa only [adjacentEvenAmbient] using
      (boxPlaquetteAt_mem_boxPlaquettes_of_physical hface)
  · generalize hplaquette :
      boxPlaquetteAt (adjacentEvenAmbient radius) face = plaquette
        at htime ⊢
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
    cases plane <;>
      simp [plaquetteTimeAdmissible] at htime ⊢ <;>
      omega

/-! ## 2. Transported lower and one-step upper roots -/

/-- The old strict lower root, canonically re-encoded in the ambient box of
the adjacent-even slab. -/
def adjacentEvenStrictLowerCanonicalRoot
    (radius base : Nat) (root : List Nat) : List Nat :=
  transportPolymer (centralAmbient radius) (adjacentEvenAmbient radius)
    (centralStrictLowerCanonicalRoot radius base root)

/-- The strict upper root of the one-step translated source, canonically
re-encoded in the same adjacent-even ambient box as the lower root. -/
def adjacentEvenStrictUpperCanonicalRoot
    (radius base : Nat) (root : List Nat) : List Nat :=
  transportPolymer (centralAmbient radius) (adjacentEvenAmbient radius)
    (centralStrictUpperCanonicalRoot radius (base + 1)
      (timeShiftCanonicalRoot 1 base root))

theorem adjacentEvenStrictLowerCanonicalRoot_canonical
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    adjacentEvenStrictLowerCanonicalRoot radius base root ∈
      canonicalSurfacePolymers (adjacentEvenAmbient radius) := by
  apply transportPolymer_mem_canonicalSurfacePolymers
    (centralAmbient_le_adjacentEvenAmbient radius)
  exact centralStrictLowerCanonicalRoot_canonical
    (strictQueryBase_le_of_succ_fit hfit) hroot

theorem adjacentEvenStrictUpperCanonicalRoot_canonical
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    adjacentEvenStrictUpperCanonicalRoot radius base root ∈
      canonicalSurfacePolymers (adjacentEvenAmbient radius) := by
  apply transportPolymer_mem_canonicalSurfacePolymers
    (centralAmbient_le_adjacentEvenAmbient radius)
  exact centralStrictUpperCanonicalRoot_canonical hfit
    (timeShiftCanonicalRoot_canonical (shift := 1) hroot)

theorem adjacentEvenStrictLowerCanonicalRoot_sameSupport
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient radius)
        (centralStrictLowerCanonicalRoot radius base root))
      (geometricPolymer (adjacentEvenAmbient radius)
        (adjacentEvenStrictLowerCanonicalRoot radius base root)) := by
  exact transportPolymer_sameSupport
    (centralAmbient_le_adjacentEvenAmbient radius)
    (canonicalSurfacePolymer_mem_faceSupports
      (centralStrictLowerCanonicalRoot_canonical
        (strictQueryBase_le_of_succ_fit hfit) hroot))

theorem adjacentEvenStrictUpperCanonicalRoot_sameSupport
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient radius)
        (centralStrictUpperCanonicalRoot radius (base + 1)
          (timeShiftCanonicalRoot 1 base root)))
      (geometricPolymer (adjacentEvenAmbient radius)
        (adjacentEvenStrictUpperCanonicalRoot radius base root)) := by
  exact transportPolymer_sameSupport
    (centralAmbient_le_adjacentEvenAmbient radius)
    (canonicalSurfacePolymer_mem_faceSupports
      (centralStrictUpperCanonicalRoot_canonical hfit
        (timeShiftCanonicalRoot_canonical (shift := 1) hroot)))

/-! ## 3. Internal time, slab-support, and side estimates -/

theorem adjacentEvenStrictLowerCanonicalRoot_time_add_two_le
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ adjacentEvenStrictLowerCanonicalRoot radius base root) :
    (boxPlaquetteAt (adjacentEvenAmbient radius) face).1.2.2.2 + 2 ≤
      radius := by
  have hsourceCanonical := centralStrictLowerCanonicalRoot_canonical
    (strictQueryBase_le_of_succ_fit hfit) hroot
  obtain ⟨sourceFace, hsourceFace, hcoordinate⟩ :=
    transportPolymerMemberSource
      (centralAmbient_le_adjacentEvenAmbient radius)
      (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical) hface
  have htime := centralStrictLowerCanonicalRoot_time_add_two_le
    (strictQueryBase_le_of_succ_fit hfit) hroot hsourceFace
  rw [hcoordinate] at htime
  exact htime

theorem adjacentEvenStrictUpperCanonicalRoot_time_ge
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ adjacentEvenStrictUpperCanonicalRoot radius base root) :
    radius + 3 ≤
      (boxPlaquetteAt (adjacentEvenAmbient radius) face).1.2.2.2 := by
  have hshifted := timeShiftCanonicalRoot_canonical (shift := 1) hroot
  have hsourceCanonical :=
    centralStrictUpperCanonicalRoot_canonical hfit hshifted
  obtain ⟨sourceFace, hsourceFace, hcoordinate⟩ :=
    transportPolymerMemberSource
      (centralAmbient_le_adjacentEvenAmbient radius)
      (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical) hface
  have htime := centralStrictUpperCanonicalRoot_time_ge
    hfit hshifted hsourceFace
  rw [hcoordinate] at htime
  exact htime

/-- The upper source also retains its strict old-ambient bound.  This spare
upper margin is what keeps the complete exterior shell inside the even slab. -/
theorem adjacentEvenStrictUpperCanonicalRoot_time_lt
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ adjacentEvenStrictUpperCanonicalRoot radius base root) :
    (boxPlaquetteAt (adjacentEvenAmbient radius) face).1.2.2.2 <
      radius + strictQueryBase (base + 1) := by
  have hshifted := timeShiftCanonicalRoot_canonical (shift := 1) hroot
  have hsourceCanonical :=
    centralStrictUpperCanonicalRoot_canonical hfit hshifted
  obtain ⟨sourceFace, hsourceFace, hcoordinate⟩ :=
    transportPolymerMemberSource
      (centralAmbient_le_adjacentEvenAmbient radius)
      (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical) hface
  have htime := centralFaceQueryCanonicalRoot_time_lt hfit
    (strictQuerySourceRoot_canonical hshifted) hsourceFace
  rw [hcoordinate] at htime
  exact htime

theorem adjacentEvenStrictLowerCanonicalRoot_face_mem_slab
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ adjacentEvenStrictLowerCanonicalRoot radius base root) :
    boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
  have hcanonical := adjacentEvenStrictLowerCanonicalRoot_canonical
    hfit hroot
  have hphysical := mem_of_mem_sublists
    (physicalFaceEdges (adjacentEvenAmbient radius))
    (adjacentEvenStrictLowerCanonicalRoot radius base root)
    (canonicalSurfacePolymer_mem_faceSupports hcanonical) face hface
  apply adjacentEvenAmbientFace_mem_slab_of_time_lt hphysical
  have htime := adjacentEvenStrictLowerCanonicalRoot_time_add_two_le
    hfit hroot hface
  unfold adjacentEvenExtent centralExtent
  omega

theorem adjacentEvenStrictUpperCanonicalRoot_face_mem_slab
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ adjacentEvenStrictUpperCanonicalRoot radius base root) :
    boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
  have hcanonical := adjacentEvenStrictUpperCanonicalRoot_canonical
    hfit hroot
  have hphysical := mem_of_mem_sublists
    (physicalFaceEdges (adjacentEvenAmbient radius))
    (adjacentEvenStrictUpperCanonicalRoot radius base root)
    (canonicalSurfacePolymer_mem_faceSupports hcanonical) face hface
  apply adjacentEvenAmbientFace_mem_slab_of_time_lt hphysical
  have htime := adjacentEvenStrictUpperCanonicalRoot_time_lt
    hfit hroot hface
  unfold adjacentEvenExtent centralExtent at ⊢
  unfold strictQueryBase uniformPaddedBase at hfit htime
  omega

theorem adjacentEvenStrictLowerCanonicalRoot_supported
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    canonicalPolymerSlabSupportedB (adjacentEvenExtent radius)
      (adjacentEvenStrictLowerCanonicalRoot radius base root) = true := by
  unfold canonicalPolymerSlabSupportedB
  apply List.all_eq_true.mpr
  intro face hface
  apply decide_eq_true
  simpa only [adjacentEvenAmbient] using
    (adjacentEvenStrictLowerCanonicalRoot_face_mem_slab
      hfit hroot hface)

theorem adjacentEvenStrictUpperCanonicalRoot_supported
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    canonicalPolymerSlabSupportedB (adjacentEvenExtent radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root) = true := by
  unfold canonicalPolymerSlabSupportedB
  apply List.all_eq_true.mpr
  intro face hface
  apply decide_eq_true
  simpa only [adjacentEvenAmbient] using
    (adjacentEvenStrictUpperCanonicalRoot_face_mem_slab
      hfit hroot hface)

theorem adjacentEvenStrictLowerCanonicalRoot_side
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ adjacentEvenStrictLowerCanonicalRoot radius base root) :
    adjacentEvenPlaquetteSide radius
      (boxPlaquetteAt (adjacentEvenAmbient radius) face) = .lower := by
  apply adjacentEvenPlaquetteSide_eq_lower_of_time_lt
  have htime := adjacentEvenStrictLowerCanonicalRoot_time_add_two_le
    hfit hroot hface
  unfold adjacentEvenCenter
  omega

theorem adjacentEvenStrictUpperCanonicalRoot_side
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ adjacentEvenStrictUpperCanonicalRoot radius base root) :
    adjacentEvenPlaquetteSide radius
      (boxPlaquetteAt (adjacentEvenAmbient radius) face) = .upper := by
  apply adjacentEvenPlaquetteSide_eq_upper_of_center_lt
  have htime := adjacentEvenStrictUpperCanonicalRoot_time_ge
    hfit hroot hface
  unfold adjacentEvenCenter
  omega

/-! ## 4. Complete one-link exterior shells -/

theorem adjacentEvenStrictLowerCanonicalRoot_exterior_time_add_one_le
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictLowerCanonicalRoot radius base root)) :
    (boxPlaquetteAt (adjacentEvenAmbient radius) face).1.2.2.2 + 1 ≤
      radius := by
  obtain ⟨_hphysical, _houtside, inside, hinside, hadj⟩ :=
    (mem_canonicalPolymerExteriorFaceQueries_iff
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictLowerCanonicalRoot radius base root) face).1 hface
  have hinsideTime :=
    adjacentEvenStrictLowerCanonicalRoot_time_add_two_le
      hfit hroot hinside
  have hforward := actualAdjacentOfFaceLinkAdjacent hadj
  have hreverse : z4Chain.toLattice.Adjacent
      (boxPlaquetteAt (adjacentEvenAmbient radius) face)
      (boxPlaquetteAt (adjacentEvenAmbient radius) inside) := {
    link := hforward.link
    on_p := hforward.on_q
    on_q := hforward.on_p
  }
  have htimeStep := adjacent_time_le_add_one hreverse
  omega

theorem adjacentEvenStrictUpperCanonicalRoot_exterior_time_ge
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root)) :
    radius + 2 ≤
      (boxPlaquetteAt (adjacentEvenAmbient radius) face).1.2.2.2 := by
  obtain ⟨_hphysical, _houtside, inside, hinside, hadj⟩ :=
    (mem_canonicalPolymerExteriorFaceQueries_iff
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root) face).1 hface
  have hinsideTime := adjacentEvenStrictUpperCanonicalRoot_time_ge
    hfit hroot hinside
  have htimeStep := adjacent_time_le_add_one
    (actualAdjacentOfFaceLinkAdjacent hadj)
  omega

/-- The upper exterior shell stays strictly below the maximum even-slab
vertex time.  This is the ambient bound needed for temporal exterior faces. -/
theorem adjacentEvenStrictUpperCanonicalRoot_exterior_time_lt_extent
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root)) :
    (boxPlaquetteAt (adjacentEvenAmbient radius) face).1.2.2.2 <
      adjacentEvenExtent radius := by
  obtain ⟨_hphysical, _houtside, inside, hinside, hadj⟩ :=
    (mem_canonicalPolymerExteriorFaceQueries_iff
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root) face).1 hface
  have hinsideTime := adjacentEvenStrictUpperCanonicalRoot_time_lt
    hfit hroot hinside
  have hforward := actualAdjacentOfFaceLinkAdjacent hadj
  have hreverse : z4Chain.toLattice.Adjacent
      (boxPlaquetteAt (adjacentEvenAmbient radius) face)
      (boxPlaquetteAt (adjacentEvenAmbient radius) inside) := {
    link := hforward.link
    on_p := hforward.on_q
    on_q := hforward.on_p
  }
  have htimeStep := adjacent_time_le_add_one hreverse
  unfold adjacentEvenExtent centralExtent at ⊢
  unfold strictQueryBase uniformPaddedBase at hfit hinsideTime
  omega

theorem adjacentEvenStrictLowerCanonicalRoot_exterior_mem_slab
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictLowerCanonicalRoot radius base root)) :
    boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
  have hphysical :=
    (mem_canonicalPolymerExteriorFaceQueries_iff
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictLowerCanonicalRoot radius base root) face).1 hface |>.1
  apply adjacentEvenAmbientFace_mem_slab_of_time_lt hphysical
  have htime :=
    adjacentEvenStrictLowerCanonicalRoot_exterior_time_add_one_le
      hfit hroot hface
  unfold adjacentEvenExtent centralExtent
  omega

theorem adjacentEvenStrictUpperCanonicalRoot_exterior_mem_slab
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root)) :
    boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
  have hphysical :=
    (mem_canonicalPolymerExteriorFaceQueries_iff
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root) face).1 hface |>.1
  exact adjacentEvenAmbientFace_mem_slab_of_time_lt hphysical
    (adjacentEvenStrictUpperCanonicalRoot_exterior_time_lt_extent
      hfit hroot hface)

theorem adjacentEvenStrictLowerCanonicalRoot_exterior_side
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictLowerCanonicalRoot radius base root)) :
    adjacentEvenPlaquetteSide radius
      (boxPlaquetteAt (adjacentEvenAmbient radius) face) = .lower := by
  apply adjacentEvenPlaquetteSide_eq_lower_of_time_lt
  have htime :=
    adjacentEvenStrictLowerCanonicalRoot_exterior_time_add_one_le
      hfit hroot hface
  unfold adjacentEvenCenter
  omega

theorem adjacentEvenStrictUpperCanonicalRoot_exterior_side
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root)) :
    adjacentEvenPlaquetteSide radius
      (boxPlaquetteAt (adjacentEvenAmbient radius) face) = .upper := by
  apply adjacentEvenPlaquetteSide_eq_upper_of_center_lt
  have htime := adjacentEvenStrictUpperCanonicalRoot_exterior_time_ge
    hfit hroot hface
  unfold adjacentEvenCenter
  omega

/-! ## 5. Canonical root exchange under the even reflection -/

private theorem sameSupport_map_oneStep
    {left right : List Z4Plaq} (mapP : Z4Plaq → Z4Plaq)
    (h : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map mapP) (right.map mapP) := by
  constructor
  · intro item hitem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hitem
    exact List.mem_map.mpr ⟨source, h.1 _ hsource, rfl⟩
  · intro item hitem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hitem
    exact List.mem_map.mpr ⟨source, h.2 _ hsource, rfl⟩

private theorem sameSupport_right_eq_oneStep
    {left right target : List Z4Plaq}
    (h : sameSupport (L := z4Chain.toLattice) left right)
    (heq : right = target) :
    sameSupport (L := z4Chain.toLattice) left target := by
  cases heq
  exact h

/-- Exact geometric exchange of the two transported roots. -/
theorem adjacentEvenStrictRoots_reflection_sameSupport
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      ((geometricPolymer (adjacentEvenAmbient radius)
        (adjacentEvenStrictLowerCanonicalRoot radius base root)).map
          (timeReflectPlaquette (adjacentEvenExtent radius)))
      (geometricPolymer (adjacentEvenAmbient radius)
        (adjacentEvenStrictUpperCanonicalRoot radius base root)) := by
  have hbase : strictQueryBase base ≤ radius :=
    strictQueryBase_le_of_succ_fit hfit
  have hlowerRaw := centralStrictLowerCanonicalRoot_raw_sameSupport
    hbase hroot
  have hlowerTransport :=
    adjacentEvenStrictLowerCanonicalRoot_sameSupport hfit hroot
  have hlowerToRaw := sameSupport_trans
    (sameSupport_symm hlowerTransport) hlowerRaw
  have hreflectedToRaw := sameSupport_map_oneStep
    (timeReflectPlaquette (adjacentEvenExtent radius)) hlowerToRaw
  have hrawExchange :
      ((geometricPolymer base root).map
          (rawStrictLowerQueryPlaquette radius)).map
          (timeReflectPlaquette (adjacentEvenExtent radius)) =
        ((geometricPolymer base root).map
          (timeShiftPlaquette 1)).map
          (strictJointRawUpperQueryPlaquette radius) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro plaquette hplaquette
    simp only [Function.comp_apply]
    rw [adjacentEvenExtent_eq_oneStepReflectionExtent]
    apply adjacentEvenReflection_exchanges_raw_oneStep
    have hsourceBox := geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hroot)
      plaquette hplaquette
    have htime : plaquette.1.2.2.2 < base :=
      ((mem_boxPlaquettes plaquette base).1 hsourceBox).2.2.2
    unfold strictQueryBase uniformPaddedBase at hfit
    omega
  have hreflectedToShifted := sameSupport_right_eq_oneStep
    hreflectedToRaw hrawExchange
  have hshiftedCanonical := timeShiftCanonicalRoot_canonical
    (shift := 1) hroot
  have hupperRaw := centralStrictUpperCanonicalRoot_raw_sameSupport_local
    hfit hshiftedCanonical
  have htime := timeShiftCanonicalRoot_sameSupport
    (shift := 1) hroot
  have htimeMapped := sameSupport_map_oneStep
    (strictJointRawUpperQueryPlaquette radius) htime
  have hupperOldToShifted := sameSupport_trans hupperRaw htimeMapped
  have hupperTransport :=
    adjacentEvenStrictUpperCanonicalRoot_sameSupport hfit hroot
  have hupperNewToShifted := sameSupport_trans
    (sameSupport_symm hupperTransport) hupperOldToShifted
  exact sameSupport_trans hreflectedToShifted
    (sameSupport_symm hupperNewToShifted)

/-- Canonical ambient re-encoding of the literal reflection of the lower
root.  No numerical source ordering is assumed to survive reflection. -/
def adjacentEvenReflectedStrictLowerCanonicalRoot
    (radius base : Nat) (root : List Nat) : List Nat :=
  geometricSupportIds (adjacentEvenAmbient radius)
    ((geometricPolymer (adjacentEvenAmbient radius)
      (adjacentEvenStrictLowerCanonicalRoot radius base root)).map
        (timeReflectPlaquette (adjacentEvenExtent radius)))

theorem adjacentEvenReflectedStrictLowerCanonicalRoot_sameSupport
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (adjacentEvenAmbient radius)
        (adjacentEvenReflectedStrictLowerCanonicalRoot radius base root))
      ((geometricPolymer (adjacentEvenAmbient radius)
        (adjacentEvenStrictLowerCanonicalRoot radius base root)).map
          (timeReflectPlaquette (adjacentEvenExtent radius))) := by
  unfold adjacentEvenReflectedStrictLowerCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro reflected hreflected
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hreflected
  obtain ⟨face, hface, rfl⟩ := List.mem_map.mp hsource
  have hslab := adjacentEvenStrictLowerCanonicalRoot_face_mem_slab
    hfit hroot hface
  exact (mem_boundaryCompleteSlabPlaquettes _ _).1
    (timeReflectPlaquette_mem_boundaryCompleteSlab hslab) |>.1

/-- Canonical one-step reflection exchange.  The equality is obtained only
after geometric reflection and `geometricSupportIds` re-encoding. -/
theorem adjacentEvenReflectedStrictLowerCanonicalRoot_eq_upper
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    adjacentEvenReflectedStrictLowerCanonicalRoot radius base root =
      adjacentEvenStrictUpperCanonicalRoot radius base root := by
  apply faceSupport_eq_of_geometric_sameSupport
    (geometricSupportIds_mem_cutoffOneFaceSupports
      (adjacentEvenAmbient radius)
      ((geometricPolymer (adjacentEvenAmbient radius)
        (adjacentEvenStrictLowerCanonicalRoot radius base root)).map
          (timeReflectPlaquette (adjacentEvenExtent radius))))
    (canonicalSurfacePolymer_mem_faceSupports
      (adjacentEvenStrictUpperCanonicalRoot_canonical hfit hroot))
  exact sameSupport_trans
    (adjacentEvenReflectedStrictLowerCanonicalRoot_sameSupport hfit hroot)
    (adjacentEvenStrictRoots_reflection_sameSupport hfit hroot)

/-! ## 6. Ambient face reflection (not slab-coordinate reflection) -/

/-- Ambient identifier of a geometrically reflected adjacent-even slab face.
This indexes `boxPlaquettes (adjacentEvenAmbient radius)`, not
`boundaryCompleteSlabPlaquettes` and not `slabPhysicalFaceEdges`. -/
def adjacentEvenAmbientFaceReflectId (radius id : Nat) : Nat :=
  listIndexOf
    (timeReflectPlaquette (adjacentEvenExtent radius)
      (boxPlaquetteAt (adjacentEvenAmbient radius) id))
    (boxPlaquettes (adjacentEvenAmbient radius))

theorem adjacentEvenAmbientFaceReflectId_physical
    {radius id : Nat}
    (hid : id ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hslab : boxPlaquetteAt (adjacentEvenAmbient radius) id ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)) :
    adjacentEvenAmbientFaceReflectId radius id ∈
      physicalFaceEdges (adjacentEvenAmbient radius) := by
  unfold adjacentEvenAmbientFaceReflectId physicalFaceEdges
    plaquetteEdgeCount
  apply List.mem_range.mpr
  apply listIndexOf_lt_of_mem
  exact (mem_boundaryCompleteSlabPlaquettes _ _).1
    (timeReflectPlaquette_mem_boundaryCompleteSlab hslab) |>.1

theorem boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
    {radius id : Nat}
    (hid : id ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hslab : boxPlaquetteAt (adjacentEvenAmbient radius) id ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)) :
    boxPlaquetteAt (adjacentEvenAmbient radius)
        (adjacentEvenAmbientFaceReflectId radius id) =
      timeReflectPlaquette (adjacentEvenExtent radius)
        (boxPlaquetteAt (adjacentEvenAmbient radius) id) := by
  unfold boxPlaquetteAt adjacentEvenAmbientFaceReflectId
  apply getD_listIndexOf_of_mem
  exact (mem_boundaryCompleteSlabPlaquettes _ _).1
    (timeReflectPlaquette_mem_boundaryCompleteSlab hslab) |>.1

theorem adjacentEvenAmbientFaceReflectId_involutive
    {radius id : Nat}
    (hid : id ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hslab : boxPlaquetteAt (adjacentEvenAmbient radius) id ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)) :
    adjacentEvenAmbientFaceReflectId radius
        (adjacentEvenAmbientFaceReflectId radius id) = id := by
  have hreflectedPhysical :=
    adjacentEvenAmbientFaceReflectId_physical hid hslab
  have hreflectedSlab :
      boxPlaquetteAt (adjacentEvenAmbient radius)
          (adjacentEvenAmbientFaceReflectId radius id) ∈
        boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
    rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId hid hslab]
    exact timeReflectPlaquette_mem_boundaryCompleteSlab hslab
  apply boxPlaquetteAt_injective_on_physical
    (adjacentEvenAmbientFaceReflectId_physical
      hreflectedPhysical hreflectedSlab) hid
  rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
      hreflectedPhysical hreflectedSlab,
    boxPlaquetteAt_adjacentEvenAmbientFaceReflectId hid hslab]
  exact timeReflectPlaquette_involutive
    (adjacentEvenExtent radius) _
    ((mem_boundaryCompleteSlabPlaquettes _ _).1 hslab).2

theorem faceLinkAdjacentB_adjacentEvenAmbientFaceReflectId
    {radius left right : Nat}
    (hleftPhysical : left ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hleftSlab : boxPlaquetteAt (adjacentEvenAmbient radius) left ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius))
    (hrightPhysical : right ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hrightSlab : boxPlaquetteAt (adjacentEvenAmbient radius) right ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius))
    (hadj : faceLinkAdjacentB (adjacentEvenAmbient radius) left right = true) :
    faceLinkAdjacentB (adjacentEvenAmbient radius)
        (adjacentEvenAmbientFaceReflectId radius left)
        (adjacentEvenAmbientFaceReflectId radius right) = true := by
  apply faceLinkAdjacentB_true_of_actualAdjacent
    (adjacentEvenAmbientFaceReflectId_physical hleftPhysical hleftSlab)
    (adjacentEvenAmbientFaceReflectId_physical hrightPhysical hrightSlab)
  have hreflected := timeReflectAdjacent
    (adjacentEvenExtent radius)
    ((mem_boundaryCompleteSlabPlaquettes _ _).1 hleftSlab).2
    ((mem_boundaryCompleteSlabPlaquettes _ _).1 hrightSlab).2
    (actualAdjacentOfFaceLinkAdjacent hadj)
  simpa only [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
    hleftPhysical hleftSlab,
    boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
      hrightPhysical hrightSlab] using hreflected

/-! ## 7. Root and exterior-shell membership exchange -/

theorem mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hfacePhysical : face ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hfaceSlab : boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)) :
    face ∈ adjacentEvenStrictLowerCanonicalRoot radius base root ↔
      adjacentEvenAmbientFaceReflectId radius face ∈
        adjacentEvenStrictUpperCanonicalRoot radius base root := by
  have hreflectedPhysical :=
    adjacentEvenAmbientFaceReflectId_physical hfacePhysical hfaceSlab
  have hlowerCanonical := adjacentEvenStrictLowerCanonicalRoot_canonical
    hfit hroot
  have hupperCanonical := adjacentEvenStrictUpperCanonicalRoot_canonical
    hfit hroot
  have hexchange := adjacentEvenStrictRoots_reflection_sameSupport
    hfit hroot
  constructor
  · intro hface
    have hgeom : boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
        geometricPolymer (adjacentEvenAmbient radius)
          (adjacentEvenStrictLowerCanonicalRoot radius base root) :=
      List.mem_map.mpr ⟨face, hface, rfl⟩
    have hmapped :
        timeReflectPlaquette (adjacentEvenExtent radius)
            (boxPlaquetteAt (adjacentEvenAmbient radius) face) ∈
          (geometricPolymer (adjacentEvenAmbient radius)
            (adjacentEvenStrictLowerCanonicalRoot radius base root)).map
              (timeReflectPlaquette (adjacentEvenExtent radius)) :=
      List.mem_map.mpr ⟨_, hgeom, rfl⟩
    have hupperGeom := hexchange.1 _ hmapped
    obtain ⟨upperFace, hupperFace, hcoordinate⟩ :=
      List.mem_map.mp hupperGeom
    have hupperPhysical := mem_of_mem_sublists
      (physicalFaceEdges (adjacentEvenAmbient radius))
      (adjacentEvenStrictUpperCanonicalRoot radius base root)
      (canonicalSurfacePolymer_mem_faceSupports hupperCanonical)
      upperFace hupperFace
    have hid : adjacentEvenAmbientFaceReflectId radius face = upperFace := by
      apply boxPlaquetteAt_injective_on_physical
        hreflectedPhysical hupperPhysical
      rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
        hfacePhysical hfaceSlab]
      exact hcoordinate.symm
    simpa only [hid] using hupperFace
  · intro hreflected
    have hupperGeom :
        boxPlaquetteAt (adjacentEvenAmbient radius)
            (adjacentEvenAmbientFaceReflectId radius face) ∈
          geometricPolymer (adjacentEvenAmbient radius)
            (adjacentEvenStrictUpperCanonicalRoot radius base root) :=
      List.mem_map.mpr ⟨_, hreflected, rfl⟩
    have hmapped := hexchange.2 _ hupperGeom
    obtain ⟨sourcePlaquette, hsourcePlaquette, hreflectedEq⟩ :=
      List.mem_map.mp hmapped
    obtain ⟨sourceFace, hsourceFace, hsourceEq⟩ :=
      List.mem_map.mp hsourcePlaquette
    have hsourcePhysical := mem_of_mem_sublists
      (physicalFaceEdges (adjacentEvenAmbient radius))
      (adjacentEvenStrictLowerCanonicalRoot radius base root)
      (canonicalSurfacePolymer_mem_faceSupports hlowerCanonical)
      sourceFace hsourceFace
    have hsourceSlab :=
      adjacentEvenStrictLowerCanonicalRoot_face_mem_slab
        hfit hroot hsourceFace
    have hsourcePlaquetteSlab : sourcePlaquette ∈
        boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
      rw [← hsourceEq]
      exact hsourceSlab
    rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
      hfacePhysical hfaceSlab] at hreflectedEq
    have hback := congrArg
      (timeReflectPlaquette (adjacentEvenExtent radius)) hreflectedEq
    rw [timeReflectPlaquette_involutive
        (adjacentEvenExtent radius) sourcePlaquette
        ((mem_boundaryCompleteSlabPlaquettes _ _).1
          hsourcePlaquetteSlab).2,
      timeReflectPlaquette_involutive
        (adjacentEvenExtent radius)
        (boxPlaquetteAt (adjacentEvenAmbient radius) face)
        ((mem_boundaryCompleteSlabPlaquettes _ _).1 hfaceSlab).2] at hback
    have hid : sourceFace = face := by
      apply boxPlaquetteAt_injective_on_physical
        hsourcePhysical hfacePhysical
      rw [hsourceEq]
      exact hback
    simpa only [hid] using hsourceFace

theorem reflectId_mem_lower_iff_mem_adjacentEvenStrictUpper
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hfacePhysical : face ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hfaceSlab : boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)) :
    adjacentEvenAmbientFaceReflectId radius face ∈
        adjacentEvenStrictLowerCanonicalRoot radius base root ↔
      face ∈ adjacentEvenStrictUpperCanonicalRoot radius base root := by
  have hreflectedPhysical :=
    adjacentEvenAmbientFaceReflectId_physical hfacePhysical hfaceSlab
  have hreflectedSlab :
      boxPlaquetteAt (adjacentEvenAmbient radius)
          (adjacentEvenAmbientFaceReflectId radius face) ∈
        boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
    rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
      hfacePhysical hfaceSlab]
    exact timeReflectPlaquette_mem_boundaryCompleteSlab hfaceSlab
  have hiff := mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
    hfit hroot hreflectedPhysical hreflectedSlab
  rw [adjacentEvenAmbientFaceReflectId_involutive
    hfacePhysical hfaceSlab] at hiff
  exact hiff

theorem mem_adjacentEvenStrictLower_exterior_iff_reflectId_mem_upper_exterior
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hfacePhysical : face ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hfaceSlab : boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)) :
    face ∈ canonicalPolymerExteriorFaceQueries
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictLowerCanonicalRoot radius base root) ↔
      adjacentEvenAmbientFaceReflectId radius face ∈
        canonicalPolymerExteriorFaceQueries
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictUpperCanonicalRoot radius base root) := by
  let lower := adjacentEvenStrictLowerCanonicalRoot radius base root
  let upper := adjacentEvenStrictUpperCanonicalRoot radius base root
  have hlowerCanonical := adjacentEvenStrictLowerCanonicalRoot_canonical
    hfit hroot
  have hupperCanonical := adjacentEvenStrictUpperCanonicalRoot_canonical
    hfit hroot
  have hreflectedPhysical :=
    adjacentEvenAmbientFaceReflectId_physical hfacePhysical hfaceSlab
  have hreflectedSlab :
      boxPlaquetteAt (adjacentEvenAmbient radius)
          (adjacentEvenAmbientFaceReflectId radius face) ∈
        boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
    rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
      hfacePhysical hfaceSlab]
    exact timeReflectPlaquette_mem_boundaryCompleteSlab hfaceSlab
  constructor
  · intro hlowerExterior
    obtain ⟨_hphysical, hlowerOutside, inside, hinside, hadj⟩ :=
      (mem_canonicalPolymerExteriorFaceQueries_iff
        (adjacentEvenAmbient radius) lower face).1 hlowerExterior
    have hinsidePhysical := mem_of_mem_sublists
      (physicalFaceEdges (adjacentEvenAmbient radius)) lower
      (canonicalSurfacePolymer_mem_faceSupports hlowerCanonical)
      inside hinside
    have hinsideSlab :=
      adjacentEvenStrictLowerCanonicalRoot_face_mem_slab
        hfit hroot hinside
    have hinsideUpper :=
      (mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
        hfit hroot hinsidePhysical hinsideSlab).1 hinside
    apply (mem_canonicalPolymerExteriorFaceQueries_iff
      (adjacentEvenAmbient radius) upper
      (adjacentEvenAmbientFaceReflectId radius face)).2
    refine ⟨hreflectedPhysical, ?_,
      adjacentEvenAmbientFaceReflectId radius inside, hinsideUpper, ?_⟩
    · intro hfaceUpper
      exact hlowerOutside
        ((mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
          hfit hroot hfacePhysical hfaceSlab).2 hfaceUpper)
    · exact faceLinkAdjacentB_adjacentEvenAmbientFaceReflectId
        hinsidePhysical hinsideSlab hfacePhysical hfaceSlab hadj
  · intro hupperExterior
    obtain ⟨_hphysical, hupperOutside, inside, hinside, hadj⟩ :=
      (mem_canonicalPolymerExteriorFaceQueries_iff
        (adjacentEvenAmbient radius) upper
        (adjacentEvenAmbientFaceReflectId radius face)).1 hupperExterior
    have hinsidePhysical := mem_of_mem_sublists
      (physicalFaceEdges (adjacentEvenAmbient radius)) upper
      (canonicalSurfacePolymer_mem_faceSupports hupperCanonical)
      inside hinside
    have hinsideSlab :=
      adjacentEvenStrictUpperCanonicalRoot_face_mem_slab
        hfit hroot hinside
    let lowerInside := adjacentEvenAmbientFaceReflectId radius inside
    have hlowerInsidePhysical : lowerInside ∈
        physicalFaceEdges (adjacentEvenAmbient radius) :=
      adjacentEvenAmbientFaceReflectId_physical
        hinsidePhysical hinsideSlab
    have hlowerInsideSlab :
        boxPlaquetteAt (adjacentEvenAmbient radius) lowerInside ∈
          boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
      rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
        hinsidePhysical hinsideSlab]
      exact timeReflectPlaquette_mem_boundaryCompleteSlab hinsideSlab
    have hlowerInside : lowerInside ∈ lower := by
      apply (mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
        hfit hroot hlowerInsidePhysical hlowerInsideSlab).2
      rw [adjacentEvenAmbientFaceReflectId_involutive
        hinsidePhysical hinsideSlab]
      exact hinside
    apply (mem_canonicalPolymerExteriorFaceQueries_iff
      (adjacentEvenAmbient radius) lower face).2
    refine ⟨hfacePhysical, ?_, lowerInside, hlowerInside, ?_⟩
    · intro hfaceLower
      exact hupperOutside
        ((mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
          hfit hroot hfacePhysical hfaceSlab).1 hfaceLower)
    · have hreflectedAdj :=
        faceLinkAdjacentB_adjacentEvenAmbientFaceReflectId
          hinsidePhysical hinsideSlab
          hreflectedPhysical hreflectedSlab hadj
      rw [adjacentEvenAmbientFaceReflectId_involutive
        hfacePhysical hfaceSlab] at hreflectedAdj
      exact hreflectedAdj

theorem reflectId_mem_lower_exterior_iff_mem_upper_exterior
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hfacePhysical : face ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hfaceSlab : boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)) :
    adjacentEvenAmbientFaceReflectId radius face ∈
        canonicalPolymerExteriorFaceQueries
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictLowerCanonicalRoot radius base root) ↔
      face ∈ canonicalPolymerExteriorFaceQueries
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictUpperCanonicalRoot radius base root) := by
  have hreflectedPhysical :=
    adjacentEvenAmbientFaceReflectId_physical hfacePhysical hfaceSlab
  have hreflectedSlab :
      boxPlaquetteAt (adjacentEvenAmbient radius)
          (adjacentEvenAmbientFaceReflectId radius face) ∈
        boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius) := by
    rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
      hfacePhysical hfaceSlab]
    exact timeReflectPlaquette_mem_boundaryCompleteSlab hfaceSlab
  have hiff :=
    mem_adjacentEvenStrictLower_exterior_iff_reflectId_mem_upper_exterior
      hfit hroot hreflectedPhysical hreflectedSlab
  rw [adjacentEvenAmbientFaceReflectId_involutive
    hfacePhysical hfaceSlab] at hiff
  exact hiff

/-! ## 8. Source-ordered root collections -/

def adjacentEvenStrictLowerCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (adjacentEvenStrictLowerCanonicalRoot radius base)

def adjacentEvenStrictUpperCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (adjacentEvenStrictUpperCanonicalRoot radius base)

/-- Reflect each lower root geometrically and canonically re-encode it while
retaining the source collection's order and multiplicity. -/
def adjacentEvenReflectedStrictLowerCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (adjacentEvenReflectedStrictLowerCanonicalRoot radius base)

@[simp] theorem adjacentEvenStrictLowerCylinderRoots_length
    (radius base : Nat) (roots : List (List Nat)) :
    (adjacentEvenStrictLowerCylinderRoots radius base roots).length =
      roots.length := by
  simp [adjacentEvenStrictLowerCylinderRoots]

@[simp] theorem adjacentEvenStrictUpperCylinderRoots_length
    (radius base : Nat) (roots : List (List Nat)) :
    (adjacentEvenStrictUpperCylinderRoots radius base roots).length =
      roots.length := by
  simp [adjacentEvenStrictUpperCylinderRoots]

/-- Per-root canonical exchange lifted over the source collection.  Repeated
source roots remain repeated; no deduplication or permutation is used. -/
theorem adjacentEvenReflectedStrictLowerCylinderRoots_eq_upper
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    adjacentEvenReflectedStrictLowerCylinderRoots radius base roots =
      adjacentEvenStrictUpperCylinderRoots radius base roots := by
  unfold adjacentEvenReflectedStrictLowerCylinderRoots
    adjacentEvenStrictUpperCylinderRoots
  apply List.map_congr_left
  intro root hroot
  exact adjacentEvenReflectedStrictLowerCanonicalRoot_eq_upper
    hfit (hroots root hroot)

#print axioms adjacentEvenExtent_eq_centralAmbient
#print axioms adjacentEvenExtent_eq_oneStepReflectionExtent
#print axioms centralAmbient_le_adjacentEvenAmbient
#print axioms adjacentEvenAmbientFace_mem_slab_of_time_lt
#print axioms adjacentEvenStrictLowerCanonicalRoot_canonical
#print axioms adjacentEvenStrictUpperCanonicalRoot_canonical
#print axioms adjacentEvenStrictLowerCanonicalRoot_sameSupport
#print axioms adjacentEvenStrictUpperCanonicalRoot_sameSupport
#print axioms adjacentEvenStrictLowerCanonicalRoot_time_add_two_le
#print axioms adjacentEvenStrictUpperCanonicalRoot_time_ge
#print axioms adjacentEvenStrictUpperCanonicalRoot_time_lt
#print axioms adjacentEvenStrictLowerCanonicalRoot_face_mem_slab
#print axioms adjacentEvenStrictUpperCanonicalRoot_face_mem_slab
#print axioms adjacentEvenStrictLowerCanonicalRoot_supported
#print axioms adjacentEvenStrictUpperCanonicalRoot_supported
#print axioms adjacentEvenStrictLowerCanonicalRoot_side
#print axioms adjacentEvenStrictUpperCanonicalRoot_side
#print axioms adjacentEvenStrictLowerCanonicalRoot_exterior_time_add_one_le
#print axioms adjacentEvenStrictUpperCanonicalRoot_exterior_time_ge
#print axioms adjacentEvenStrictUpperCanonicalRoot_exterior_time_lt_extent
#print axioms adjacentEvenStrictLowerCanonicalRoot_exterior_mem_slab
#print axioms adjacentEvenStrictUpperCanonicalRoot_exterior_mem_slab
#print axioms adjacentEvenStrictLowerCanonicalRoot_exterior_side
#print axioms adjacentEvenStrictUpperCanonicalRoot_exterior_side
#print axioms adjacentEvenStrictRoots_reflection_sameSupport
#print axioms adjacentEvenReflectedStrictLowerCanonicalRoot_sameSupport
#print axioms adjacentEvenReflectedStrictLowerCanonicalRoot_eq_upper
#print axioms adjacentEvenAmbientFaceReflectId_physical
#print axioms boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
#print axioms adjacentEvenAmbientFaceReflectId_involutive
#print axioms faceLinkAdjacentB_adjacentEvenAmbientFaceReflectId
#print axioms mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
#print axioms reflectId_mem_lower_iff_mem_adjacentEvenStrictUpper
#print axioms mem_adjacentEvenStrictLower_exterior_iff_reflectId_mem_upper_exterior
#print axioms reflectId_mem_lower_exterior_iff_mem_upper_exterior
#print axioms adjacentEvenReflectedStrictLowerCylinderRoots_eq_upper

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepQueryGeometry
