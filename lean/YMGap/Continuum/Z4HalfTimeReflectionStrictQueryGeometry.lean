/-
# Strict-side geometry for local half-time queries

The one-link exterior shell of a marked polymer is part of its occurrence
query.  A three-layer translation margin places both the marked faces and that
entire shell strictly on one side of the half-time reflection plane.  This
file establishes the geometric estimates used to reflect the resulting local
chart into the lower-support coordinate.
-/

import YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
import YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
import YMGap.Continuum.Z4UniformShiftPhysicalTransport

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

/-- Bases of two plaquettes sharing a lattice link differ by at most one in
the time coordinate. -/
theorem adjacent_time_le_add_one
    {left right : YMGap.Continuum.ClusterCount4DProgress.Z4Plaq}
    (hadj : z4Chain.toLattice.Adjacent left right) :
    left.1.2.2.2 ≤ right.1.2.2.2 + 1 := by
  obtain ⟨link, hleft, hright⟩ := hadj
  change decide (link ∈ edgesOf left) = true at hleft
  change decide (link ∈ edgesOf right) = true at hright
  have hleftMem : link ∈ edgesOf left := of_decide_eq_true hleft
  have hrightMem : link ∈ edgesOf right := of_decide_eq_true hright
  obtain ⟨⟨a, b, c, d⟩, leftPlane⟩ := left
  obtain ⟨⟨e, f, g, h⟩, rightPlane⟩ := right
  obtain ⟨⟨i, j, k, l⟩, direction⟩ := link
  change (((i, j, k, l), direction) : Z4Link) ∈
    edgesOf (((a, b, c, d), leftPlane) : Z4Plaq) at hleftMem
  change (((i, j, k, l), direction) : Z4Link) ∈
    edgesOf (((e, f, g, h), rightPlane) : Z4Plaq) at hrightMem
  change d ≤ h + 1
  cases leftPlane <;> cases rightPlane <;> cases direction <;>
    simp [edgesOf, dirsOf, addE] at hleftMem hrightMem <;>
    omega

/-- A plaquette based strictly after the central slice is on the upper side,
independently of its orientation. -/
theorem plaquetteHalfSide_eq_upper_of_time_gt
    {half : Nat}
    {plaquette : YMGap.Continuum.ClusterCount4DProgress.Z4Plaq}
    (htime : half < plaquette.1.2.2.2) :
    plaquetteHalfSide half plaquette = .upper := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  change half < d at htime
  change plaquetteHalfSide half (((a, b, c, d), plane) : Z4Plaq) = .upper
  have hnle : ¬ d ≤ half := by omega
  have hnlt : ¬ d < half := by omega
  have hne : d ≠ half := by omega
  cases plane <;>
    simp [plaquetteHalfSide, spatialHalfSide, temporalHalfSide,
      hnle, hnlt, hne]

/-- A plaquette based strictly before the central slice is on the lower side,
independently of its orientation. -/
theorem plaquetteHalfSide_eq_lower_of_time_lt
    {half : Nat} {plaquette : Z4Plaq}
    (htime : plaquette.1.2.2.2 < half) :
    plaquetteHalfSide half plaquette = .lower := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  change d < half at htime
  change plaquetteHalfSide half (((a, b, c, d), plane) : Z4Plaq) = .lower
  have hle : d ≤ half := Nat.le_of_lt htime
  cases plane <;>
    simp [plaquetteHalfSide, spatialHalfSide, temporalHalfSide,
      htime, hle]

/-! ## Reflection preserves geometric connectedness -/

def timeReflectAdjacent
    (extent : Nat)
    {left right : Z4Plaq}
    (hleft : plaquetteTimeAdmissible extent left)
    (hright : plaquetteTimeAdmissible extent right)
    (hadj : z4Chain.toLattice.Adjacent left right) :
    z4Chain.toLattice.Adjacent
      (timeReflectPlaquette extent left)
      (timeReflectPlaquette extent right) := by
  refine {
    link := timeReflectLink extent hadj.link
    on_p := ?_
    on_q := ?_
  }
  · change decide
      (timeReflectLink extent hadj.link ∈
        edgesOf (timeReflectPlaquette extent left)) = true
    apply decide_eq_true
    apply timeReflectLink_mem_edgesOf_timeReflectPlaquette hleft
    have hon := hadj.on_p
    change decide (hadj.link ∈ edgesOf left) = true at hon
    exact of_decide_eq_true hon
  · change decide
      (timeReflectLink extent hadj.link ∈
        edgesOf (timeReflectPlaquette extent right)) = true
    apply decide_eq_true
    apply timeReflectLink_mem_edgesOf_timeReflectPlaquette hright
    have hon := hadj.on_q
    change decide (hadj.link ∈ edgesOf right) = true at hon
    exact of_decide_eq_true hon

def timeReflectChain
    (extent : Nat) {support : List Z4Plaq}
    (hadmissible : ∀ plaquette, plaquette ∈ support →
      plaquetteTimeAdmissible extent plaquette) :
    {left right : Z4Plaq} →
      (hleft : left ∈ support) →
      PolymerModel.ChainIn z4Chain.toLattice support left right →
      PolymerModel.ChainIn z4Chain.toLattice
        (support.map (timeReflectPlaquette extent))
        (timeReflectPlaquette extent left)
        (timeReflectPlaquette extent right)
  | _, _, _, PolymerModel.ChainIn.refl point =>
      PolymerModel.ChainIn.refl _
  | left, _right, hleft,
      PolymerModel.ChainIn.step (r := next) hadj hnext rest =>
      PolymerModel.ChainIn.step
        (timeReflectAdjacent extent
          (hadmissible left hleft) (hadmissible next hnext) hadj)
        (List.mem_map.mpr ⟨next, hnext, rfl⟩)
        (timeReflectChain extent hadmissible hnext rest)

def timeReflectConnected
    (extent : Nat) {support : List Z4Plaq}
    (hadmissible : ∀ plaquette, plaquette ∈ support →
      plaquetteTimeAdmissible extent plaquette)
    (hconnected : PolymerModel.connectedIn
      (L := z4Chain.toLattice) support) :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      (support.map (timeReflectPlaquette extent)) := by
  intro left right hleft hright
  obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
    decodeMapMember (timeReflectPlaquette extent) support left hleft
  obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
    decodeMapMember (timeReflectPlaquette extent) support right hright
  rw [← hleftEq, ← hrightEq]
  exact timeReflectChain extent hadmissible hsourceLeft
    (hconnected sourceLeft sourceRight hsourceLeft hsourceRight)

/-! ## Canonical numerical re-encoding of a reflected slab root -/

theorem canonicalPolymerSlabSupported_face
    {half : Nat} {root : List Nat}
    (hsupported : canonicalPolymerSlabSupportedB (centralExtent half) root = true)
    {face : Nat} (hface : face ∈ root) :
    boxPlaquetteAt (centralAmbient half) face ∈
      boundaryCompleteSlabPlaquettes (centralExtent half) := by
  unfold canonicalPolymerSlabSupportedB at hsupported
  have hdecision := List.all_eq_true.mp hsupported face hface
  exact of_decide_eq_true hdecision

/-- Re-encode the geometric time reflection of a canonical slab-supported
root as canonical ambient face identifiers. -/
def centralReflectedCanonicalRoot
    (half : Nat) (root : List Nat) : List Nat :=
  geometricSupportIds (centralAmbient half)
    ((geometricPolymer (centralAmbient half) root).map
      (timeReflectPlaquette (centralExtent half)))

theorem centralReflectedCanonicalRoot_sameSupport
    {half : Nat} {root : List Nat}
    (hsupported : canonicalPolymerSlabSupportedB (centralExtent half) root = true) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient half)
        (centralReflectedCanonicalRoot half root))
      ((geometricPolymer (centralAmbient half) root).map
        (timeReflectPlaquette (centralExtent half))) := by
  unfold centralReflectedCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro reflected hreflected
  obtain ⟨source, hsource, hreflectedEq⟩ := List.mem_map.mp hreflected
  obtain ⟨face, hface, hsourceEq⟩ := List.mem_map.mp hsource
  rw [← hreflectedEq, ← hsourceEq]
  have hslab := canonicalPolymerSlabSupported_face hsupported hface
  exact (mem_boundaryCompleteSlabPlaquettes
    (centralExtent half)
    (timeReflectPlaquette (centralExtent half)
      (boxPlaquetteAt (centralAmbient half) face))).1
      (timeReflectPlaquette_mem_boundaryCompleteSlab hslab) |>.1

def centralReflectedCanonicalRoot_nonempty
    {half : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers (centralAmbient half))
    (hsupported : canonicalPolymerSlabSupportedB (centralExtent half) root = true) :
    Σ' face : Nat, face ∈ centralReflectedCanonicalRoot half root := by
  obtain ⟨sourceFace, hsourceFace⟩ :=
    canonicalSurfacePolymers_allNonempty (centralAmbient half) root hroot
  have hsource : boxPlaquetteAt (centralAmbient half) sourceFace ∈
      geometricPolymer (centralAmbient half) root :=
    List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
  have hreflected :
      timeReflectPlaquette (centralExtent half)
          (boxPlaquetteAt (centralAmbient half) sourceFace) ∈
        (geometricPolymer (centralAmbient half) root).map
          (timeReflectPlaquette (centralExtent half)) :=
    List.mem_map.mpr ⟨_, hsource, rfl⟩
  have hencoded :=
    (centralReflectedCanonicalRoot_sameSupport hsupported).2 _ hreflected
  obtain ⟨targetFace, htargetFace, _⟩ :=
    decodeMapMember (boxPlaquetteAt (centralAmbient half))
      (centralReflectedCanonicalRoot half root)
      (timeReflectPlaquette (centralExtent half)
        (boxPlaquetteAt (centralAmbient half) sourceFace))
      hencoded
  exact ⟨targetFace, htargetFace⟩

def centralReflectedCanonicalRoot_connected
    {half : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers (centralAmbient half))
    (hsupported : canonicalPolymerSlabSupportedB (centralExtent half) root = true) :
    InternallyConnected (faceLinkAdjacentB (centralAmbient half))
      (centralReflectedCanonicalRoot half root) := by
  unfold centralReflectedCanonicalRoot
  apply geometricSupportIds_connected
  · intro reflected hreflected
    obtain ⟨source, hsource, hreflectedEq⟩ := List.mem_map.mp hreflected
    obtain ⟨face, hface, hsourceEq⟩ := List.mem_map.mp hsource
    rw [← hreflectedEq, ← hsourceEq]
    have hslab := canonicalPolymerSlabSupported_face hsupported hface
    exact (mem_boundaryCompleteSlabPlaquettes
      (centralExtent half)
      (timeReflectPlaquette (centralExtent half)
        (boxPlaquetteAt (centralAmbient half) face))).1
        (timeReflectPlaquette_mem_boundaryCompleteSlab hslab) |>.1
  · apply timeReflectConnected
    · intro plaquette hplaquette
      obtain ⟨face, hface, hplaquetteEq⟩ := List.mem_map.mp hplaquette
      rw [← hplaquetteEq]
      exact (mem_boundaryCompleteSlabPlaquettes
        (centralExtent half)
        (boxPlaquetteAt (centralAmbient half) face)).1
          (canonicalPolymerSlabSupported_face hsupported hface) |>.2
    · exact numericalConnectedToGeometric
        ((canonicalSurfacePolymers_allConnected (centralAmbient half))
          root hroot)

theorem centralReflectedCanonicalRoot_canonical
    {half : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers (centralAmbient half))
    (hsupported : canonicalPolymerSlabSupportedB (centralExtent half) root = true) :
    centralReflectedCanonicalRoot half root ∈
      canonicalSurfacePolymers (centralAmbient half) :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (geometricSupportIds_mem_cutoffOneFaceSupports
      (centralAmbient half)
      ((geometricPolymer (centralAmbient half) root).map
        (timeReflectPlaquette (centralExtent half))))
    (centralReflectedCanonicalRoot_nonempty hroot hsupported)
    (centralReflectedCanonicalRoot_connected hroot hsupported)

theorem centralReflectedCanonicalRoot_side_lower
    {half : Nat} {root : List Nat}
    (hsupported : canonicalPolymerSlabSupportedB (centralExtent half) root = true)
    (hupper : ∀ face, face ∈ root →
      plaquetteHalfSide half
        (boxPlaquetteAt (centralAmbient half) face) = .upper)
    {face : Nat} (hface : face ∈ centralReflectedCanonicalRoot half root) :
    plaquetteHalfSide half
      (boxPlaquetteAt (centralAmbient half) face) = .lower := by
  have hgeom : boxPlaquetteAt (centralAmbient half) face ∈
      geometricPolymer (centralAmbient half)
        (centralReflectedCanonicalRoot half root) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hmapped :=
    (centralReflectedCanonicalRoot_sameSupport hsupported).1 _ hgeom
  obtain ⟨sourcePlaquette, hsourcePlaquette, hreflectedEq⟩ :=
    List.mem_map.mp hmapped
  obtain ⟨sourceFace, hsourceFace, hsourceEq⟩ :=
    List.mem_map.mp hsourcePlaquette
  have hadmissible :=
    (mem_boundaryCompleteSlabPlaquettes
      (centralExtent half)
      (boxPlaquetteAt (centralAmbient half) sourceFace)).1
      (canonicalPolymerSlabSupported_face hsupported hsourceFace) |>.2
  have hside := plaquetteHalfSide_reflection hadmissible
  rw [hupper sourceFace hsourceFace] at hside
  simp only [flipSide] at hside
  rw [hsourceEq, hreflectedEq] at hside
  exact hside

/-! ## A three-layer pre-shift before the centered stage embedding -/

/-- The fixed source box after adding a three-face margin on every side. -/
def strictQueryBase (base : Nat) : Nat :=
  uniformPaddedBase 3 base

/-- A fixed canonical root translated three lattice units away from every
boundary of its padded source box. -/
def strictQuerySourceRoot (base : Nat) (root : List Nat) : List Nat :=
  uniformShiftCanonicalRoot 3 base root

/-- Embed the margin-three source root into the usual adjacent even half-time
ambient box.  This is the upper marked root that will subsequently be
reflected into the lower query chart. -/
def centralStrictUpperCanonicalRoot
    (radius base : Nat) (root : List Nat) : List Nat :=
  centralFaceQueryCanonicalRoot radius (strictQueryBase base)
    (strictQuerySourceRoot base root)

theorem strictQuerySourceRoot_canonical
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    strictQuerySourceRoot base root ∈
      canonicalSurfacePolymers (strictQueryBase base) := by
  exact uniformShiftCanonicalRoot_canonical hroot

theorem centralStrictUpperCanonicalRoot_canonical
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictUpperCanonicalRoot radius base root ∈
      canonicalSurfacePolymers (centralAmbient radius) := by
  exact centralFaceQueryCanonicalRoot_canonical hbase
    (strictQuerySourceRoot_canonical hroot)

/-- Every face of the margin-three marked root is based at least three slices
strictly above the half-time plane before reflection. -/
theorem centralStrictUpperCanonicalRoot_time_ge
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ centralStrictUpperCanonicalRoot radius base root) :
    radius + 3 ≤
      (boxPlaquetteAt (centralAmbient radius) face).1.2.2.2 := by
  have hgeom : boxPlaquetteAt (centralAmbient radius) face ∈
      geometricPolymer (centralAmbient radius)
        (centralStrictUpperCanonicalRoot radius base root) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hcentral :=
    (centralFaceQueryCanonicalRoot_sameSupport hbase
      (strictQuerySourceRoot_canonical hroot)).1 _ hgeom
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hcentral
  have hmargin :=
    (uniformShiftCanonicalRoot_sameSupport hroot).1 source hsource
  obtain ⟨original, horiginal, horiginalEq⟩ :=
    List.mem_map.mp hmargin
  rw [← hsourceEq, ← horiginalEq]
  simp only [uniformShiftPlaquette, uniformShiftVertex]
  omega

theorem centralStrictUpperCanonicalRoot_side
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ centralStrictUpperCanonicalRoot radius base root) :
    plaquetteHalfSide radius
      (boxPlaquetteAt (centralAmbient radius) face) = .upper := by
  apply plaquetteHalfSide_eq_upper_of_time_gt
  have htime := centralStrictUpperCanonicalRoot_time_ge
    hbase hroot hface
  omega

/-- The three-layer margin gives a spare layer for occurrence queries:
every face in the one-link exterior shell remains strictly upper as well. -/
theorem centralStrictUpperCanonicalRoot_exterior_side
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (centralAmbient radius)
      (centralStrictUpperCanonicalRoot radius base root)) :
    plaquetteHalfSide radius
      (boxPlaquetteAt (centralAmbient radius) face) = .upper := by
  obtain ⟨_hphysical, _houtside, inside, hinside, hadj⟩ :=
    (mem_canonicalPolymerExteriorFaceQueries_iff
      (centralAmbient radius)
      (centralStrictUpperCanonicalRoot radius base root) face).1 hface
  have hinsideTime := centralStrictUpperCanonicalRoot_time_ge
    hbase hroot hinside
  have htimeStep := adjacent_time_le_add_one
    (actualAdjacentOfFaceLinkAdjacent hadj)
  apply plaquetteHalfSide_eq_upper_of_time_gt
  omega

/-! ## The concrete strictly lower reflected chart -/

def centralStrictLowerCanonicalRoot
    (radius base : Nat) (root : List Nat) : List Nat :=
  centralReflectedCanonicalRoot radius
    (centralStrictUpperCanonicalRoot radius base root)

theorem centralStrictUpperCanonicalRoot_supported
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    canonicalPolymerSlabSupportedB (centralExtent radius)
      (centralStrictUpperCanonicalRoot radius base root) = true := by
  exact centralFaceQueryCanonicalRoot_supported hbase
    (strictQuerySourceRoot_canonical hroot)

theorem centralStrictLowerCanonicalRoot_canonical
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCanonicalRoot radius base root ∈
      canonicalSurfacePolymers (centralAmbient radius) := by
  exact centralReflectedCanonicalRoot_canonical
    (centralStrictUpperCanonicalRoot_canonical hbase hroot)
    (centralStrictUpperCanonicalRoot_supported hbase hroot)

theorem centralStrictLowerCanonicalRoot_side
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ centralStrictLowerCanonicalRoot radius base root) :
    plaquetteHalfSide radius
      (boxPlaquetteAt (centralAmbient radius) face) = .lower := by
  apply centralReflectedCanonicalRoot_side_lower
    (centralStrictUpperCanonicalRoot_supported hbase hroot)
  · intro upperFace hupperFace
    exact centralStrictUpperCanonicalRoot_side hbase hroot hupperFace
  · exact hface

/-- Reflected marked faces retain two untouched layers below the reflection
plane; one of them will be spent on the exterior occurrence shell. -/
theorem centralStrictLowerCanonicalRoot_time_add_two_le
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ centralStrictLowerCanonicalRoot radius base root) :
    (boxPlaquetteAt (centralAmbient radius) face).1.2.2.2 + 2 ≤
      radius := by
  have hsupported := centralStrictUpperCanonicalRoot_supported hbase hroot
  have hgeom : boxPlaquetteAt (centralAmbient radius) face ∈
      geometricPolymer (centralAmbient radius)
        (centralStrictLowerCanonicalRoot radius base root) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hmapped :=
    (centralReflectedCanonicalRoot_sameSupport hsupported).1 _ hgeom
  obtain ⟨sourcePlaquette, hsourcePlaquette, hreflectedEq⟩ :=
    List.mem_map.mp hmapped
  obtain ⟨sourceFace, hsourceFace, hsourceEq⟩ :=
    List.mem_map.mp hsourcePlaquette
  have htime := centralStrictUpperCanonicalRoot_time_ge
    hbase hroot hsourceFace
  have hadmissible :=
    (mem_boundaryCompleteSlabPlaquettes
      (centralExtent radius)
      (boxPlaquetteAt (centralAmbient radius) sourceFace)).1
      (canonicalPolymerSlabSupported_face hsupported hsourceFace) |>.2
  rw [hsourceEq] at htime
  rw [hsourceEq] at hadmissible
  rw [← hreflectedEq]
  change radius + 3 ≤ sourcePlaquette.1.2.2.2 at htime
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := sourcePlaquette
  change radius + 3 ≤ d at htime
  cases plane <;>
    simp [timeReflectPlaquette, plaquetteTimeAdmissible,
      centralExtent] at hadmissible ⊢ <;>
    omega

/-- Every one-link exterior face of the reflected margin-three root remains
strictly lower, which discharges the complete local occurrence query rather
than only its internal marked faces. -/
theorem centralStrictLowerCanonicalRoot_exterior_side
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (centralAmbient radius)
      (centralStrictLowerCanonicalRoot radius base root)) :
    plaquetteHalfSide radius
      (boxPlaquetteAt (centralAmbient radius) face) = .lower := by
  obtain ⟨_hphysical, _houtside, inside, hinside, hadj⟩ :=
    (mem_canonicalPolymerExteriorFaceQueries_iff
      (centralAmbient radius)
      (centralStrictLowerCanonicalRoot radius base root) face).1 hface
  have hinsideTime := centralStrictLowerCanonicalRoot_time_add_two_le
    hbase hroot hinside
  have hforward := actualAdjacentOfFaceLinkAdjacent hadj
  have hreverse : z4Chain.toLattice.Adjacent
      (boxPlaquetteAt (centralAmbient radius) face)
      (boxPlaquetteAt (centralAmbient radius) inside) := {
    link := hforward.link
    on_p := hforward.on_q
    on_q := hforward.on_p
  }
  have htimeStep := adjacent_time_le_add_one hreverse
  apply plaquetteHalfSide_eq_lower_of_time_lt
  omega

def centralStrictLowerCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (centralStrictLowerCanonicalRoot radius base)

@[simp] theorem centralStrictLowerCylinderRoots_length
    (radius base : Nat) (roots : List (List Nat)) :
    (centralStrictLowerCylinderRoots radius base roots).length =
      roots.length := by
  simp [centralStrictLowerCylinderRoots]

theorem centralStrictLowerCylinderRoots_canonical
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centralStrictLowerCylinderRoots radius base roots →
      target ∈ canonicalSurfacePolymers (centralAmbient radius) := by
  intro target htarget
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq]
  exact centralStrictLowerCanonicalRoot_canonical hbase
    (hroots source hsource)

theorem centralStrictLowerCylinderRoots_internal_side
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centralStrictLowerCylinderRoots radius base roots →
      ∀ face, face ∈ target →
        plaquetteHalfSide radius
          (boxPlaquetteAt (centralAmbient radius) face) = .lower := by
  intro target htarget face hface
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq] at hface
  exact centralStrictLowerCanonicalRoot_side hbase
    (hroots source hsource) hface

theorem centralStrictLowerCylinderRoots_exterior_side
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centralStrictLowerCylinderRoots radius base roots →
      ∀ face, face ∈ canonicalPolymerExteriorFaceQueries
        (centralAmbient radius) target →
          plaquetteHalfSide radius
            (boxPlaquetteAt (centralAmbient radius) face) = .lower := by
  intro target htarget face hface
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq] at hface
  exact centralStrictLowerCanonicalRoot_exterior_side hbase
    (hroots source hsource) hface

/-- The concrete reflected, margin-three marked chart satisfies all geometry
needed by the lower-support decoder, so no abstract side hypotheses remain. -/
theorem centralStrictLowerSupportQueryFingerprint_eq_familyOccurrence
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    centralLowerSupportQueryFingerprint radius
        (centralStrictLowerCylinderRoots radius base roots)
        (centralHalfSupportCode radius
          (centralLowerRestriction radius
            (ambientToSlabPhysical (centralExtent radius) physical))) =
      familyOccurrenceFingerprint
        (centralStrictLowerCylinderRoots radius base roots)
        (physicalCanonicalAmbientFamily (centralAmbient radius) physical) := by
  exact centralLowerSupportQueryFingerprint_eq_familyOccurrence
    radius (centralStrictLowerCylinderRoots radius base roots) physical
    (centralStrictLowerCylinderRoots_canonical hbase hroots)
    (centralStrictLowerCylinderRoots_internal_side hbase hroots)
    (centralStrictLowerCylinderRoots_exterior_side hbase hroots)

#print axioms adjacent_time_le_add_one
#print axioms plaquetteHalfSide_eq_upper_of_time_gt
#print axioms plaquetteHalfSide_eq_lower_of_time_lt
#print axioms centralReflectedCanonicalRoot_canonical
#print axioms centralReflectedCanonicalRoot_side_lower
#print axioms centralStrictUpperCanonicalRoot_canonical
#print axioms centralStrictUpperCanonicalRoot_time_ge
#print axioms centralStrictUpperCanonicalRoot_side
#print axioms centralStrictUpperCanonicalRoot_exterior_side
#print axioms centralStrictLowerCanonicalRoot_canonical
#print axioms centralStrictLowerCanonicalRoot_side
#print axioms centralStrictLowerCanonicalRoot_time_add_two_le
#print axioms centralStrictLowerCanonicalRoot_exterior_side
#print axioms centralStrictLowerCylinderRoots_canonical
#print axioms centralStrictLowerCylinderRoots_internal_side
#print axioms centralStrictLowerCylinderRoots_exterior_side
#print axioms centralStrictLowerSupportQueryFingerprint_eq_familyOccurrence

end YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
