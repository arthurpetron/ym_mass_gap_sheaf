/-
# Time-translation transport for strict half-time cylinder queries

This module tests and then constructs the complete-lower-support query
intertwiner needed for positive-time translation to descend through the
quotient-free strict-cylinder semantic relation.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. The naive same-radius law is false -/

/-- The geometric operation underneath one strict lower query coordinate,
before canonical numerical re-encoding. -/
def rawStrictLowerQueryPlaquette
    (radius : Nat) (plaquette : Z4Plaq) : Z4Plaq :=
  timeReflectPlaquette (centralExtent radius)
    (uniformShiftPlaquette radius
      (uniformShiftPlaquette 3 plaquette))

/-- Translating the source while keeping the reflection radius fixed is not
an intertwiner: reflection reverses the time displacement.  This closed
counterexample fences off the strongest naive same-support formulation. -/
theorem rawStrictLowerQueryPlaquette_sameRadius_counterexample :
    rawStrictLowerQueryPlaquette 5
        (timeShiftPlaquette 1 (((0, 0, 0, 0), .p01) : Z4Plaq)) ≠
      rawStrictLowerQueryPlaquette 5
        (((0, 0, 0, 0), .p01) : Z4Plaq) := by
  decide

/-- The universal same-radius covariance statement ruled out by the closed
origin-plaquette computation. -/
def RawStrictLowerSameRadiusCovariant : Prop :=
  ∀ radius shift plaquette,
    rawStrictLowerQueryPlaquette radius
        (timeShiftPlaquette shift plaquette) =
      rawStrictLowerQueryPlaquette radius plaquette

theorem not_rawStrictLowerSameRadiusCovariant :
    ¬ RawStrictLowerSameRadiusCovariant := by
  intro hcovariant
  exact rawStrictLowerQueryPlaquette_sameRadius_counterexample
    (hcovariant 5 1 (((0, 0, 0, 0), .p01) : Z4Plaq))

/-! ## 2. The correct radius-shifted geometric covariance -/

/-- Shift only the three spatial base coordinates of a plaquette. -/
def spatialShiftVertex (shift : Nat) : Z4Vertex → Z4Vertex
  | (a, b, c, d) => (a + shift, b + shift, c + shift, d)

def spatialShiftLink (shift : Nat) (link : Z4Link) : Z4Link :=
  (spatialShiftVertex shift link.1, link.2)

def spatialShiftPlaquette (shift : Nat) : Z4Plaq → Z4Plaq
  | (vertex, plane) => (spatialShiftVertex shift vertex, plane)

theorem spatialShiftVertex_injective (shift : Nat) :
    Function.Injective (spatialShiftVertex shift) := by
  intro left right heq
  obtain ⟨a, b, c, d⟩ := left
  obtain ⟨a', b', c', d'⟩ := right
  simp only [spatialShiftVertex, Prod.mk.injEq] at heq ⊢
  exact ⟨Nat.add_right_cancel heq.1,
    Nat.add_right_cancel heq.2.1,
    Nat.add_right_cancel heq.2.2.1, heq.2.2.2⟩

theorem spatialShiftLink_injective (shift : Nat) :
    Function.Injective (spatialShiftLink shift) := by
  intro left right heq
  obtain ⟨leftVertex, leftDirection⟩ := left
  obtain ⟨rightVertex, rightDirection⟩ := right
  simp only [spatialShiftLink, Prod.mk.injEq] at heq ⊢
  exact ⟨spatialShiftVertex_injective shift heq.1, heq.2⟩

theorem spatialShiftPlaquette_injective (shift : Nat) :
    Function.Injective (spatialShiftPlaquette shift) := by
  intro left right heq
  obtain ⟨leftVertex, leftPlane⟩ := left
  obtain ⟨rightVertex, rightPlane⟩ := right
  simp only [spatialShiftPlaquette, Prod.mk.injEq] at heq ⊢
  exact ⟨spatialShiftVertex_injective shift heq.1, heq.2⟩

theorem spatialShiftVertex_addE
    (shift : Nat) (vertex : Z4Vertex) (direction : Dir4) :
    spatialShiftVertex shift (addE vertex direction) =
      addE (spatialShiftVertex shift vertex) direction := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction <;> simp [spatialShiftVertex, addE] <;> omega

theorem edgesOf_spatialShiftPlaquette
    (shift : Nat) (plaquette : Z4Plaq) :
    edgesOf (spatialShiftPlaquette shift plaquette) =
      (edgesOf plaquette).map (spatialShiftLink shift) := by
  simp [edgesOf, spatialShiftPlaquette, spatialShiftLink,
    spatialShiftVertex_addE]

def spatialShiftAdjacent (shift : Nat) {left right : Z4Plaq}
    (adjacent : z4Chain.toLattice.Adjacent left right) :
    z4Chain.toLattice.Adjacent
      (spatialShiftPlaquette shift left)
      (spatialShiftPlaquette shift right) := by
  refine {
    link := spatialShiftLink shift adjacent.link
    on_p := ?_
    on_q := ?_
  }
  · change z4Boundary (spatialShiftPlaquette shift left)
      (spatialShiftLink shift adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_spatialShiftPlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_p, rfl⟩
  · change z4Boundary (spatialShiftPlaquette shift right)
      (spatialShiftLink shift adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_spatialShiftPlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_q, rfl⟩

/-- Spatial translation reflects genuine shared-link adjacency: no new
adjacency can be created between two translated faces. -/
def spatialUnshiftAdjacentOfShifted
    (shift : Nat) {left right : Z4Plaq}
    (adjacent : z4Chain.toLattice.Adjacent
      (spatialShiftPlaquette shift left)
      (spatialShiftPlaquette shift right)) :
    z4Chain.toLattice.Adjacent left right := by
  obtain ⟨link, hleft, hright⟩ := adjacent
  change decide
    (link ∈ edgesOf (spatialShiftPlaquette shift left)) = true at hleft
  change decide
    (link ∈ edgesOf (spatialShiftPlaquette shift right)) = true at hright
  have hleftMem : link ∈
      edgesOf (spatialShiftPlaquette shift left) :=
    of_decide_eq_true hleft
  have hrightMem : link ∈
      edgesOf (spatialShiftPlaquette shift right) :=
    of_decide_eq_true hright
  rw [edgesOf_spatialShiftPlaquette] at hleftMem hrightMem
  obtain ⟨leftLink, hleftLink, hleftEq⟩ :=
    decodeMapMember (spatialShiftLink shift) (edgesOf left) link hleftMem
  obtain ⟨rightLink, hrightLink, hrightEq⟩ :=
    decodeMapMember (spatialShiftLink shift) (edgesOf right) link hrightMem
  have hlinkEq : leftLink = rightLink :=
    spatialShiftLink_injective shift (hleftEq.trans hrightEq.symm)
  refine {
    link := leftLink
    on_p := ?_
    on_q := ?_
  }
  · change decide (leftLink ∈ edgesOf left) = true
    exact decide_eq_true hleftLink
  · change decide (leftLink ∈ edgesOf right) = true
    exact decide_eq_true (by simpa only [hlinkEq] using hrightLink)

/-- The spatial shift embeds the source box in the box padded by `shift` on
both ends of every coordinate.  The fourth coordinate is left at the lower
end of that larger box. -/
theorem spatialShiftPlaquette_mem_padded_box
    {shift base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    spatialShiftPlaquette shift plaquette ∈
      boxPlaquettes (uniformPaddedBase shift base) := by
  rw [mem_boxPlaquettes] at hplaquette ⊢
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  change a < base ∧ b < base ∧ c < base ∧ d < base at hplaquette
  simp only [spatialShiftPlaquette, spatialShiftVertex]
  unfold uniformPaddedBase
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Constructive numerical identifier of the spatial translate of a physical
source face.  The irrelevant fallback is used only off the physical range. -/
def spatialShiftFaceId (shift base sourceId : Nat) : Nat :=
  listIndexOf
    (spatialShiftPlaquette shift (boxPlaquetteAt base sourceId))
    (boxPlaquettes (uniformPaddedBase shift base))

theorem spatialShiftFaceId_physical
    {shift base sourceId : Nat}
    (hsource : sourceId ∈ physicalFaceEdges base) :
    spatialShiftFaceId shift base sourceId ∈
      physicalFaceEdges (uniformPaddedBase shift base) := by
  unfold spatialShiftFaceId physicalFaceEdges plaquetteEdgeCount
  apply List.mem_range.mpr
  apply listIndexOf_lt_of_mem
  exact spatialShiftPlaquette_mem_padded_box
    (boxPlaquetteAt_mem_boxPlaquettes_of_physical hsource)

theorem boxPlaquetteAt_spatialShiftFaceId
    {shift base sourceId : Nat}
    (hsource : sourceId ∈ physicalFaceEdges base) :
    boxPlaquetteAt (uniformPaddedBase shift base)
        (spatialShiftFaceId shift base sourceId) =
      spatialShiftPlaquette shift (boxPlaquetteAt base sourceId) := by
  unfold boxPlaquetteAt spatialShiftFaceId
  exact getD_listIndexOf_of_mem fallbackPlaquette _ _
    (spatialShiftPlaquette_mem_padded_box
      (boxPlaquetteAt_mem_boxPlaquettes_of_physical hsource))

theorem spatialShiftFaceId_injective_on_physical
    {shift base left right : Nat}
    (hleft : left ∈ physicalFaceEdges base)
    (hright : right ∈ physicalFaceEdges base)
    (heq : spatialShiftFaceId shift base left =
      spatialShiftFaceId shift base right) :
    left = right := by
  apply boxPlaquetteAt_injective_on_physical hleft hright
  apply spatialShiftPlaquette_injective shift
  rw [← boxPlaquetteAt_spatialShiftFaceId hleft,
    ← boxPlaquetteAt_spatialShiftFaceId hright, heq]

/-- Sharing a lattice link bounds the displacement of every base coordinate
by one.  The existing strict-query geometry only needed the time projection;
shell surjectivity needs all four projections simultaneously. -/
theorem adjacent_all_coordinates_le_add_one
    {left right : Z4Plaq}
    (hadj : z4Chain.toLattice.Adjacent left right) :
    left.1.1 ≤ right.1.1 + 1 ∧
      left.1.2.1 ≤ right.1.2.1 + 1 ∧
      left.1.2.2.1 ≤ right.1.2.2.1 + 1 ∧
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
  change a ≤ e + 1 ∧ b ≤ f + 1 ∧ c ≤ g + 1 ∧ d ≤ h + 1
  cases leftPlane <;> cases rightPlane <;> cases direction <;>
    simp [edgesOf, dirsOf, addE] at hleftMem hrightMem <;>
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- Subtract the known spatial offset, leaving Euclidean time unchanged. -/
def spatialUnshiftVertex (shift : Nat) : Z4Vertex → Z4Vertex
  | (a, b, c, d) => (a - shift, b - shift, c - shift, d)

def spatialUnshiftPlaquette (shift : Nat) : Z4Plaq → Z4Plaq
  | (vertex, plane) => (spatialUnshiftVertex shift vertex, plane)

theorem spatialUnshiftPlaquette_spatialShiftPlaquette
    (shift : Nat) (plaquette : Z4Plaq) :
    spatialUnshiftPlaquette shift
        (spatialShiftPlaquette shift plaquette) = plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp [spatialUnshiftPlaquette, spatialUnshiftVertex,
    spatialShiftPlaquette, spatialShiftVertex]

theorem spatialShiftPlaquette_spatialUnshiftPlaquette
    {shift : Nat} {plaquette : Z4Plaq}
    (ha : shift ≤ plaquette.1.1)
    (hb : shift ≤ plaquette.1.2.1)
    (hc : shift ≤ plaquette.1.2.2.1) :
    spatialShiftPlaquette shift
        (spatialUnshiftPlaquette shift plaquette) = plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  change shift ≤ a at ha
  change shift ≤ b at hb
  change shift ≤ c at hc
  simp [spatialUnshiftPlaquette, spatialUnshiftVertex,
    spatialShiftPlaquette, spatialShiftVertex,
    Nat.sub_add_cancel ha, Nat.sub_add_cancel hb,
    Nat.sub_add_cancel hc]

/-- Any face adjacent to a spatially shifted, two-layer-interior face has a
unique spatial preimage still lying in the source box. -/
theorem spatialUnshiftPlaquette_mem_box_of_adjacent_shifted_margin
    {shift sourceAmbient : Nat} {inside outside : Z4Plaq}
    (hmargin :
      1 ≤ inside.1.1 ∧ inside.1.1 + 2 ≤ sourceAmbient ∧
      1 ≤ inside.1.2.1 ∧ inside.1.2.1 + 2 ≤ sourceAmbient ∧
      1 ≤ inside.1.2.2.1 ∧ inside.1.2.2.1 + 2 ≤ sourceAmbient ∧
      1 ≤ inside.1.2.2.2 ∧ inside.1.2.2.2 + 2 ≤ sourceAmbient)
    (hadj : z4Chain.toLattice.Adjacent
      (spatialShiftPlaquette shift inside) outside) :
    spatialUnshiftPlaquette shift outside ∈
        boxPlaquettes sourceAmbient ∧
      spatialShiftPlaquette shift
        (spatialUnshiftPlaquette shift outside) = outside := by
  have hreverse : z4Chain.toLattice.Adjacent outside
      (spatialShiftPlaquette shift inside) := {
    link := hadj.link
    on_p := hadj.on_q
    on_q := hadj.on_p
  }
  have hforward := adjacent_all_coordinates_le_add_one hadj
  have hbackward := adjacent_all_coordinates_le_add_one hreverse
  obtain ⟨⟨a, b, c, d⟩, insidePlane⟩ := inside
  obtain ⟨⟨e, f, g, h⟩, outsidePlane⟩ := outside
  change 1 ≤ a ∧ a + 2 ≤ sourceAmbient ∧
    1 ≤ b ∧ b + 2 ≤ sourceAmbient ∧
    1 ≤ c ∧ c + 2 ≤ sourceAmbient ∧
    1 ≤ d ∧ d + 2 ≤ sourceAmbient at hmargin
  change a + shift ≤ e + 1 ∧ b + shift ≤ f + 1 ∧
    c + shift ≤ g + 1 ∧ d ≤ h + 1 at hforward
  change e ≤ a + shift + 1 ∧ f ≤ b + shift + 1 ∧
    g ≤ c + shift + 1 ∧ h ≤ d + 1 at hbackward
  have he : shift ≤ e := by omega
  have hf : shift ≤ f := by omega
  have hg : shift ≤ g := by omega
  constructor
  · rw [mem_boxPlaquettes]
    simp only [spatialUnshiftPlaquette, spatialUnshiftVertex]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · exact spatialShiftPlaquette_spatialUnshiftPlaquette he hf hg

/-- Increasing the reflection radius together with positive-time translation
turns the reflected lower query into a purely spatial translate. -/
theorem rawStrictLowerQueryPlaquette_timeShift
    (radius shift : Nat) (plaquette : Z4Plaq) :
    rawStrictLowerQueryPlaquette (radius + shift)
        (timeShiftPlaquette shift plaquette) =
      spatialShiftPlaquette shift
        (rawStrictLowerQueryPlaquette radius plaquette) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp [rawStrictLowerQueryPlaquette, spatialShiftPlaquette,
      spatialShiftVertex,
      timeShiftPlaquette, timeShiftVertex,
      uniformShiftPlaquette, uniformShiftVertex,
      timeReflectPlaquette, centralExtent, Nat.add_assoc] <;>
    omega

private theorem rawStrictLowerQueryPlaquette_map
    (radius : Nat) : ∀ support : List Z4Plaq,
    ((support.map (uniformShiftPlaquette 3)).map
        (uniformShiftPlaquette radius)).map
          (timeReflectPlaquette (centralExtent radius)) =
      support.map (rawStrictLowerQueryPlaquette radius)
  | [] => rfl
  | plaquette :: rest => by
      change
        rawStrictLowerQueryPlaquette radius plaquette ::
            (((rest.map (uniformShiftPlaquette 3)).map
              (uniformShiftPlaquette radius)).map
                (timeReflectPlaquette (centralExtent radius))) =
          rawStrictLowerQueryPlaquette radius plaquette ::
            rest.map (rawStrictLowerQueryPlaquette radius)
      exact congrArg (List.cons
        (rawStrictLowerQueryPlaquette radius plaquette))
        (rawStrictLowerQueryPlaquette_map radius rest)

private theorem sameSupport_map_query_local
    {X Y : List Z4Plaq} (mapP : Z4Plaq → Z4Plaq)
    (h : sameSupport (L := z4Chain.toLattice) X Y) :
    sameSupport (L := z4Chain.toLattice)
      (X.map mapP) (Y.map mapP) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr ⟨source, h.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr ⟨source, h.2 source hsource, rfl⟩

private theorem sameSupport_right_congr_query_local
    {X Y Z : List Z4Plaq}
    (h : sameSupport (L := z4Chain.toLattice) X Y)
    (heq : Y = Z) :
    sameSupport (L := z4Chain.toLattice) X Z := by
  cases heq
  exact h

/-- A strict lower canonical query is exactly the canonical re-encoding of
the raw translate-then-reflect operation on the original source root. -/
theorem centralStrictLowerCanonicalRoot_raw_sameSupport
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient radius)
        (centralStrictLowerCanonicalRoot radius base root))
      ((geometricPolymer base root).map
        (rawStrictLowerQueryPlaquette radius)) := by
  have hsource := uniformShiftCanonicalRoot_sameSupport
    (padding := 3) hroot
  have hupper := centralFaceQueryCanonicalRoot_sameSupport hbase
    (strictQuerySourceRoot_canonical hroot)
  have hupperRaw := sameSupport_trans hupper
    (sameSupport_map_query_local (uniformShiftPlaquette radius) hsource)
  have hsupported := centralStrictUpperCanonicalRoot_supported hbase hroot
  have hlower := centralReflectedCanonicalRoot_sameSupport hsupported
  have hlowerRaw := sameSupport_trans hlower
    (sameSupport_map_query_local
      (timeReflectPlaquette (centralExtent radius)) hupperRaw)
  apply sameSupport_right_congr_query_local hlowerRaw
  exact rawStrictLowerQueryPlaquette_map radius
    (geometricPolymer base root)

/-- The reflected strict root remains two full coordinate layers inside its
ambient box in every direction.  This is stronger than the previously needed
strict-time-side estimate and is precisely the margin consumed by the
complete exterior query shell. -/
theorem centralStrictLowerCanonicalRoot_full_margin
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ centralStrictLowerCanonicalRoot radius base root) :
    let plaquette := boxPlaquetteAt (centralAmbient radius) face
    1 ≤ plaquette.1.1 ∧
      plaquette.1.1 + 2 ≤ centralAmbient radius ∧
      1 ≤ plaquette.1.2.1 ∧
      plaquette.1.2.1 + 2 ≤ centralAmbient radius ∧
      1 ≤ plaquette.1.2.2.1 ∧
      plaquette.1.2.2.1 + 2 ≤ centralAmbient radius ∧
      1 ≤ plaquette.1.2.2.2 ∧
      plaquette.1.2.2.2 + 2 ≤ centralAmbient radius := by
  have hgeom : boxPlaquetteAt (centralAmbient radius) face ∈
      geometricPolymer (centralAmbient radius)
        (centralStrictLowerCanonicalRoot radius base root) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hraw :=
    (centralStrictLowerCanonicalRoot_raw_sameSupport hbase hroot).1
      _ hgeom
  obtain ⟨source, hsource, heq⟩ :=
    decodeMapMember (rawStrictLowerQueryPlaquette radius)
      (geometricPolymer base root)
      (boxPlaquetteAt (centralAmbient radius) face) hraw
  have hsourceBox : source ∈ boxPlaquettes base :=
    geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource
  rw [← heq]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  rw [mem_boxPlaquettes] at hsourceBox
  change a < base ∧ b < base ∧ c < base ∧ d < base at hsourceBox
  unfold strictQueryBase uniformPaddedBase at hbase
  cases plane <;>
    dsimp [rawStrictLowerQueryPlaquette,
      uniformShiftPlaquette, uniformShiftVertex,
      timeReflectPlaquette, centralAmbient, centralExtent]
  all_goals
    exact ⟨by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega⟩

/-- After shifting both source time and reflection radius, the entire lower
canonical root is the same geometric support as the spatial translate of the
original lower canonical root. -/
theorem centralStrictLowerCanonicalRoot_timeShift_sameSupport
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient (radius + shift))
        (centralStrictLowerCanonicalRoot (radius + shift) (base + shift)
          (timeShiftCanonicalRoot shift base root)))
      ((geometricPolymer (centralAmbient radius)
          (centralStrictLowerCanonicalRoot radius base root)).map
        (spatialShiftPlaquette shift)) := by
  have hbaseShift : strictQueryBase (base + shift) ≤ radius + shift := by
    unfold strictQueryBase uniformPaddedBase at hbase ⊢
    omega
  have htranslatedCanonical := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetRaw := centralStrictLowerCanonicalRoot_raw_sameSupport
    hbaseShift htranslatedCanonical
  have htime := timeShiftCanonicalRoot_sameSupport
    (shift := shift) hroot
  have htimeRaw := sameSupport_map_query_local
    (rawStrictLowerQueryPlaquette (radius + shift)) htime
  have htargetOriginal := sameSupport_trans htargetRaw htimeRaw
  have hsourceRaw := centralStrictLowerCanonicalRoot_raw_sameSupport
    hbase hroot
  have hsourceShifted := sameSupport_map_query_local
    (spatialShiftPlaquette shift) hsourceRaw
  refine sameSupport_trans htargetOriginal ?_
  refine sameSupport_trans ?_ (sameSupport_symm hsourceShifted)
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, hplaquetteEq⟩ :=
      List.mem_map.mp hplaquette
    obtain ⟨original, horiginal, hsourceEq⟩ :=
      List.mem_map.mp hsource
    rw [← hplaquetteEq, ← hsourceEq,
      rawStrictLowerQueryPlaquette_timeShift]
    exact List.mem_map.mpr
      ⟨rawStrictLowerQueryPlaquette radius original,
        List.mem_map.mpr ⟨original, horiginal, rfl⟩, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, hplaquetteEq⟩ :=
      List.mem_map.mp hplaquette
    obtain ⟨original, horiginal, hsourceEq⟩ :=
      List.mem_map.mp hsource
    rw [← hplaquetteEq, ← hsourceEq,
      ← rawStrictLowerQueryPlaquette_timeShift]
    exact List.mem_map.mpr
      ⟨timeShiftPlaquette shift original,
        List.mem_map.mpr ⟨original, horiginal, rfl⟩, rfl⟩

theorem uniformPaddedBase_centralAmbient
    (radius shift : Nat) :
    uniformPaddedBase shift (centralAmbient radius) =
      centralAmbient (radius + shift) := by
  unfold uniformPaddedBase centralAmbient centralExtent
  omega

/-- Numerical membership form of the radius-shifted root covariance.  It
does not assume that canonical enumeration order is preserved: every target
identifier is characterized by the constructive spatial face reindex. -/
theorem mem_centralStrictLowerCanonicalRoot_timeShift_iff
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (targetFace : Nat) :
    targetFace ∈
        centralStrictLowerCanonicalRoot (radius + shift) (base + shift)
          (timeShiftCanonicalRoot shift base root) ↔
      ∃ sourceFace,
        sourceFace ∈ centralStrictLowerCanonicalRoot radius base root ∧
          targetFace = spatialShiftFaceId shift
            (centralAmbient radius) sourceFace := by
  let sourceRoot := centralStrictLowerCanonicalRoot radius base root
  let targetRoot :=
    centralStrictLowerCanonicalRoot (radius + shift) (base + shift)
      (timeShiftCanonicalRoot shift base root)
  have hsourceCanonical : sourceRoot ∈
      canonicalSurfacePolymers (centralAmbient radius) :=
    centralStrictLowerCanonicalRoot_canonical hbase hroot
  have hbaseShift : strictQueryBase (base + shift) ≤ radius + shift := by
    unfold strictQueryBase uniformPaddedBase at hbase ⊢
    omega
  have htranslatedCanonical := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetCanonical : targetRoot ∈
      canonicalSurfacePolymers (centralAmbient (radius + shift)) :=
    centralStrictLowerCanonicalRoot_canonical hbaseShift
      htranslatedCanonical
  have hsame : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient (radius + shift)) targetRoot)
      ((geometricPolymer (centralAmbient radius) sourceRoot).map
        (spatialShiftPlaquette shift)) :=
    centralStrictLowerCanonicalRoot_timeShift_sameSupport
      hbase hroot
  constructor
  · intro htarget
    have htargetPhysical : targetFace ∈
        physicalFaceEdges (centralAmbient (radius + shift)) :=
      mem_of_mem_sublists _ targetRoot
        (canonicalSurfacePolymer_mem_faceSupports htargetCanonical)
        targetFace htarget
    have htargetGeom : boxPlaquetteAt
          (centralAmbient (radius + shift)) targetFace ∈
        geometricPolymer (centralAmbient (radius + shift)) targetRoot :=
      List.mem_map.mpr ⟨targetFace, htarget, rfl⟩
    obtain ⟨sourcePlaquette, hsourcePlaquette, htargetEq⟩ :=
      decodeMapMember (spatialShiftPlaquette shift)
        (geometricPolymer (centralAmbient radius) sourceRoot)
        (boxPlaquetteAt (centralAmbient (radius + shift)) targetFace)
        (hsame.1 _ htargetGeom)
    obtain ⟨sourceFace, hsourceFace, hsourceEq⟩ :=
      decodeMapMember (boxPlaquetteAt (centralAmbient radius))
        sourceRoot sourcePlaquette hsourcePlaquette
    have hsourcePhysical : sourceFace ∈
        physicalFaceEdges (centralAmbient radius) :=
      mem_of_mem_sublists _ sourceRoot
        (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical)
        sourceFace hsourceFace
    have hmappedPhysical := spatialShiftFaceId_physical
      (shift := shift) hsourcePhysical
    have hmappedPhysical' : spatialShiftFaceId shift
          (centralAmbient radius) sourceFace ∈
        physicalFaceEdges (centralAmbient (radius + shift)) := by
      rw [← uniformPaddedBase_centralAmbient radius shift]
      exact hmappedPhysical
    refine ⟨sourceFace, hsourceFace, ?_⟩
    apply boxPlaquetteAt_injective_on_physical
      htargetPhysical hmappedPhysical'
    rw [← uniformPaddedBase_centralAmbient radius shift,
      boxPlaquetteAt_spatialShiftFaceId hsourcePhysical]
    have hcoordinate := htargetEq.symm
    rw [← hsourceEq,
      ← uniformPaddedBase_centralAmbient radius shift] at hcoordinate
    exact hcoordinate
  · rintro ⟨sourceFace, hsourceFace, rfl⟩
    have hsourcePhysical : sourceFace ∈
        physicalFaceEdges (centralAmbient radius) :=
      mem_of_mem_sublists _ sourceRoot
        (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical)
        sourceFace hsourceFace
    have hsourceGeom : boxPlaquetteAt (centralAmbient radius) sourceFace ∈
        geometricPolymer (centralAmbient radius) sourceRoot :=
      List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
    have hshiftedGeom : spatialShiftPlaquette shift
          (boxPlaquetteAt (centralAmbient radius) sourceFace) ∈
        (geometricPolymer (centralAmbient radius) sourceRoot).map
          (spatialShiftPlaquette shift) :=
      List.mem_map.mpr
        ⟨boxPlaquetteAt (centralAmbient radius) sourceFace,
          hsourceGeom, rfl⟩
    have htargetGeom := hsame.2 _ hshiftedGeom
    obtain ⟨foundFace, hfoundFace, hfoundEq⟩ :=
      decodeMapMember
        (boxPlaquetteAt (centralAmbient (radius + shift)))
        targetRoot
        (spatialShiftPlaquette shift
          (boxPlaquetteAt (centralAmbient radius) sourceFace))
        htargetGeom
    have hfoundPhysical : foundFace ∈
        physicalFaceEdges (centralAmbient (radius + shift)) :=
      mem_of_mem_sublists _ targetRoot
        (canonicalSurfacePolymer_mem_faceSupports htargetCanonical)
        foundFace hfoundFace
    have hmappedPhysical := spatialShiftFaceId_physical
      (shift := shift) hsourcePhysical
    have hmappedPhysical' : spatialShiftFaceId shift
          (centralAmbient radius) sourceFace ∈
        physicalFaceEdges (centralAmbient (radius + shift)) := by
      rw [← uniformPaddedBase_centralAmbient radius shift]
      exact hmappedPhysical
    have hid : foundFace = spatialShiftFaceId shift
        (centralAmbient radius) sourceFace := by
      apply boxPlaquetteAt_injective_on_physical
        hfoundPhysical hmappedPhysical'
      have hmappedEq := boxPlaquetteAt_spatialShiftFaceId
        (shift := shift) hsourcePhysical
      rw [uniformPaddedBase_centralAmbient radius shift] at hmappedEq
      rw [hmappedEq]
      exact hfoundEq
    simpa only [← hid] using hfoundFace

/-- The complete one-link exterior shell, not merely the marked root, is
transported bijectively by the constructive spatial face reindex.  The
reverse direction spends exactly one of the two certified margin layers. -/
theorem mem_centralStrictLowerExterior_timeShift_iff
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (targetFace : Nat) :
    targetFace ∈ canonicalPolymerExteriorFaceQueries
        (centralAmbient (radius + shift))
        (centralStrictLowerCanonicalRoot (radius + shift) (base + shift)
          (timeShiftCanonicalRoot shift base root)) ↔
      ∃ sourceFace,
        sourceFace ∈ canonicalPolymerExteriorFaceQueries
            (centralAmbient radius)
            (centralStrictLowerCanonicalRoot radius base root) ∧
          targetFace = spatialShiftFaceId shift
            (centralAmbient radius) sourceFace := by
  let sourceRoot := centralStrictLowerCanonicalRoot radius base root
  let targetRoot :=
    centralStrictLowerCanonicalRoot (radius + shift) (base + shift)
      (timeShiftCanonicalRoot shift base root)
  have hsourceCanonical : sourceRoot ∈
      canonicalSurfacePolymers (centralAmbient radius) :=
    centralStrictLowerCanonicalRoot_canonical hbase hroot
  have hbaseShift : strictQueryBase (base + shift) ≤ radius + shift := by
    unfold strictQueryBase uniformPaddedBase at hbase ⊢
    omega
  have htranslatedCanonical := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetCanonical : targetRoot ∈
      canonicalSurfacePolymers (centralAmbient (radius + shift)) :=
    centralStrictLowerCanonicalRoot_canonical hbaseShift
      htranslatedCanonical
  have hrootTransport (face : Nat) :
      face ∈ targetRoot ↔
        ∃ sourceFace, sourceFace ∈ sourceRoot ∧
          face = spatialShiftFaceId shift
            (centralAmbient radius) sourceFace := by
    simpa only [sourceRoot, targetRoot] using
      (mem_centralStrictLowerCanonicalRoot_timeShift_iff
        (shift := shift) hbase hroot face)
  constructor
  · intro htargetExterior
    obtain ⟨htargetPhysical, htargetOutside, targetInside,
        htargetInside, hadjTargetB⟩ :=
      (mem_canonicalPolymerExteriorFaceQueries_iff
        (centralAmbient (radius + shift)) targetRoot targetFace).1
        htargetExterior
    obtain ⟨sourceInside, hsourceInside, hinsideId⟩ :=
      (hrootTransport targetInside).1 htargetInside
    have hsourceInsidePhysical : sourceInside ∈
        physicalFaceEdges (centralAmbient radius) :=
      mem_of_mem_sublists _ sourceRoot
        (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical)
        sourceInside hsourceInside
    have hinsideCoordinate :
        boxPlaquetteAt (centralAmbient (radius + shift)) targetInside =
          spatialShiftPlaquette shift
            (boxPlaquetteAt (centralAmbient radius) sourceInside) := by
      rw [hinsideId]
      have hcoordinate := boxPlaquetteAt_spatialShiftFaceId
        (shift := shift) hsourceInsidePhysical
      rw [uniformPaddedBase_centralAmbient radius shift] at hcoordinate
      exact hcoordinate
    have hadjTarget := actualAdjacentOfFaceLinkAdjacent hadjTargetB
    rw [hinsideCoordinate] at hadjTarget
    have hinsideMargin :=
      centralStrictLowerCanonicalRoot_full_margin
        hbase hroot hsourceInside
    have hpreimage :=
      spatialUnshiftPlaquette_mem_box_of_adjacent_shifted_margin
        hinsideMargin hadjTarget
    obtain ⟨hsourceOutsideBox, hroundtrip⟩ := hpreimage
    obtain ⟨sourceFace, hsourceIndexed⟩ :=
      exists_mem_enumerate hsourceOutsideBox
    have hsourcePhysical : sourceFace ∈
        physicalFaceEdges (centralAmbient radius) := by
      unfold physicalFaceEdges plaquetteEdgeCount
      exact List.mem_range.mpr (enumerate_index_lt hsourceIndexed)
    have hsourceCoordinate :
        boxPlaquetteAt (centralAmbient radius) sourceFace =
          spatialUnshiftPlaquette shift
            (boxPlaquetteAt (centralAmbient (radius + shift)) targetFace) :=
      boxPlaquetteAt_eq_of_enumerate hsourceIndexed
    have hmappedCoordinate :
        boxPlaquetteAt (centralAmbient (radius + shift))
            (spatialShiftFaceId shift (centralAmbient radius) sourceFace) =
          boxPlaquetteAt (centralAmbient (radius + shift)) targetFace := by
      have hcoordinate := boxPlaquetteAt_spatialShiftFaceId
        (shift := shift) hsourcePhysical
      rw [uniformPaddedBase_centralAmbient radius shift] at hcoordinate
      rw [hcoordinate, hsourceCoordinate, hroundtrip]
    have hmappedPhysical : spatialShiftFaceId shift
          (centralAmbient radius) sourceFace ∈
        physicalFaceEdges (centralAmbient (radius + shift)) := by
      rw [← uniformPaddedBase_centralAmbient radius shift]
      exact spatialShiftFaceId_physical hsourcePhysical
    have htargetId : targetFace = spatialShiftFaceId shift
        (centralAmbient radius) sourceFace := by
      apply boxPlaquetteAt_injective_on_physical
        htargetPhysical hmappedPhysical
      exact hmappedCoordinate.symm
    have hsourceOutside : sourceFace ∉ sourceRoot := by
      intro hsourceRoot
      have hmappedRoot :=
        (hrootTransport
          (spatialShiftFaceId shift
            (centralAmbient radius) sourceFace)).2
          ⟨sourceFace, hsourceRoot, rfl⟩
      rw [← htargetId] at hmappedRoot
      exact htargetOutside hmappedRoot
    have houtsideCoordinate :
        spatialShiftPlaquette shift
            (boxPlaquetteAt (centralAmbient radius) sourceFace) =
          boxPlaquetteAt (centralAmbient (radius + shift)) targetFace := by
      rw [hsourceCoordinate, hroundtrip]
    have hadjShifted : z4Chain.toLattice.Adjacent
        (spatialShiftPlaquette shift
          (boxPlaquetteAt (centralAmbient radius) sourceInside))
        (spatialShiftPlaquette shift
          (boxPlaquetteAt (centralAmbient radius) sourceFace)) := by
      rw [houtsideCoordinate]
      exact hadjTarget
    have hadjSource :=
      spatialUnshiftAdjacentOfShifted shift hadjShifted
    have hadjSourceB : faceLinkAdjacentB (centralAmbient radius)
        sourceInside sourceFace = true :=
      faceLinkAdjacentB_true_of_actualAdjacent
        hsourceInsidePhysical hsourcePhysical hadjSource
    have hsourceExterior : sourceFace ∈
        canonicalPolymerExteriorFaceQueries
          (centralAmbient radius) sourceRoot :=
      (mem_canonicalPolymerExteriorFaceQueries_iff
        (centralAmbient radius) sourceRoot sourceFace).2
        ⟨hsourcePhysical, hsourceOutside, sourceInside,
          hsourceInside, hadjSourceB⟩
    exact ⟨sourceFace, hsourceExterior, htargetId⟩
  · rintro ⟨sourceFace, hsourceExterior, rfl⟩
    obtain ⟨hsourcePhysical, hsourceOutside, sourceInside,
        hsourceInside, hadjSourceB⟩ :=
      (mem_canonicalPolymerExteriorFaceQueries_iff
        (centralAmbient radius) sourceRoot sourceFace).1
        hsourceExterior
    have hsourceInsidePhysical : sourceInside ∈
        physicalFaceEdges (centralAmbient radius) :=
      mem_of_mem_sublists _ sourceRoot
        (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical)
        sourceInside hsourceInside
    have hmappedPhysical : spatialShiftFaceId shift
          (centralAmbient radius) sourceFace ∈
        physicalFaceEdges (centralAmbient (radius + shift)) := by
      rw [← uniformPaddedBase_centralAmbient radius shift]
      exact spatialShiftFaceId_physical hsourcePhysical
    have hmappedInsidePhysical : spatialShiftFaceId shift
          (centralAmbient radius) sourceInside ∈
        physicalFaceEdges (centralAmbient (radius + shift)) := by
      rw [← uniformPaddedBase_centralAmbient radius shift]
      exact spatialShiftFaceId_physical hsourceInsidePhysical
    have hmappedInsideRoot : spatialShiftFaceId shift
          (centralAmbient radius) sourceInside ∈ targetRoot :=
      (hrootTransport
        (spatialShiftFaceId shift
          (centralAmbient radius) sourceInside)).2
        ⟨sourceInside, hsourceInside, rfl⟩
    have hmappedOutside : spatialShiftFaceId shift
          (centralAmbient radius) sourceFace ∉ targetRoot := by
      intro hmappedRoot
      obtain ⟨sourceOther, hsourceOther, hidOther⟩ :=
        (hrootTransport
          (spatialShiftFaceId shift
            (centralAmbient radius) sourceFace)).1 hmappedRoot
      have hsourceOtherPhysical : sourceOther ∈
          physicalFaceEdges (centralAmbient radius) :=
        mem_of_mem_sublists _ sourceRoot
          (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical)
          sourceOther hsourceOther
      have hidSource : sourceFace = sourceOther :=
        spatialShiftFaceId_injective_on_physical
          (shift := shift) hsourcePhysical hsourceOtherPhysical hidOther
      exact hsourceOutside (by simpa only [hidSource] using hsourceOther)
    have hadjSource := actualAdjacentOfFaceLinkAdjacent hadjSourceB
    have hadjShifted := spatialShiftAdjacent shift hadjSource
    have hinsideCoordinate := boxPlaquetteAt_spatialShiftFaceId
      (shift := shift) hsourceInsidePhysical
    have houtsideCoordinate := boxPlaquetteAt_spatialShiftFaceId
      (shift := shift) hsourcePhysical
    rw [uniformPaddedBase_centralAmbient radius shift] at hinsideCoordinate
    rw [uniformPaddedBase_centralAmbient radius shift] at houtsideCoordinate
    have hadjTarget : z4Chain.toLattice.Adjacent
        (boxPlaquetteAt (centralAmbient (radius + shift))
          (spatialShiftFaceId shift
            (centralAmbient radius) sourceInside))
        (boxPlaquetteAt (centralAmbient (radius + shift))
          (spatialShiftFaceId shift
            (centralAmbient radius) sourceFace)) := by
      rw [hinsideCoordinate, houtsideCoordinate]
      exact hadjShifted
    have hadjTargetB : faceLinkAdjacentB
        (centralAmbient (radius + shift))
        (spatialShiftFaceId shift (centralAmbient radius) sourceInside)
        (spatialShiftFaceId shift (centralAmbient radius) sourceFace) = true :=
      faceLinkAdjacentB_true_of_actualAdjacent
        hmappedInsidePhysical hmappedPhysical hadjTarget
    exact (mem_canonicalPolymerExteriorFaceQueries_iff
      (centralAmbient (radius + shift)) targetRoot
      (spatialShiftFaceId shift
        (centralAmbient radius) sourceFace)).2
      ⟨hmappedPhysical, hmappedOutside,
        spatialShiftFaceId shift (centralAmbient radius) sourceInside,
        hmappedInsideRoot, hadjTargetB⟩

/-! ## 3. A simultaneous finite-support query intertwiner -/

/-- Pull a finite target support back along a coordinate renaming, restricted
to the specified finite source domain. -/
def finiteSupportPreimage
    (domain : List Nat) (rename : Nat → Nat)
    (targetSupport : List Nat) : List Nat :=
  domain.filter (fun source => memberB targetSupport (rename source))

theorem memberB_finiteSupportPreimage
    (domain : List Nat) (rename : Nat → Nat)
    (targetSupport : List Nat) {source : Nat}
    (hsource : source ∈ domain) :
    memberB (finiteSupportPreimage domain rename targetSupport) source =
      memberB targetSupport (rename source) := by
  apply Bool.eq_iff_iff.mpr
  simp [finiteSupportPreimage, hsource]

private theorem listAll_map_eq_of_pointwise
    {A B : Type} (rename : A → B)
    (left : B → Bool) (right : A → Bool) :
    ∀ xs : List A,
      (∀ item, item ∈ xs → left (rename item) = right item) →
      (xs.map rename).all left = xs.all right
  | [], _ => rfl
  | item :: rest, hpointwise => by
      simp only [List.map_cons, List.all_cons]
      rw [hpointwise item List.mem_cons_self]
      rw [listAll_map_eq_of_pointwise rename left right rest
        (fun target htarget => hpointwise target
          (List.mem_cons_of_mem item htarget))]

private theorem listAll_eq_of_mem_iff
    {A : Type} (xs ys : List A) (predicate : A → Bool)
    (hmem : ∀ item, item ∈ xs ↔ item ∈ ys) :
    xs.all predicate = ys.all predicate := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro hall item hitem
    exact hall item ((hmem item).2 hitem)
  · intro hall item hitem
    exact hall item ((hmem item).1 hitem)

/-- Order-independent support-query transport.  Canonical re-encoding may
permute numerical identifiers, so the correct interface is membership
bijection of both the root and its complete shell, not literal list equality. -/
theorem canonicalPolymerSupportQueryEventB_finiteSupportPreimage_of_mem_iff
    (sourceAmbient targetAmbient : Nat)
    (domain : List Nat) (rename : Nat → Nat)
    (sourceRoot targetRoot targetSupport : List Nat)
    (hrootDomain : ∀ face, face ∈ sourceRoot → face ∈ domain)
    (hexteriorDomain : ∀ face,
      face ∈ canonicalPolymerExteriorFaceQueries
        sourceAmbient sourceRoot → face ∈ domain)
    (hroot : ∀ face, face ∈ targetRoot ↔
      ∃ sourceFace, sourceFace ∈ sourceRoot ∧
        face = rename sourceFace)
    (hexterior : ∀ face,
      face ∈ canonicalPolymerExteriorFaceQueries
          targetAmbient targetRoot ↔
        ∃ sourceFace,
          sourceFace ∈ canonicalPolymerExteriorFaceQueries
            sourceAmbient sourceRoot ∧
          face = rename sourceFace) :
    canonicalPolymerSupportQueryEventB targetAmbient
        targetRoot targetSupport =
      canonicalPolymerSupportQueryEventB sourceAmbient sourceRoot
        (finiteSupportPreimage domain rename targetSupport) := by
  have hrootMem : ∀ face,
      face ∈ targetRoot ↔ face ∈ sourceRoot.map rename := by
    intro face
    rw [hroot face]
    constructor
    · rintro ⟨sourceFace, hsourceFace, heq⟩
      exact List.mem_map.mpr ⟨sourceFace, hsourceFace, heq.symm⟩
    · intro hmapped
      obtain ⟨sourceFace, hsourceFace, heq⟩ := List.mem_map.mp hmapped
      exact ⟨sourceFace, hsourceFace, heq.symm⟩
  have hexteriorMem : ∀ face,
      face ∈ canonicalPolymerExteriorFaceQueries
          targetAmbient targetRoot ↔
        face ∈ (canonicalPolymerExteriorFaceQueries
          sourceAmbient sourceRoot).map rename := by
    intro face
    rw [hexterior face]
    constructor
    · rintro ⟨sourceFace, hsourceFace, heq⟩
      exact List.mem_map.mpr ⟨sourceFace, hsourceFace, heq.symm⟩
    · intro hmapped
      obtain ⟨sourceFace, hsourceFace, heq⟩ := List.mem_map.mp hmapped
      exact ⟨sourceFace, hsourceFace, heq.symm⟩
  have hinternalTarget : targetRoot.all (memberB targetSupport) =
      (sourceRoot.map rename).all (memberB targetSupport) :=
    listAll_eq_of_mem_iff _ _ _ hrootMem
  have hinternalMapped :
      (sourceRoot.map rename).all (memberB targetSupport) =
        sourceRoot.all
          (memberB (finiteSupportPreimage domain rename targetSupport)) := by
    apply listAll_map_eq_of_pointwise
    intro face hface
    exact (memberB_finiteSupportPreimage
      domain rename targetSupport (hrootDomain face hface)).symm
  have hexteriorTarget :
      (canonicalPolymerExteriorFaceQueries
          targetAmbient targetRoot).all
          (fun face => !(memberB targetSupport face)) =
        ((canonicalPolymerExteriorFaceQueries
          sourceAmbient sourceRoot).map rename).all
          (fun face => !(memberB targetSupport face)) :=
    listAll_eq_of_mem_iff _ _ _ hexteriorMem
  have hexteriorMapped :
      ((canonicalPolymerExteriorFaceQueries
          sourceAmbient sourceRoot).map rename).all
          (fun face => !(memberB targetSupport face)) =
        (canonicalPolymerExteriorFaceQueries
          sourceAmbient sourceRoot).all
          (fun face =>
            !(memberB
              (finiteSupportPreimage domain rename targetSupport) face)) := by
    apply listAll_map_eq_of_pointwise
    intro face hface
    exact congrArg Bool.not
      (memberB_finiteSupportPreimage
        domain rename targetSupport
        (hexteriorDomain face hface)).symm
  unfold canonicalPolymerSupportQueryEventB
  rw [hinternalTarget, hinternalMapped,
    hexteriorTarget, hexteriorMapped]

/-- Ambient occupied-face support pulled back through the constructive
spatial reindex. -/
def spatialPullbackAmbientSupport
    (radius shift : Nat) (targetSupport : List Nat) : List Nat :=
  finiteSupportPreimage (physicalFaceEdges (centralAmbient radius))
    (spatialShiftFaceId shift (centralAmbient radius)) targetSupport

theorem spatialPullbackAmbientSupport_mem_cutoffOneFaceSupports
    (radius shift : Nat) (targetSupport : List Nat) :
    spatialPullbackAmbientSupport radius shift targetSupport ∈
      cutoffOneFaceSupports (centralAmbient radius) := by
  unfold spatialPullbackAmbientSupport finiteSupportPreimage
    cutoffOneFaceSupports
  exact filter_mem_sublists _ _

/-- Exact complete-root-and-shell transport for one strict lower query bit. -/
theorem centralStrictLowerSupportQueryEventB_timeShift
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (targetSupport : List Nat) :
    canonicalPolymerSupportQueryEventB
        (centralAmbient (radius + shift))
        (centralStrictLowerCanonicalRoot (radius + shift) (base + shift)
          (timeShiftCanonicalRoot shift base root)) targetSupport =
      canonicalPolymerSupportQueryEventB (centralAmbient radius)
        (centralStrictLowerCanonicalRoot radius base root)
        (spatialPullbackAmbientSupport radius shift targetSupport) := by
  unfold spatialPullbackAmbientSupport
  apply canonicalPolymerSupportQueryEventB_finiteSupportPreimage_of_mem_iff
  · intro face hface
    have hcanonical := centralStrictLowerCanonicalRoot_canonical hbase hroot
    exact mem_of_mem_sublists _ _
      (canonicalSurfacePolymer_mem_faceSupports hcanonical) face hface
  · intro face hface
    exact (mem_canonicalPolymerExteriorFaceQueries_iff
      (centralAmbient radius)
      (centralStrictLowerCanonicalRoot radius base root) face).1 hface |>.1
  · intro face
    exact mem_centralStrictLowerCanonicalRoot_timeShift_iff
      (shift := shift) hbase hroot face
  · intro face
    exact mem_centralStrictLowerExterior_timeShift_iff
      (shift := shift) hbase hroot face

/-- Simultaneous query transport for an arbitrary finite family of roots.  A
single ambient pullback support is shared by all coordinates. -/
theorem centralStrictLowerCylinderFingerprint_timeShift
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (targetSupport : List Nat) :
    canonicalRootsSupportQueryFingerprint
        (centralAmbient (radius + shift))
        (centralStrictLowerCylinderRoots (radius + shift) (base + shift)
          (roots.map (timeShiftCanonicalRoot shift base)))
        targetSupport =
      canonicalRootsSupportQueryFingerprint (centralAmbient radius)
        (centralStrictLowerCylinderRoots radius base roots)
        (spatialPullbackAmbientSupport radius shift targetSupport) := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
      simp only [List.map_cons, centralStrictLowerCylinderRoots,
        canonicalRootsSupportQueryFingerprint]
      rw [centralStrictLowerSupportQueryEventB_timeShift
        hbase (hroots root List.mem_cons_self) targetSupport]
      have htail := ih
        (fun item hitem => hroots item
          (List.mem_cons_of_mem root hitem))
      simpa only [centralStrictLowerCylinderRoots,
        canonicalRootsSupportQueryFingerprint] using congrArg
          (List.cons
            (canonicalPolymerSupportQueryEventB
              (centralAmbient radius)
              (centralStrictLowerCanonicalRoot radius base root)
              (spatialPullbackAmbientSupport
                radius shift targetSupport))) htail

/-- Reconstruct the pulled-back ambient support as a genuine complete
lower-half support coordinate at the source radius. -/
def centralSpatialPullbackLowerSupport
    (radius shift : Nat) (targetAmbientSupport : List Nat) : List Nat :=
  centralHalfSupportCode radius
    (centralLowerRestriction radius
      (ambientToSlabPhysical (centralExtent radius)
        (componentLabel
          (spatialPullbackAmbientSupport
            radius shift targetAmbientSupport))))

theorem centralSpatialPullbackLowerSupport_mem
    (radius shift : Nat) (targetAmbientSupport : List Nat) :
    centralSpatialPullbackLowerSupport radius shift targetAmbientSupport ∈
      centralHalfSupportSpace radius := by
  unfold centralSpatialPullbackLowerSupport
  exact centralHalfSupportCode_mem _ _

/-- The reconstructed lower coordinate reads exactly the pulled-back ambient
support on every strict root and every face in its complete exterior shell. -/
theorem centralStrictLowerCylinderFingerprint_pullback_reconstruct
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (targetAmbientSupport : List Nat) :
    centralLowerSupportQueryFingerprint radius
        (centralStrictLowerCylinderRoots radius base roots)
        (centralSpatialPullbackLowerSupport
          radius shift targetAmbientSupport) =
      canonicalRootsSupportQueryFingerprint (centralAmbient radius)
        (centralStrictLowerCylinderRoots radius base roots)
        (spatialPullbackAmbientSupport
          radius shift targetAmbientSupport) := by
  have hdecode := centralLowerSupportQueryFingerprint_physical
    radius (centralStrictLowerCylinderRoots radius base roots)
      (componentLabel
        (spatialPullbackAmbientSupport
          radius shift targetAmbientSupport))
      (centralStrictLowerCylinderRoots_canonical hbase hroots)
      (centralStrictLowerCylinderRoots_internal_side hbase hroots)
      (centralStrictLowerCylinderRoots_exterior_side hbase hroots)
  rw [excitedPlaquetteIds_componentLabel_eq_support
    (spatialPullbackAmbientSupport_mem_cutoffOneFaceSupports
      radius shift targetAmbientSupport)] at hdecode
  simpa only [centralSpatialPullbackLowerSupport] using hdecode

/-- Exact simultaneous complete-lower-support query intertwiner for positive
time translation.  This is the missing code-level statement: the translated
chart at radius `radius + shift` is evaluated on an arbitrary target lower
support, and the same Boolean code is obtained from one constructively
reconstructed source lower support shared by all roots. -/
theorem centralStrictLocalQueryCode_timeShift_completeLowerSupport
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (targetSupport : List Nat) :
    centralStrictLocalQueryCode (radius + shift) (base + shift)
        (roots.map (timeShiftCanonicalRoot shift base)) targetSupport =
      centralStrictLocalQueryCode radius base roots
        (centralSpatialPullbackLowerSupport radius shift
          (centralLowerSupportAmbientFaces
            (radius + shift) targetSupport)) := by
  unfold centralStrictLocalQueryCode
  change canonicalRootsSupportQueryFingerprint
      (centralAmbient (radius + shift))
      (centralStrictLowerCylinderRoots (radius + shift) (base + shift)
        (roots.map (timeShiftCanonicalRoot shift base)))
      (centralLowerSupportAmbientFaces (radius + shift) targetSupport) =
    centralLowerSupportQueryFingerprint radius
      (centralStrictLowerCylinderRoots radius base roots)
      (centralSpatialPullbackLowerSupport radius shift
        (centralLowerSupportAmbientFaces (radius + shift) targetSupport))
  rw [centralStrictLowerCylinderFingerprint_timeShift
    (shift := shift) hbase hroots
      (centralLowerSupportAmbientFaces (radius + shift) targetSupport)]
  exact (centralStrictLowerCylinderFingerprint_pullback_reconstruct
    (shift := shift) hbase hroots
      (centralLowerSupportAmbientFaces
        (radius + shift) targetSupport)).symm

/-- A single local support-query bit is transported exactly when the root and
its complete one-link exterior shell are renamed together. -/
theorem canonicalPolymerSupportQueryEventB_finiteSupportPreimage
    (sourceAmbient targetAmbient : Nat)
    (domain : List Nat) (rename : Nat → Nat)
    (sourceRoot targetSupport : List Nat)
    (hrootDomain : ∀ face, face ∈ sourceRoot → face ∈ domain)
    (hexteriorDomain : ∀ face,
      face ∈ canonicalPolymerExteriorFaceQueries
        sourceAmbient sourceRoot → face ∈ domain)
    (hexterior :
      canonicalPolymerExteriorFaceQueries targetAmbient
          (sourceRoot.map rename) =
        (canonicalPolymerExteriorFaceQueries
          sourceAmbient sourceRoot).map rename) :
    canonicalPolymerSupportQueryEventB targetAmbient
        (sourceRoot.map rename) targetSupport =
      canonicalPolymerSupportQueryEventB sourceAmbient sourceRoot
        (finiteSupportPreimage domain rename targetSupport) := by
  have hinternal :
      (sourceRoot.map rename).all (memberB targetSupport) =
        sourceRoot.all
          (memberB (finiteSupportPreimage domain rename targetSupport)) := by
    apply listAll_map_eq_of_pointwise
    intro face hface
    exact (memberB_finiteSupportPreimage
      domain rename targetSupport (hrootDomain face hface)).symm
  have hexteriorBits :
      ((canonicalPolymerExteriorFaceQueries
          sourceAmbient sourceRoot).map rename).all
          (fun face => !(memberB targetSupport face)) =
        (canonicalPolymerExteriorFaceQueries
          sourceAmbient sourceRoot).all
          (fun face =>
            !(memberB
              (finiteSupportPreimage domain rename targetSupport) face)) := by
    apply listAll_map_eq_of_pointwise
    intro face hface
    exact congrArg Bool.not
      (memberB_finiteSupportPreimage
        domain rename targetSupport
        (hexteriorDomain face hface)).symm
  unfold canonicalPolymerSupportQueryEventB
  rw [hexterior, hinternal, hexteriorBits]

/-- Exact simultaneous intertwining of every coordinate in a finite root
family.  The same finite support preimage is used for all roots, which is the
compatibility needed by semantic cylinder-vector comparison. -/
theorem canonicalRootsSupportQueryFingerprint_finiteSupportPreimage
    (sourceAmbient targetAmbient : Nat)
    (domain : List Nat) (rename : Nat → Nat)
    (roots : List (List Nat)) (targetSupport : List Nat)
    (hrootDomain : ∀ root, root ∈ roots →
      ∀ face, face ∈ root → face ∈ domain)
    (hexteriorDomain : ∀ root, root ∈ roots → ∀ face,
      face ∈ canonicalPolymerExteriorFaceQueries
        sourceAmbient root → face ∈ domain)
    (hexterior : ∀ root, root ∈ roots →
      canonicalPolymerExteriorFaceQueries targetAmbient
          (root.map rename) =
        (canonicalPolymerExteriorFaceQueries
          sourceAmbient root).map rename) :
    canonicalRootsSupportQueryFingerprint targetAmbient
        (roots.map (List.map rename)) targetSupport =
      canonicalRootsSupportQueryFingerprint sourceAmbient roots
        (finiteSupportPreimage domain rename targetSupport) := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
      simp only [List.map_cons, canonicalRootsSupportQueryFingerprint]
      rw [canonicalPolymerSupportQueryEventB_finiteSupportPreimage
        sourceAmbient targetAmbient domain rename root targetSupport
        (hrootDomain root List.mem_cons_self)
        (hexteriorDomain root List.mem_cons_self)
        (hexterior root List.mem_cons_self)]
      have htail := ih
        (fun item hitem => hrootDomain item
          (List.mem_cons_of_mem root hitem))
        (fun item hitem => hexteriorDomain item
          (List.mem_cons_of_mem root hitem))
        (fun item hitem => hexterior item
          (List.mem_cons_of_mem root hitem))
      unfold canonicalRootsSupportQueryFingerprint at htail
      exact congrArg
        (List.cons
          (canonicalPolymerSupportQueryEventB sourceAmbient root
            (finiteSupportPreimage domain rename targetSupport)))
        htail

#print axioms not_rawStrictLowerSameRadiusCovariant
#print axioms rawStrictLowerQueryPlaquette_timeShift
#print axioms centralStrictLowerCanonicalRoot_raw_sameSupport
#print axioms centralStrictLowerCanonicalRoot_full_margin
#print axioms centralStrictLowerCanonicalRoot_timeShift_sameSupport
#print axioms mem_centralStrictLowerCanonicalRoot_timeShift_iff
#print axioms mem_centralStrictLowerExterior_timeShift_iff
#print axioms centralStrictLowerSupportQueryEventB_timeShift
#print axioms centralStrictLowerCylinderFingerprint_timeShift
#print axioms centralSpatialPullbackLowerSupport_mem
#print axioms centralStrictLocalQueryCode_timeShift_completeLowerSupport
#print axioms canonicalPolymerSupportQueryEventB_finiteSupportPreimage
#print axioms canonicalPolymerSupportQueryEventB_finiteSupportPreimage_of_mem_iff
#print axioms canonicalRootsSupportQueryFingerprint_finiteSupportPreimage

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
