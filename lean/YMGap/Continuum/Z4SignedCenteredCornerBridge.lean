/-
# Exact affine bridge from corner boxes to signed centered boxes

The existing finite Yang--Mills laws are indexed by corner-anchored `Nat^4`
boxes.  This module gives those same finite cell lists signed coordinates:
the box of side `2 r + 1` is translated by `-r` in every coordinate, and an
arbitrary signed center is then added.  The coordinate changes have explicit
inverses on the finite lists, preserve plaquette incidence, and commute with
every signed translation.

Thus a finite law on an existing corner box can be transported without any
new amplitude or normalization choice to a centered signed box.  This is the
finite change-of-coordinates needed before a receding-boundary comparison;
it does not assert that two differently centered finite laws have equal local
marginals.
-/

import YMGap.Continuum.Z4SignedCenteredExhaustion

namespace YMGap.Continuum.Z4SignedCenteredCornerBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4SignedCenteredExhaustion

/-! ## 1. The affine coordinate change -/

def centeredBoxBase (radius : Nat) : Nat := radius + radius + 1

def natCoordinateToCenteredSigned (radius coordinate : Nat) : Int :=
  (coordinate : Int) - (radius : Int)

def centeredSignedCoordinateToNat (radius : Nat) (coordinate : Int) : Nat :=
  Int.toNat (coordinate + (radius : Int))

theorem centeredSignedCoordinateToNat_natCoordinateToCenteredSigned
    (radius coordinate : Nat) :
    centeredSignedCoordinateToNat radius
        (natCoordinateToCenteredSigned radius coordinate) = coordinate := by
  unfold centeredSignedCoordinateToNat natCoordinateToCenteredSigned
  rw [Int.sub_add_cancel]
  rfl

theorem signedCoordinate_add_radius_nonnegative
    {radius : Nat} {coordinate : Int}
    (hstage : signedCoordinateStage coordinate ≤ radius) :
    0 ≤ coordinate + (radius : Int) := by
  cases coordinate with
  | ofNat coordinate =>
      exact Int.add_nonneg (Int.natCast_nonneg coordinate)
        (Int.natCast_nonneg radius)
  | negSucc coordinate =>
      have hnat : coordinate + 1 ≤ radius := hstage
      have hcast : ((coordinate + 1 : Nat) : Int) ≤ (radius : Int) :=
        Int.ofNat_le.mpr hnat
      have hnonnegative := Int.sub_nonneg_of_le hcast
      rw [Int.sub_eq_add_neg, Int.add_comm] at hnonnegative
      simpa only [Int.negSucc_eq, Int.natCast_add, Int.natCast_one] using
        hnonnegative

theorem natCoordinateToCenteredSigned_centeredSignedCoordinateToNat
    {radius : Nat} {coordinate : Int}
    (hstage : signedCoordinateStage coordinate ≤ radius) :
    natCoordinateToCenteredSigned radius
        (centeredSignedCoordinateToNat radius coordinate) = coordinate := by
  unfold natCoordinateToCenteredSigned centeredSignedCoordinateToNat
  change ((coordinate + (radius : Int)).toNat : Int) -
      (radius : Int) = coordinate
  rw [Int.toNat_of_nonneg
    (signedCoordinate_add_radius_nonnegative hstage)]
  exact Int.add_sub_cancel coordinate (radius : Int)

theorem centeredSignedCoordinateToNat_lt_base
    {radius : Nat} {coordinate : Int}
    (hstage : signedCoordinateStage coordinate ≤ radius) :
    centeredSignedCoordinateToNat radius coordinate < centeredBoxBase radius := by
  apply Int.ofNat_lt.mp
  unfold centeredSignedCoordinateToNat
  rw [Int.toNat_of_nonneg
    (signedCoordinate_add_radius_nonnegative hstage)]
  cases coordinate with
  | ofNat coordinate =>
      change coordinate ≤ radius at hstage
      simp only [centeredBoxBase, Int.natCast_add, Int.natCast_one,
        Int.ofNat_eq_natCast]
      omega
  | negSucc coordinate =>
      change coordinate + 1 ≤ radius at hstage
      simp only [centeredBoxBase, Int.natCast_add, Int.natCast_one]
      rw [Int.negSucc_eq]
      omega

theorem natCoordinateToCenteredSigned_succ
    (radius coordinate : Nat) :
    natCoordinateToCenteredSigned radius (coordinate + 1) =
      natCoordinateToCenteredSigned radius coordinate + 1 := by
  unfold natCoordinateToCenteredSigned
  rw [Int.natCast_add, Int.natCast_one]
  simp only [Int.sub_eq_add_neg]
  rw [Int.add_assoc, Int.add_comm 1 (-(radius : Int)), ← Int.add_assoc]

/-! ## 2. Vertices, plaquettes, links, and incidence -/

def natVertexToCenteredSigned (radius : Nat) : Z4Vertex → SignedZ4Vertex
  | (a, b, c, d) =>
      (natCoordinateToCenteredSigned radius a,
        natCoordinateToCenteredSigned radius b,
        natCoordinateToCenteredSigned radius c,
        natCoordinateToCenteredSigned radius d)

def centeredSignedVertexToNat (radius : Nat) : SignedZ4Vertex → Z4Vertex
  | (a, b, c, d) =>
      (centeredSignedCoordinateToNat radius a,
        centeredSignedCoordinateToNat radius b,
        centeredSignedCoordinateToNat radius c,
        centeredSignedCoordinateToNat radius d)

def natPlaquetteToCenteredSigned (radius : Nat) (plaquette : Z4Plaq) :
    SignedZ4Plaq :=
  (natVertexToCenteredSigned radius plaquette.1, plaquette.2)

def centeredSignedPlaquetteToNat (radius : Nat)
    (plaquette : SignedZ4Plaq) : Z4Plaq :=
  (centeredSignedVertexToNat radius plaquette.1, plaquette.2)

def natLinkToCenteredSigned (radius : Nat) (link : Z4Link) : SignedZ4Link :=
  (natVertexToCenteredSigned radius link.1, link.2)

def centeredSignedLinkToNat (radius : Nat) (link : SignedZ4Link) : Z4Link :=
  (centeredSignedVertexToNat radius link.1, link.2)

theorem centeredSignedVertexToNat_natVertexToCenteredSigned
    (radius : Nat) (vertex : Z4Vertex) :
    centeredSignedVertexToNat radius
        (natVertexToCenteredSigned radius vertex) = vertex := by
  obtain ⟨a, b, c, d⟩ := vertex
  simp [centeredSignedVertexToNat, natVertexToCenteredSigned,
    centeredSignedCoordinateToNat_natCoordinateToCenteredSigned]

theorem centeredSignedPlaquetteToNat_natPlaquetteToCenteredSigned
    (radius : Nat) (plaquette : Z4Plaq) :
    centeredSignedPlaquetteToNat radius
        (natPlaquetteToCenteredSigned radius plaquette) = plaquette := by
  apply Prod.ext
  · exact centeredSignedVertexToNat_natVertexToCenteredSigned
      radius plaquette.1
  · rfl

theorem centeredSignedLinkToNat_natLinkToCenteredSigned
    (radius : Nat) (link : Z4Link) :
    centeredSignedLinkToNat radius
        (natLinkToCenteredSigned radius link) = link := by
  apply Prod.ext
  · exact centeredSignedVertexToNat_natVertexToCenteredSigned radius link.1
  · rfl

theorem natVertexToCenteredSigned_addE
    (radius : Nat) (vertex : Z4Vertex) (direction : Dir4) :
    natVertexToCenteredSigned radius (addE vertex direction) =
      signedAddE (natVertexToCenteredSigned radius vertex) direction := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction <;>
    simp [natVertexToCenteredSigned, addE, signedAddE,
      natCoordinateToCenteredSigned_succ]

theorem signedEdgesOf_natPlaquetteToCenteredSigned
    (radius : Nat) (plaquette : Z4Plaq) :
    signedEdgesOf (natPlaquetteToCenteredSigned radius plaquette) =
      (edgesOf plaquette).map (natLinkToCenteredSigned radius) := by
  simp [signedEdgesOf, edgesOf, natPlaquetteToCenteredSigned,
    natLinkToCenteredSigned, natVertexToCenteredSigned_addE]

/-! ## 3. Existing corner lists in centered signed coordinates -/

def cornerCenteredBoxVertices (center : SignedZ4Vertex) (radius : Nat) :
    List SignedZ4Vertex :=
  (boxVertices (centeredBoxBase radius)).map fun vertex =>
    signedTranslateVertex center (natVertexToCenteredSigned radius vertex)

def cornerCenteredBoxPlaquettes (center : SignedZ4Vertex) (radius : Nat) :
    List SignedZ4Plaq :=
  (boxPlaquettes (centeredBoxBase radius)).map fun plaquette =>
    signedTranslatePlaquette center
      (natPlaquetteToCenteredSigned radius plaquette)

def cornerCenteredBoxLinks (center : SignedZ4Vertex) (radius : Nat) :
    List SignedZ4Link :=
  (boxLinks (centeredBoxBase radius)).map fun link =>
    signedTranslateLink center (natLinkToCenteredSigned radius link)

theorem cornerCenteredBoxVertices_translate
    (center shift : SignedZ4Vector) (radius : Nat) :
    (cornerCenteredBoxVertices center radius).map
        (signedTranslateVertex shift) =
      cornerCenteredBoxVertices (signedAdd center shift) radius := by
  unfold cornerCenteredBoxVertices
  rw [List.map_map]
  apply List.map_congr_left
  intro vertex _
  simp only [Function.comp_apply]
  exact signedTranslateVertex_comp center shift
    (natVertexToCenteredSigned radius vertex)

theorem cornerCenteredBoxPlaquettes_translate
    (center shift : SignedZ4Vector) (radius : Nat) :
    (cornerCenteredBoxPlaquettes center radius).map
        (signedTranslatePlaquette shift) =
      cornerCenteredBoxPlaquettes (signedAdd center shift) radius := by
  unfold cornerCenteredBoxPlaquettes
  rw [List.map_map]
  apply List.map_congr_left
  intro plaquette _
  simp only [Function.comp_apply, signedTranslatePlaquette]
  apply Prod.ext
  · exact signedTranslateVertex_comp center shift
      (natVertexToCenteredSigned radius plaquette.1)
  · rfl

theorem cornerCenteredBoxLinks_translate
    (center shift : SignedZ4Vector) (radius : Nat) :
    (cornerCenteredBoxLinks center radius).map
        (signedTranslateLink shift) =
      cornerCenteredBoxLinks (signedAdd center shift) radius := by
  unfold cornerCenteredBoxLinks
  rw [List.map_map]
  apply List.map_congr_left
  intro link _
  simp only [Function.comp_apply, signedTranslateLink]
  apply Prod.ext
  · exact signedTranslateVertex_comp center shift
      (natVertexToCenteredSigned radius link.1)
  · rfl

/-! ## 4. Explicit heterogeneous finite-list bijections -/

structure FiniteListReindexing (A B : Type) where
  source : List A
  target : List B
  forward : A → B
  inverse : B → A
  inverse_forward_on_source : ∀ item, item ∈ source →
    inverse (forward item) = item
  forward_inverse_on_target : ∀ item, item ∈ target →
    forward (inverse item) = item
  map_source : source.map forward = target

def cornerVertexCenteredReindexing (radius : Nat) :
    FiniteListReindexing Z4Vertex SignedZ4Vertex where
  source := boxVertices (centeredBoxBase radius)
  target := cornerCenteredBoxVertices signedZero radius
  forward := natVertexToCenteredSigned radius
  inverse := centeredSignedVertexToNat radius
  inverse_forward_on_source := fun item _ =>
    centeredSignedVertexToNat_natVertexToCenteredSigned radius item
  forward_inverse_on_target := by
    intro item hitem
    unfold cornerCenteredBoxVertices at hitem
    obtain ⟨source, _, heq⟩ := List.mem_map.mp hitem
    rw [← heq]
    simp only [signedTranslateVertex, signedAdd_zero_right]
    rw [centeredSignedVertexToNat_natVertexToCenteredSigned]
  map_source := by
    unfold cornerCenteredBoxVertices
    apply List.map_congr_left
    intro vertex _
    exact (signedAdd_zero_right
      (natVertexToCenteredSigned radius vertex)).symm

def cornerPlaquetteCenteredReindexing (radius : Nat) :
    FiniteListReindexing Z4Plaq SignedZ4Plaq where
  source := boxPlaquettes (centeredBoxBase radius)
  target := cornerCenteredBoxPlaquettes signedZero radius
  forward := natPlaquetteToCenteredSigned radius
  inverse := centeredSignedPlaquetteToNat radius
  inverse_forward_on_source := fun item _ =>
    centeredSignedPlaquetteToNat_natPlaquetteToCenteredSigned radius item
  forward_inverse_on_target := by
    intro item hitem
    unfold cornerCenteredBoxPlaquettes at hitem
    obtain ⟨source, _, heq⟩ := List.mem_map.mp hitem
    rw [← heq]
    change natPlaquetteToCenteredSigned radius
        (centeredSignedPlaquetteToNat radius
          (signedTranslatePlaquette signedZero
            (natPlaquetteToCenteredSigned radius source))) = _
    simp only [signedTranslatePlaquette, signedTranslateVertex,
      signedAdd_zero_right]
    rw [centeredSignedPlaquetteToNat_natPlaquetteToCenteredSigned]
  map_source := by
    unfold cornerCenteredBoxPlaquettes
    apply List.map_congr_left
    intro plaquette _
    apply Prod.ext
    · exact (signedAdd_zero_right
        (natVertexToCenteredSigned radius plaquette.1)).symm
    · rfl

def cornerLinkCenteredReindexing (radius : Nat) :
    FiniteListReindexing Z4Link SignedZ4Link where
  source := boxLinks (centeredBoxBase radius)
  target := cornerCenteredBoxLinks signedZero radius
  forward := natLinkToCenteredSigned radius
  inverse := centeredSignedLinkToNat radius
  inverse_forward_on_source := fun item _ =>
    centeredSignedLinkToNat_natLinkToCenteredSigned radius item
  forward_inverse_on_target := by
    intro item hitem
    unfold cornerCenteredBoxLinks at hitem
    obtain ⟨source, _, heq⟩ := List.mem_map.mp hitem
    rw [← heq]
    change natLinkToCenteredSigned radius
        (centeredSignedLinkToNat radius
          (signedTranslateLink signedZero
            (natLinkToCenteredSigned radius source))) = _
    simp only [signedTranslateLink, signedTranslateVertex,
      signedAdd_zero_right]
    rw [centeredSignedLinkToNat_natLinkToCenteredSigned]
  map_source := by
    unfold cornerCenteredBoxLinks
    apply List.map_congr_left
    intro link _
    apply Prod.ext
    · exact (signedAdd_zero_right
        (natVertexToCenteredSigned radius link.1)).symm
    · rfl

/-! ## 5. Cofinality and the existing local-root bridge -/

private theorem coordinateStage_le_vertexStage_first
    (vertex : SignedZ4Vertex) :
    signedCoordinateStage vertex.1 ≤ signedVertexStage vertex :=
  Nat.le_max_left _ _

private theorem coordinateStage_le_vertexStage_second
    (vertex : SignedZ4Vertex) :
    signedCoordinateStage vertex.2.1 ≤ signedVertexStage vertex :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

private theorem coordinateStage_le_vertexStage_third
    (vertex : SignedZ4Vertex) :
    signedCoordinateStage vertex.2.2.1 ≤ signedVertexStage vertex :=
  Nat.le_trans
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    (Nat.le_max_right _ _)

private theorem coordinateStage_le_vertexStage_fourth
    (vertex : SignedZ4Vertex) :
    signedCoordinateStage vertex.2.2.2 ≤ signedVertexStage vertex :=
  Nat.le_trans
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (Nat.le_max_right _ _)

private theorem natVertexToCenteredSigned_stage_inverse
    (vertex : SignedZ4Vertex) :
    natVertexToCenteredSigned (signedVertexStage vertex)
        (centeredSignedVertexToNat (signedVertexStage vertex) vertex) =
      vertex := by
  obtain ⟨a, b, c, d⟩ := vertex
  apply Prod.ext
  · exact natCoordinateToCenteredSigned_centeredSignedCoordinateToNat
      (coordinateStage_le_vertexStage_first (a, b, c, d))
  · apply Prod.ext
    · exact natCoordinateToCenteredSigned_centeredSignedCoordinateToNat
        (coordinateStage_le_vertexStage_second (a, b, c, d))
    · apply Prod.ext
      · exact natCoordinateToCenteredSigned_centeredSignedCoordinateToNat
          (coordinateStage_le_vertexStage_third (a, b, c, d))
      · exact natCoordinateToCenteredSigned_centeredSignedCoordinateToNat
          (coordinateStage_le_vertexStage_fourth (a, b, c, d))

theorem signedVertex_mem_cornerCenteredBox_stage
    (vertex : SignedZ4Vertex) :
    vertex ∈ cornerCenteredBoxVertices signedZero
      (signedVertexStage vertex) := by
  let radius := signedVertexStage vertex
  let source := centeredSignedVertexToNat radius vertex
  have hsource : source ∈ boxVertices (centeredBoxBase radius) := by
    rw [mem_boxVertices]
    exact
      ⟨centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_first vertex),
        centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_second vertex),
        centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_third vertex),
        centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_fourth vertex)⟩
  unfold cornerCenteredBoxVertices
  apply List.mem_map.mpr
  refine ⟨source, hsource, ?_⟩
  simp only [signedTranslateVertex, signedAdd_zero_right]
  exact natVertexToCenteredSigned_stage_inverse vertex

theorem signedPlaquette_mem_cornerCenteredBox
    (plaquette : SignedZ4Plaq) :
    plaquette ∈ cornerCenteredBoxPlaquettes signedZero
      (signedVertexStage plaquette.1) := by
  let radius := signedVertexStage plaquette.1
  let source := centeredSignedPlaquetteToNat radius plaquette
  have hsourceVertex : source.1 ∈
      boxVertices (centeredBoxBase radius) := by
    rw [mem_boxVertices]
    exact
      ⟨centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_first plaquette.1),
        centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_second plaquette.1),
        centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_third plaquette.1),
        centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_fourth plaquette.1)⟩
  have hsource : source ∈ boxPlaquettes (centeredBoxBase radius) := by
    unfold boxPlaquettes
    apply List.mem_flatMap.mpr
    refine ⟨source.1, hsourceVertex, ?_⟩
    obtain ⟨sourceVertex, sourcePlane⟩ := source
    cases sourcePlane <;> simp [z4Planes]
  unfold cornerCenteredBoxPlaquettes
  apply List.mem_map.mpr
  refine ⟨source, hsource, ?_⟩
  simp only [signedTranslatePlaquette, signedTranslateVertex,
    signedAdd_zero_right]
  apply Prod.ext
  · exact natVertexToCenteredSigned_stage_inverse plaquette.1
  · rfl

theorem signedLink_mem_cornerCenteredBox
    (link : SignedZ4Link) :
    link ∈ cornerCenteredBoxLinks signedZero
      (signedVertexStage link.1) := by
  let radius := signedVertexStage link.1
  let source := centeredSignedLinkToNat radius link
  have hsourceVertex : source.1 ∈ boxVertices (centeredBoxBase radius) := by
    rw [mem_boxVertices]
    exact
      ⟨centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_first link.1),
        centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_second link.1),
        centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_third link.1),
        centeredSignedCoordinateToNat_lt_base
          (coordinateStage_le_vertexStage_fourth link.1)⟩
  have hcarrier : linkCarrierPlaquette source ∈
      boxPlaquettes (centeredBoxBase radius) := by
    unfold boxPlaquettes
    apply List.mem_flatMap.mpr
    refine ⟨source.1, hsourceVertex, ?_⟩
    obtain ⟨sourceVertex, sourceDirection⟩ := source
    cases sourceDirection <;> simp [linkCarrierPlaquette, z4Planes]
  have hsource : source ∈ boxLinks (centeredBoxBase radius) := by
    exact boundary_mem_boxLinks hcarrier (link_mem_carrier_boundary source)
  unfold cornerCenteredBoxLinks
  apply List.mem_map.mpr
  refine ⟨source, hsource, ?_⟩
  simp only [signedTranslateLink, signedTranslateVertex,
    signedAdd_zero_right]
  apply Prod.ext
  · exact natVertexToCenteredSigned_stage_inverse link.1
  · rfl

/-! ## 6. Concrete placement of the existing canonical local roots -/

def offsetNatVertex (offset : Nat) : Z4Vertex → Z4Vertex
  | (a, b, c, d) =>
      (a + offset, b + offset, c + offset, d + offset)

def offsetNatPlaquette (offset : Nat) (plaquette : Z4Plaq) : Z4Plaq :=
  (offsetNatVertex offset plaquette.1, plaquette.2)

theorem offsetNatPlaquette_mem_centeredBase
    {base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    offsetNatPlaquette base plaquette ∈
      boxPlaquettes (centeredBoxBase base) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rw [mem_boxPlaquettes] at hplaquette ⊢
  change a < base ∧ b < base ∧ c < base ∧ d < base at hplaquette
  change a + base < centeredBoxBase base ∧
    b + base < centeredBoxBase base ∧
    c + base < centeredBoxBase base ∧
    d + base < centeredBoxBase base
  unfold centeredBoxBase
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem natPlaquetteToCenteredSigned_offset
    (base : Nat) (plaquette : Z4Plaq) :
    natPlaquetteToCenteredSigned base (offsetNatPlaquette base plaquette) =
      natPlaquetteToSigned plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  apply Prod.ext
  · simp only [natPlaquetteToCenteredSigned, offsetNatPlaquette,
      offsetNatVertex, natVertexToCenteredSigned, natPlaquetteToSigned,
      natVertexToSigned, natCoordinateToCenteredSigned]
    simp only [Int.natCast_add, Int.add_sub_cancel,
      Int.ofNat_eq_natCast]
  · rfl

theorem natPlaquetteToSigned_mem_cornerCenteredBox
    {base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    natPlaquetteToSigned plaquette ∈
      cornerCenteredBoxPlaquettes signedZero base := by
  unfold cornerCenteredBoxPlaquettes
  apply List.mem_map.mpr
  refine ⟨offsetNatPlaquette base plaquette,
    offsetNatPlaquette_mem_centeredBase hplaquette, ?_⟩
  simp only [signedTranslatePlaquette, signedTranslateVertex,
    signedAdd_zero_right]
  exact natPlaquetteToCenteredSigned_offset base plaquette

theorem signedCanonicalRootSupport_subset_cornerCenteredBox
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    ∀ plaquette,
      plaquette ∈ signedCanonicalRootSupport base root →
        plaquette ∈ cornerCenteredBoxPlaquettes signedZero base := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  apply natPlaquetteToSigned_mem_cornerCenteredBox
  exact geometricPolymer_subset_box
    (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource

#print axioms centeredSignedCoordinateToNat_natCoordinateToCenteredSigned
#print axioms natCoordinateToCenteredSigned_centeredSignedCoordinateToNat
#print axioms signedEdgesOf_natPlaquetteToCenteredSigned
#print axioms cornerCenteredBoxVertices_translate
#print axioms cornerCenteredBoxPlaquettes_translate
#print axioms cornerCenteredBoxLinks_translate
#print axioms cornerVertexCenteredReindexing
#print axioms cornerPlaquetteCenteredReindexing
#print axioms cornerLinkCenteredReindexing
#print axioms signedVertex_mem_cornerCenteredBox_stage
#print axioms signedPlaquette_mem_cornerCenteredBox
#print axioms signedLink_mem_cornerCenteredBox
#print axioms natPlaquetteToSigned_mem_cornerCenteredBox
#print axioms signedCanonicalRootSupport_subset_cornerCenteredBox

end YMGap.Continuum.Z4SignedCenteredCornerBridge
