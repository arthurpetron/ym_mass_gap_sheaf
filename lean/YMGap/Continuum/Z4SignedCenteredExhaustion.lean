/-
# A signed, centered, translation-reindexed Z4 exhaustion

The corner geometry is replaced at the geometric layer by explicit finite
subsets of `Int^4`.  A radius lists the symmetric coordinates
`0, ±1, ..., ±r`; a signed slab uses independent spatial and time radii,
and a centered slab is a literal translate of the zero-centered slab.

Signed translation has an explicit inverse.  It reindexes the complete
vertex, plaquette, and boundary-link lists exactly, while zero-centered boxes
are cofinal for every signed vertex, plaquette, and link.  Finally the old
`Nat^4` geometry embeds into this signed geometry, and the existing canonical
time-shifted cylinder roots agree supportwise with signed translation after
that embedding.

This module is finite geometry only.  The physical spin-foam law on these
centered lists and the receding-boundary thermodynamic estimate are separate
next layers.
-/

import YMGap.Continuum.Z4FiniteCylinderTimeTranslationColimit

namespace YMGap.Continuum.Z4SignedCenteredExhaustion

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Signed cells and their translation group -/

abbrev SignedZ4Vertex : Type := Int × Int × Int × Int
abbrev SignedZ4Vector : Type := SignedZ4Vertex
abbrev SignedZ4Link : Type := SignedZ4Vertex × Dir4
abbrev SignedZ4Plaq : Type := SignedZ4Vertex × Z4Plane

def signedZero : SignedZ4Vector := (0, 0, 0, 0)

def signedAdd (left right : SignedZ4Vector) : SignedZ4Vector :=
  (left.1 + right.1,
    left.2.1 + right.2.1,
    left.2.2.1 + right.2.2.1,
    left.2.2.2 + right.2.2.2)

def signedNeg (vector : SignedZ4Vector) : SignedZ4Vector :=
  (-vector.1, -vector.2.1, -vector.2.2.1, -vector.2.2.2)

def signedTranslateVertex (shift : SignedZ4Vector)
    (vertex : SignedZ4Vertex) : SignedZ4Vertex :=
  signedAdd vertex shift

def signedTranslateLink (shift : SignedZ4Vector)
    (link : SignedZ4Link) : SignedZ4Link :=
  (signedTranslateVertex shift link.1, link.2)

def signedTranslatePlaquette (shift : SignedZ4Vector)
    (plaquette : SignedZ4Plaq) : SignedZ4Plaq :=
  (signedTranslateVertex shift plaquette.1, plaquette.2)

theorem signedAdd_assoc (first second third : SignedZ4Vector) :
    signedAdd (signedAdd first second) third =
      signedAdd first (signedAdd second third) := by
  obtain ⟨a, b, c, d⟩ := first
  obtain ⟨e, f, g, h⟩ := second
  obtain ⟨i, j, k, l⟩ := third
  simp [signedAdd, Int.add_assoc]

theorem signedAdd_zero_right (vector : SignedZ4Vector) :
    signedAdd vector signedZero = vector := by
  obtain ⟨a, b, c, d⟩ := vector
  simp [signedAdd, signedZero]

theorem signedAdd_neg_right (vector : SignedZ4Vector) :
    signedAdd vector (signedNeg vector) = signedZero := by
  obtain ⟨a, b, c, d⟩ := vector
  simp [signedAdd, signedNeg, signedZero, Int.add_right_neg]

theorem signedTranslateVertex_comp
    (first second : SignedZ4Vector) (vertex : SignedZ4Vertex) :
    signedTranslateVertex second (signedTranslateVertex first vertex) =
      signedTranslateVertex (signedAdd first second) vertex := by
  exact signedAdd_assoc vertex first second

theorem signedTranslateVertex_inverse_left
    (shift : SignedZ4Vector) (vertex : SignedZ4Vertex) :
    signedTranslateVertex (signedNeg shift)
        (signedTranslateVertex shift vertex) = vertex := by
  obtain ⟨a, b, c, d⟩ := vertex
  obtain ⟨e, f, g, h⟩ := shift
  simp [signedTranslateVertex, signedAdd, signedNeg,
    Int.add_neg_cancel_right]

theorem signedTranslateVertex_inverse_right
    (shift : SignedZ4Vector) (vertex : SignedZ4Vertex) :
    signedTranslateVertex shift
        (signedTranslateVertex (signedNeg shift) vertex) = vertex := by
  obtain ⟨a, b, c, d⟩ := vertex
  obtain ⟨e, f, g, h⟩ := shift
  simp [signedTranslateVertex, signedAdd, signedNeg,
    Int.neg_add_cancel_right]

theorem signedTranslatePlaquette_inverse_left
    (shift : SignedZ4Vector) (plaquette : SignedZ4Plaq) :
    signedTranslatePlaquette (signedNeg shift)
        (signedTranslatePlaquette shift plaquette) = plaquette := by
  apply Prod.ext
  · exact signedTranslateVertex_inverse_left shift plaquette.1
  · rfl

theorem signedTranslateLink_inverse_left
    (shift : SignedZ4Vector) (link : SignedZ4Link) :
    signedTranslateLink (signedNeg shift)
        (signedTranslateLink shift link) = link := by
  apply Prod.ext
  · exact signedTranslateVertex_inverse_left shift link.1
  · rfl

/-! ## 2. Signed incidence -/

def signedAddE : SignedZ4Vertex → Dir4 → SignedZ4Vertex
  | (a, b, c, d), .x0 => (a + 1, b, c, d)
  | (a, b, c, d), .x1 => (a, b + 1, c, d)
  | (a, b, c, d), .x2 => (a, b, c + 1, d)
  | (a, b, c, d), .x3 => (a, b, c, d + 1)

def signedEdgesOf (plaquette : SignedZ4Plaq) : List SignedZ4Link :=
  [ (plaquette.1, (dirsOf plaquette.2).1),
    (plaquette.1, (dirsOf plaquette.2).2),
    (signedAddE plaquette.1 (dirsOf plaquette.2).2,
      (dirsOf plaquette.2).1),
    (signedAddE plaquette.1 (dirsOf plaquette.2).1,
      (dirsOf plaquette.2).2) ]

theorem signedTranslateVertex_addE
    (shift : SignedZ4Vector) (vertex : SignedZ4Vertex) (direction : Dir4) :
    signedTranslateVertex shift (signedAddE vertex direction) =
      signedAddE (signedTranslateVertex shift vertex) direction := by
  obtain ⟨a, b, c, d⟩ := vertex
  obtain ⟨e, f, g, h⟩ := shift
  cases direction <;> simp [signedTranslateVertex, signedAdd, signedAddE] <;>
    omega

theorem signedEdgesOf_translate
    (shift : SignedZ4Vector) (plaquette : SignedZ4Plaq) :
    signedEdgesOf (signedTranslatePlaquette shift plaquette) =
      (signedEdgesOf plaquette).map (signedTranslateLink shift) := by
  simp [signedEdgesOf, signedTranslatePlaquette, signedTranslateLink,
    signedTranslateVertex_addE]

/-! ## 3. Symmetric coordinates and centered finite slabs -/

def symmetricIntCoordinates : Nat → List Int
  | 0 => [0]
  | radius + 1 =>
      (-(Int.ofNat (radius + 1))) ::
        symmetricIntCoordinates radius ++ [Int.ofNat (radius + 1)]

def signedCoordinateStage : Int → Nat
  | .ofNat n => n
  | .negSucc n => n + 1

theorem signedCoordinate_mem_stage (coordinate : Int) :
    coordinate ∈ symmetricIntCoordinates (signedCoordinateStage coordinate) := by
  cases coordinate with
  | ofNat n =>
      cases n with
      | zero => simp [signedCoordinateStage, symmetricIntCoordinates]
      | succ n => simp [signedCoordinateStage, symmetricIntCoordinates]
  | negSucc n =>
      simp [signedCoordinateStage, symmetricIntCoordinates, Int.negSucc_eq]

theorem symmetricIntCoordinates_mem_succ
    {radius : Nat} {coordinate : Int}
    (hcoordinate : coordinate ∈ symmetricIntCoordinates radius) :
    coordinate ∈ symmetricIntCoordinates (radius + 1) := by
  unfold symmetricIntCoordinates
  exact List.mem_cons.mpr
    (Or.inr (List.mem_append.mpr (Or.inl hcoordinate)))

theorem symmetricIntCoordinates_mem_mono
    {small large : Nat} (hsmall : small ≤ large)
    {coordinate : Int}
    (hcoordinate : coordinate ∈ symmetricIntCoordinates small) :
    coordinate ∈ symmetricIntCoordinates large := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hsmall
  clear hsmall
  induction offset with
  | zero => simpa
  | succ offset ih =>
      rw [Nat.add_succ]
      exact symmetricIntCoordinates_mem_succ ih

def zeroSignedSlabVertices
    (spatialRadius timeRadius : Nat) : List SignedZ4Vertex :=
  (symmetricIntCoordinates spatialRadius).flatMap fun a =>
    (symmetricIntCoordinates spatialRadius).flatMap fun b =>
      (symmetricIntCoordinates spatialRadius).flatMap fun c =>
        (symmetricIntCoordinates timeRadius).map fun d => (a, b, c, d)

def zeroSignedSlabPlaquettes
    (spatialRadius timeRadius : Nat) : List SignedZ4Plaq :=
  (zeroSignedSlabVertices spatialRadius timeRadius).flatMap fun vertex =>
    z4Planes.map fun plane => (vertex, plane)

def zeroSignedSlabLinks
    (spatialRadius timeRadius : Nat) : List SignedZ4Link :=
  (zeroSignedSlabPlaquettes spatialRadius timeRadius).flatMap signedEdgesOf

def centeredSignedSlabVertices (center : SignedZ4Vertex)
    (spatialRadius timeRadius : Nat) : List SignedZ4Vertex :=
  (zeroSignedSlabVertices spatialRadius timeRadius).map
    (signedTranslateVertex center)

def centeredSignedSlabPlaquettes (center : SignedZ4Vertex)
    (spatialRadius timeRadius : Nat) : List SignedZ4Plaq :=
  (zeroSignedSlabPlaquettes spatialRadius timeRadius).map
    (signedTranslatePlaquette center)

def centeredSignedSlabLinks (center : SignedZ4Vertex)
    (spatialRadius timeRadius : Nat) : List SignedZ4Link :=
  (zeroSignedSlabLinks spatialRadius timeRadius).map
    (signedTranslateLink center)

def centeredSignedBoxVertices (center : SignedZ4Vertex) (radius : Nat) :
    List SignedZ4Vertex := centeredSignedSlabVertices center radius radius

def centeredSignedBoxPlaquettes (center : SignedZ4Vertex) (radius : Nat) :
    List SignedZ4Plaq := centeredSignedSlabPlaquettes center radius radius

def centeredSignedBoxLinks (center : SignedZ4Vertex) (radius : Nat) :
    List SignedZ4Link := centeredSignedSlabLinks center radius radius

theorem centeredSignedSlabVertices_translate
    (center shift : SignedZ4Vector) (spatialRadius timeRadius : Nat) :
    (centeredSignedSlabVertices center spatialRadius timeRadius).map
        (signedTranslateVertex shift) =
      centeredSignedSlabVertices (signedAdd center shift)
        spatialRadius timeRadius := by
  unfold centeredSignedSlabVertices
  rw [List.map_map]
  apply List.map_congr_left
  intro vertex _
  simp only [Function.comp_apply]
  exact signedTranslateVertex_comp center shift vertex

theorem centeredSignedSlabPlaquettes_translate
    (center shift : SignedZ4Vector) (spatialRadius timeRadius : Nat) :
    (centeredSignedSlabPlaquettes center spatialRadius timeRadius).map
        (signedTranslatePlaquette shift) =
      centeredSignedSlabPlaquettes (signedAdd center shift)
        spatialRadius timeRadius := by
  unfold centeredSignedSlabPlaquettes
  rw [List.map_map]
  apply List.map_congr_left
  intro plaquette _
  simp only [Function.comp_apply, signedTranslatePlaquette]
  apply Prod.ext
  · exact signedTranslateVertex_comp center shift plaquette.1
  · rfl

theorem centeredSignedSlabLinks_translate
    (center shift : SignedZ4Vector) (spatialRadius timeRadius : Nat) :
    (centeredSignedSlabLinks center spatialRadius timeRadius).map
        (signedTranslateLink shift) =
      centeredSignedSlabLinks (signedAdd center shift)
        spatialRadius timeRadius := by
  unfold centeredSignedSlabLinks
  rw [List.map_map]
  apply List.map_congr_left
  intro link _
  simp only [Function.comp_apply, signedTranslateLink]
  apply Prod.ext
  · exact signedTranslateVertex_comp center shift link.1
  · rfl

/-! ## 4. Explicit finite reindexing -/

structure FiniteListBijection (A : Type) where
  source : List A
  target : List A
  forward : A → A
  inverse : A → A
  inverse_forward : ∀ item, inverse (forward item) = item
  forward_inverse : ∀ item, forward (inverse item) = item
  map_source : source.map forward = target

def signedSlabVertexTranslationBijection
    (center shift : SignedZ4Vector) (spatialRadius timeRadius : Nat) :
    FiniteListBijection SignedZ4Vertex where
  source := centeredSignedSlabVertices center spatialRadius timeRadius
  target := centeredSignedSlabVertices (signedAdd center shift)
    spatialRadius timeRadius
  forward := signedTranslateVertex shift
  inverse := signedTranslateVertex (signedNeg shift)
  inverse_forward := signedTranslateVertex_inverse_left shift
  forward_inverse := signedTranslateVertex_inverse_right shift
  map_source := centeredSignedSlabVertices_translate
    center shift spatialRadius timeRadius

def signedSlabPlaquetteTranslationBijection
    (center shift : SignedZ4Vector) (spatialRadius timeRadius : Nat) :
    FiniteListBijection SignedZ4Plaq where
  source := centeredSignedSlabPlaquettes center spatialRadius timeRadius
  target := centeredSignedSlabPlaquettes (signedAdd center shift)
    spatialRadius timeRadius
  forward := signedTranslatePlaquette shift
  inverse := signedTranslatePlaquette (signedNeg shift)
  inverse_forward := signedTranslatePlaquette_inverse_left shift
  forward_inverse := by
    intro plaquette
    apply Prod.ext
    · exact signedTranslateVertex_inverse_right shift plaquette.1
    · rfl
  map_source := centeredSignedSlabPlaquettes_translate
    center shift spatialRadius timeRadius

def signedSlabLinkTranslationBijection
    (center shift : SignedZ4Vector) (spatialRadius timeRadius : Nat) :
    FiniteListBijection SignedZ4Link where
  source := centeredSignedSlabLinks center spatialRadius timeRadius
  target := centeredSignedSlabLinks (signedAdd center shift)
    spatialRadius timeRadius
  forward := signedTranslateLink shift
  inverse := signedTranslateLink (signedNeg shift)
  inverse_forward := signedTranslateLink_inverse_left shift
  forward_inverse := by
    intro link
    apply Prod.ext
    · exact signedTranslateVertex_inverse_right shift link.1
    · rfl
  map_source := centeredSignedSlabLinks_translate
    center shift spatialRadius timeRadius

/-! ## 5. Cofinality -/

def signedVertexStage (vertex : SignedZ4Vertex) : Nat :=
  max (signedCoordinateStage vertex.1)
    (max (signedCoordinateStage vertex.2.1)
      (max (signedCoordinateStage vertex.2.2.1)
        (signedCoordinateStage vertex.2.2.2)))

theorem signedVertex_mem_zero_box_stage (vertex : SignedZ4Vertex) :
    vertex ∈ zeroSignedSlabVertices
      (signedVertexStage vertex) (signedVertexStage vertex) := by
  have h0 : signedCoordinateStage vertex.1 ≤ signedVertexStage vertex :=
    Nat.le_max_left _ _
  have h1 : signedCoordinateStage vertex.2.1 ≤ signedVertexStage vertex :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have h2 : signedCoordinateStage vertex.2.2.1 ≤ signedVertexStage vertex :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _)
  have h3 : signedCoordinateStage vertex.2.2.2 ≤ signedVertexStage vertex :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _)
  unfold zeroSignedSlabVertices
  apply List.mem_flatMap.mpr
  refine ⟨vertex.1,
    symmetricIntCoordinates_mem_mono h0
      (signedCoordinate_mem_stage vertex.1), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨vertex.2.1,
    symmetricIntCoordinates_mem_mono h1
      (signedCoordinate_mem_stage vertex.2.1), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨vertex.2.2.1,
    symmetricIntCoordinates_mem_mono h2
      (signedCoordinate_mem_stage vertex.2.2.1), ?_⟩
  exact List.mem_map.mpr
    ⟨vertex.2.2.2,
      symmetricIntCoordinates_mem_mono h3
        (signedCoordinate_mem_stage vertex.2.2.2), rfl⟩

theorem signedVertex_mem_centered_zero_box_stage (vertex : SignedZ4Vertex) :
    vertex ∈ centeredSignedBoxVertices signedZero
      (signedVertexStage vertex) := by
  unfold centeredSignedBoxVertices centeredSignedSlabVertices
  apply List.mem_map.mpr
  exact ⟨vertex, signedVertex_mem_zero_box_stage vertex,
    signedAdd_zero_right vertex⟩

theorem signedPlaquette_mem_centered_zero_box
    (plaquette : SignedZ4Plaq) :
    plaquette ∈ centeredSignedBoxPlaquettes signedZero
      (signedVertexStage plaquette.1) := by
  unfold centeredSignedBoxPlaquettes centeredSignedSlabPlaquettes
    zeroSignedSlabPlaquettes
  apply List.mem_map.mpr
  refine ⟨plaquette, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨plaquette.1, signedVertex_mem_zero_box_stage plaquette.1, ?_⟩
    obtain ⟨vertex, plane⟩ := plaquette
    cases plane <;> simp [z4Planes]
  · apply Prod.ext
    · exact signedAdd_zero_right plaquette.1
    · rfl

def signedLinkCarrierPlaquette : SignedZ4Link → SignedZ4Plaq
  | (vertex, .x0) => (vertex, .p01)
  | (vertex, .x1) => (vertex, .p01)
  | (vertex, .x2) => (vertex, .p02)
  | (vertex, .x3) => (vertex, .p03)

theorem signedLink_mem_carrier_boundary (link : SignedZ4Link) :
    link ∈ signedEdgesOf (signedLinkCarrierPlaquette link) := by
  obtain ⟨vertex, direction⟩ := link
  cases direction <;> simp [signedLinkCarrierPlaquette,
    signedEdgesOf, dirsOf]

theorem signedLink_mem_centered_zero_box (link : SignedZ4Link) :
    link ∈ centeredSignedBoxLinks signedZero
      (signedVertexStage (signedLinkCarrierPlaquette link).1) := by
  unfold centeredSignedBoxLinks centeredSignedSlabLinks zeroSignedSlabLinks
  apply List.mem_map.mpr
  refine ⟨link, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    exact ⟨signedLinkCarrierPlaquette link,
      by
        unfold zeroSignedSlabPlaquettes
        apply List.mem_flatMap.mpr
        refine ⟨(signedLinkCarrierPlaquette link).1,
          signedVertex_mem_zero_box_stage
            (signedLinkCarrierPlaquette link).1, ?_⟩
        obtain ⟨vertex, direction⟩ := link
        cases direction <;> simp [signedLinkCarrierPlaquette, z4Planes],
      signedLink_mem_carrier_boundary link⟩
  · apply Prod.ext
    · exact signedAdd_zero_right link.1
    · rfl

/-! ## 6. Embedding the existing local cylinder roots -/

def natVertexToSigned : Z4Vertex → SignedZ4Vertex
  | (a, b, c, d) => (Int.ofNat a, Int.ofNat b, Int.ofNat c, Int.ofNat d)

def natLinkToSigned (link : Z4Link) : SignedZ4Link :=
  (natVertexToSigned link.1, link.2)

def natPlaquetteToSigned (plaquette : Z4Plaq) : SignedZ4Plaq :=
  (natVertexToSigned plaquette.1, plaquette.2)

def signedNatTimeShift (shift : Nat) : SignedZ4Vector :=
  (0, 0, 0, Int.ofNat shift)

theorem natPlaquetteToSigned_timeShift
    (shift : Nat) (plaquette : Z4Plaq) :
    natPlaquetteToSigned (timeShiftPlaquette shift plaquette) =
      signedTranslatePlaquette (signedNatTimeShift shift)
        (natPlaquetteToSigned plaquette) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp [natPlaquetteToSigned, natVertexToSigned, timeShiftPlaquette,
    timeShiftVertex, signedTranslatePlaquette, signedTranslateVertex,
    signedNatTimeShift, signedAdd]

def signedCanonicalRootSupport (base : Nat) (root : List Nat) :
    List SignedZ4Plaq :=
  (geometricPolymer base root).map natPlaquetteToSigned

theorem signedCanonicalRootSupport_timeShift
    {base shift : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    (∀ plaquette,
      plaquette ∈ signedCanonicalRootSupport (base + shift)
          (timeShiftCanonicalRoot shift base root) →
        plaquette ∈
          (signedCanonicalRootSupport base root).map
            (signedTranslatePlaquette (signedNatTimeShift shift))) ∧
    (∀ plaquette,
      plaquette ∈
          (signedCanonicalRootSupport base root).map
            (signedTranslatePlaquette (signedNatTimeShift shift)) →
        plaquette ∈ signedCanonicalRootSupport (base + shift)
          (timeShiftCanonicalRoot shift base root)) := by
  have hsame := timeShiftCanonicalRoot_sameSupport
    (shift := shift) hroot
  constructor
  · intro plaquette hplaquette
    obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hplaquette
    have hshifted := hsame.1 target htarget
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hshifted
    apply List.mem_map.mpr
    refine ⟨natPlaquetteToSigned source,
      List.mem_map.mpr ⟨source, hsource, rfl⟩, ?_⟩
    rw [← heq]
    exact natPlaquetteToSigned_timeShift shift source
  · intro plaquette hplaquette
    obtain ⟨sourceSigned, hsourceSigned, heq⟩ := List.mem_map.mp hplaquette
    obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hsourceSigned
    subst sourceSigned
    rw [← natPlaquetteToSigned_timeShift] at heq
    have hshifted : timeShiftPlaquette shift source ∈
        (geometricPolymer base root).map (timeShiftPlaquette shift) :=
      List.mem_map.mpr ⟨source, hsource, rfl⟩
    have htarget := hsame.2 _ hshifted
    change plaquette ∈
      (geometricPolymer (base + shift)
        (timeShiftCanonicalRoot shift base root)).map natPlaquetteToSigned
    exact List.mem_map.mpr
      ⟨timeShiftPlaquette shift source, htarget, heq⟩

#print axioms centeredSignedSlabVertices_translate
#print axioms centeredSignedSlabPlaquettes_translate
#print axioms centeredSignedSlabLinks_translate
#print axioms signedTranslateVertex_inverse_left
#print axioms signedTranslateVertex_inverse_right
#print axioms signedTranslatePlaquette_inverse_left
#print axioms signedTranslateLink_inverse_left
#print axioms signedSlabVertexTranslationBijection
#print axioms signedSlabPlaquetteTranslationBijection
#print axioms signedSlabLinkTranslationBijection
#print axioms signedVertex_mem_centered_zero_box_stage
#print axioms signedPlaquette_mem_centered_zero_box
#print axioms signedLink_mem_centered_zero_box
#print axioms signedCanonicalRootSupport_timeShift

end YMGap.Continuum.Z4SignedCenteredExhaustion
