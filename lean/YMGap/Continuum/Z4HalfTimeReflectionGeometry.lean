/-
# Boundary-complete half-time reflection geometry on the finite Z4 slab

The current physical cutoff enumerates plaquettes whose four *base*
coordinates are below `n`.  This is not a cubical cell complex closed under
reflection: a spatial plaquette on the bottom slice is reflected to the
missing top spatial slice.  The first section records that obstruction as a
kernel theorem, including the resulting failure of a physical-face reindex.

The rest of the file constructs the minimal boundary-complete replacement.
For maximum vertex time `M`, spatial plaquette bases occur on all slices
`0,...,M`, while time-oriented plaquette bases occur on `0,...,M-1`.
Reflection reverses vertices by `d |-> M-d`; the base point of an `x3` link
or time-oriented plaquette has the necessary additional unit shift.  The
resulting vertex, link, and plaquette lists are permuted by reflection and
actual edge incidence is preserved.

For odd `M = 2h+1`, the two refined spatial cube surfaces on the adjacent
central slices `h` and `h+1` are exchanged.  They are also re-encoded as
canonical numerical roots in the ambient box.  This supplies the genuine
finite reflection geometry needed by an Osterwalder--Schrader attack.  It
does not identify the corrected slab sum with the existing full-box physical
partition: the first-section obstruction proves that a face reindex for that
existing partition is unavailable until the boundary enumeration is changed.
-/

import YMGap.Continuum.Z4AdjacentTimeUnitCubeCylinder
import YMGap.Continuum.Z4UnitCubeEnumerationParity

namespace YMGap.Continuum.Z4HalfTimeReflectionGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4AdjacentTimeUnitCubeCylinder
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. Cell reflection and the obstruction in the current box -/

def timeReflectVertex (extent : Nat) : Z4Vertex -> Z4Vertex
  | (a, b, c, d) => (a, b, c, extent - d)

/-- Reversing a positively oriented time link reverses its geometric edge,
so its new positive-direction base is the reflected far endpoint. -/
def timeReflectLink (extent : Nat) : Z4Link -> Z4Link
  | ((a, b, c, d), .x0) => ((a, b, c, extent - d), .x0)
  | ((a, b, c, d), .x1) => ((a, b, c, extent - d), .x1)
  | ((a, b, c, d), .x2) => ((a, b, c, extent - d), .x2)
  | ((a, b, c, d), .x3) => ((a, b, c, extent - (d + 1)), .x3)

/-- Time-oriented plaquettes need the same base-point shift as time links. -/
def timeReflectPlaquette (extent : Nat) : Z4Plaq -> Z4Plaq
  | ((a, b, c, d), .p01) => ((a, b, c, extent - d), .p01)
  | ((a, b, c, d), .p02) => ((a, b, c, extent - d), .p02)
  | ((a, b, c, d), .p03) => ((a, b, c, extent - (d + 1)), .p03)
  | ((a, b, c, d), .p12) => ((a, b, c, extent - d), .p12)
  | ((a, b, c, d), .p13) => ((a, b, c, extent - (d + 1)), .p13)
  | ((a, b, c, d), .p23) => ((a, b, c, extent - (d + 1)), .p23)

def bottomSpatialPlaquette : Z4Plaq := ((0, 0, 0, 0), .p01)

theorem bottomSpatialPlaquette_mem_boxPlaquettes
    {n : Nat} (hn : 0 < n) :
    bottomSpatialPlaquette ∈ boxPlaquettes n := by
  rw [mem_boxPlaquettes]
  unfold bottomSpatialPlaquette
  exact ⟨hn, hn, hn, hn⟩

/-- The genuine vertex reversal `d |-> n-d` sends a bottom spatial face to
the absent slice `d=n` of the current base-coordinate box. -/
theorem timeReflect_bottomSpatialPlaquette_not_mem_boxPlaquettes
    (n : Nat) :
    timeReflectPlaquette n bottomSpatialPlaquette ∉ boxPlaquettes n := by
  rw [mem_boxPlaquettes]
  unfold timeReflectPlaquette bottomSpatialPlaquette
  simp only [Nat.sub_zero, not_and]
  intro _ _ _
  exact Nat.lt_irrefl n

/-- Trying the internal-slice reversal `d |-> (n-1)-d` does not repair the
geometry: the shifted base formula is already non-involutive on the top
time plaquette of the two-slice box. -/
theorem internalSliceReflection_not_involutive :
    timeReflectPlaquette 1
        (timeReflectPlaquette 1 ((0, 0, 0, 1), .p03)) ≠
      ((0, 0, 0, 1), .p03) := by
  decide

/-- The exact face-reindex identity required before a physical face labelling
can be reflected in the existing cutoff enumeration. -/
def PhysicalFaceReflectionClosed (n : Nat) : Prop :=
  ∀ id, id ∈ physicalFaceEdges n ->
    ∃ reflectedId, reflectedId ∈ physicalFaceEdges n ∧
      boxPlaquetteAt n reflectedId =
        timeReflectPlaquette n (boxPlaquetteAt n id)

/-- A single deterministic geometry-respecting face-coordinate reindex would
in particular imply `PhysicalFaceReflectionClosed`. -/
structure PhysicalFaceReflectionReindex (n : Nat) where
  reflectId : Nat -> Nat
  physical : ∀ id, id ∈ physicalFaceEdges n ->
    reflectId id ∈ physicalFaceEdges n
  geometric : ∀ id, id ∈ physicalFaceEdges n ->
    boxPlaquetteAt n (reflectId id) =
      timeReflectPlaquette n (boxPlaquetteAt n id)

/-- There is no such reindex at any nonempty cutoff.  Consequently an exact
`parametricKPhysicalTerm` reflection theorem cannot be obtained merely by
permuting the present physical face coordinates. -/
theorem not_physicalFaceReflectionClosed
    {n : Nat} (hn : 0 < n) : ¬ PhysicalFaceReflectionClosed n := by
  intro hclosed
  have hbottom := bottomSpatialPlaquette_mem_boxPlaquettes hn
  obtain ⟨id, hindexed⟩ := exists_mem_enumerate hbottom
  have hidPhysical : id ∈ physicalFaceEdges n := by
    unfold physicalFaceEdges plaquetteEdgeCount
    exact List.mem_range.mpr (enumerate_index_lt hindexed)
  obtain ⟨reflectedId, hreflectedPhysical, hreflectedEq⟩ :=
    hclosed id hidPhysical
  have hreflectedBox :=
    boxPlaquetteAt_mem_boxPlaquettes_of_physical hreflectedPhysical
  have hidEq : boxPlaquetteAt n id = bottomSpatialPlaquette :=
    boxPlaquetteAt_eq_of_enumerate hindexed
  rw [hreflectedEq, hidEq] at hreflectedBox
  exact timeReflect_bottomSpatialPlaquette_not_mem_boxPlaquettes n
    hreflectedBox

theorem no_physicalFaceReflectionReindex
    {n : Nat} (hn : 0 < n) : PhysicalFaceReflectionReindex n -> False := by
  intro reindex
  apply not_physicalFaceReflectionClosed hn
  intro id hid
  exact ⟨reindex.reflectId id, reindex.physical id hid,
    reindex.geometric id hid⟩

/-! ## 2. The boundary-complete slab -/

/-- Time bounds on positive-direction plaquette bases in a slab whose maximum
vertex time is `extent`. -/
def plaquetteTimeAdmissible (extent : Nat) (plaquette : Z4Plaq) : Prop :=
  match plaquette.2 with
  | .p01 | .p02 | .p12 => plaquette.1.2.2.2 ≤ extent
  | .p03 | .p13 | .p23 => plaquette.1.2.2.2 < extent

instance plaquetteTimeAdmissibleDecidable
    (extent : Nat) (plaquette : Z4Plaq) :
    Decidable (plaquetteTimeAdmissible extent plaquette) := by
  obtain ⟨vertex, plane⟩ := plaquette
  cases plane <;> unfold plaquetteTimeAdmissible <;> infer_instance

/-- Spatial bases include both boundary slices; temporal bases stop one slice
earlier.  Spatial coordinates retain the existing finite-box cutoff. -/
def boundaryCompleteSlabPlaquettes (extent : Nat) : List Z4Plaq :=
  (boxPlaquettes (extent + 1)).filter
    (fun plaquette => decide (plaquetteTimeAdmissible extent plaquette))

theorem mem_boundaryCompleteSlabPlaquettes
    (extent : Nat) (plaquette : Z4Plaq) :
    plaquette ∈ boundaryCompleteSlabPlaquettes extent ↔
      plaquette ∈ boxPlaquettes (extent + 1) ∧
        plaquetteTimeAdmissible extent plaquette := by
  simp [boundaryCompleteSlabPlaquettes]

theorem boundaryCompleteSlabPlaquettes_nodup (extent : Nat) :
    (boundaryCompleteSlabPlaquettes extent).Nodup := by
  unfold boundaryCompleteSlabPlaquettes
  exact List.filter_sublist.nodup (boxPlaquettes_nodup (extent + 1))

theorem timeReflectVertex_involutive
    (extent : Nat) (vertex : Z4Vertex)
    (htime : vertex.2.2.2 ≤ extent) :
    timeReflectVertex extent (timeReflectVertex extent vertex) = vertex := by
  obtain ⟨a, b, c, d⟩ := vertex
  change d ≤ extent at htime
  simp [timeReflectVertex]
  omega

theorem timeReflectVertex_mem_boxVertices
    {extent : Nat} {vertex : Z4Vertex}
    (hvertex : vertex ∈ boxVertices (extent + 1)) :
    timeReflectVertex extent vertex ∈ boxVertices (extent + 1) := by
  obtain ⟨a, b, c, d⟩ := vertex
  rw [mem_boxVertices] at hvertex ⊢
  simp only [timeReflectVertex]
  exact ⟨hvertex.1, hvertex.2.1, hvertex.2.2.1, by omega⟩

theorem vertexTime_le_extent_of_mem_boxVertices
    {extent : Nat} {vertex : Z4Vertex}
    (hvertex : vertex ∈ boxVertices (extent + 1)) :
    vertex.2.2.2 ≤ extent := by
  obtain ⟨a, b, c, d⟩ := vertex
  rw [mem_boxVertices] at hvertex
  exact Nat.le_of_lt_succ (by simpa only [Nat.add_comm] using hvertex.2.2.2)

/-- Vertex reversal is a permutation of the bounded vertex list. -/
theorem timeReflect_boxVertices_perm (extent : Nat) :
    ((boxVertices (extent + 1)).map (timeReflectVertex extent)).Perm
      (boxVertices (extent + 1)) := by
  apply perm_of_nodup_mem_iff
  · apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
      (timeReflectVertex extent)
      (boxVertices (extent + 1))
      (boxVertices_nodup (extent + 1))
    intro first hfirst second hsecond heq
    have hfirstTime := vertexTime_le_extent_of_mem_boxVertices hfirst
    have hsecondTime := vertexTime_le_extent_of_mem_boxVertices hsecond
    exact (timeReflectVertex_involutive extent first hfirstTime).symm.trans
      ((congrArg (timeReflectVertex extent) heq).trans
        (timeReflectVertex_involutive extent second hsecondTime))
  · exact boxVertices_nodup (extent + 1)
  · intro vertex
    constructor
    · intro hvertex
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hvertex
      rw [← hsourceEq]
      exact timeReflectVertex_mem_boxVertices hsource
    · intro hvertex
      have hreflected := timeReflectVertex_mem_boxVertices hvertex
      have htime := vertexTime_le_extent_of_mem_boxVertices hvertex
      exact List.mem_map.mpr
        ⟨timeReflectVertex extent vertex, hreflected,
          timeReflectVertex_involutive extent vertex htime⟩

theorem timeReflectPlaquette_involutive
    (extent : Nat) (plaquette : Z4Plaq)
    (hadmissible : plaquetteTimeAdmissible extent plaquette) :
    timeReflectPlaquette extent
        (timeReflectPlaquette extent plaquette) = plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp [plaquetteTimeAdmissible, timeReflectPlaquette] at hadmissible ⊢ <;>
    omega

theorem timeReflectPlaquette_admissible
    (extent : Nat) (plaquette : Z4Plaq)
    (hadmissible : plaquetteTimeAdmissible extent plaquette) :
    plaquetteTimeAdmissible extent
      (timeReflectPlaquette extent plaquette) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp [plaquetteTimeAdmissible, timeReflectPlaquette] at hadmissible ⊢ <;>
    omega

theorem timeReflectPlaquette_mem_box_extentSucc
    {extent : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes (extent + 1)) :
    timeReflectPlaquette extent plaquette ∈
      boxPlaquettes (extent + 1) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rw [mem_boxPlaquettes] at hplaquette ⊢
  cases plane <;> simp only [timeReflectPlaquette] <;>
    exact ⟨hplaquette.1, hplaquette.2.1, hplaquette.2.2.1,
      Nat.lt_succ_of_le (Nat.sub_le extent _)⟩

theorem timeReflectPlaquette_mem_boundaryCompleteSlab
    {extent : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boundaryCompleteSlabPlaquettes extent) :
    timeReflectPlaquette extent plaquette ∈
      boundaryCompleteSlabPlaquettes extent := by
  have hparts :=
    (mem_boundaryCompleteSlabPlaquettes extent plaquette).mp hplaquette
  apply (mem_boundaryCompleteSlabPlaquettes extent _).mpr
  exact ⟨timeReflectPlaquette_mem_box_extentSucc hparts.1,
    timeReflectPlaquette_admissible extent plaquette hparts.2⟩

/-- The corrected plaquette list, unlike the current full-box list, is
permuted by geometric time reflection. -/
theorem timeReflect_boundaryCompleteSlabPlaquettes_perm (extent : Nat) :
    ((boundaryCompleteSlabPlaquettes extent).map
        (timeReflectPlaquette extent)).Perm
      (boundaryCompleteSlabPlaquettes extent) := by
  apply perm_of_nodup_mem_iff
  · apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
      (timeReflectPlaquette extent)
      (boundaryCompleteSlabPlaquettes extent)
      (boundaryCompleteSlabPlaquettes_nodup extent)
    intro first hfirst second hsecond heq
    have hfirstAdmissible :=
      ((mem_boundaryCompleteSlabPlaquettes extent first).mp hfirst).2
    have hsecondAdmissible :=
      ((mem_boundaryCompleteSlabPlaquettes extent second).mp hsecond).2
    exact
      (timeReflectPlaquette_involutive extent first hfirstAdmissible).symm.trans
        ((congrArg (timeReflectPlaquette extent) heq).trans
          (timeReflectPlaquette_involutive extent second
            hsecondAdmissible))
  · exact boundaryCompleteSlabPlaquettes_nodup extent
  · intro plaquette
    constructor
    · intro hplaquette
      obtain ⟨source, hsource, hsourceEq⟩ :=
        List.mem_map.mp hplaquette
      rw [← hsourceEq]
      exact timeReflectPlaquette_mem_boundaryCompleteSlab hsource
    · intro hplaquette
      have hreflected :=
        timeReflectPlaquette_mem_boundaryCompleteSlab hplaquette
      have hadmissible :=
        ((mem_boundaryCompleteSlabPlaquettes extent plaquette).mp
          hplaquette).2
      exact List.mem_map.mpr
        ⟨timeReflectPlaquette extent plaquette, hreflected,
          timeReflectPlaquette_involutive extent plaquette hadmissible⟩

/-! ## 3. Boundary incidence and the reflected link list -/

def linkTimeAdmissible (extent : Nat) (link : Z4Link) : Prop :=
  match link.2 with
  | .x0 | .x1 | .x2 => link.1.2.2.2 ≤ extent
  | .x3 => link.1.2.2.2 < extent

theorem timeReflectLink_involutive
    (extent : Nat) (link : Z4Link)
    (hadmissible : linkTimeAdmissible extent link) :
    timeReflectLink extent (timeReflectLink extent link) = link := by
  obtain ⟨⟨a, b, c, d⟩, direction⟩ := link
  cases direction <;>
    simp [linkTimeAdmissible, timeReflectLink] at hadmissible ⊢ <;>
    omega

theorem timeReflectLink_admissible
    (extent : Nat) (link : Z4Link)
    (hadmissible : linkTimeAdmissible extent link) :
    linkTimeAdmissible extent (timeReflectLink extent link) := by
  obtain ⟨⟨a, b, c, d⟩, direction⟩ := link
  cases direction <;>
    simp [linkTimeAdmissible, timeReflectLink] at hadmissible ⊢ <;>
    omega

theorem linkTimeAdmissible_of_mem_edgesOf
    {extent : Nat} {plaquette : Z4Plaq} {link : Z4Link}
    (hplaquette : plaquetteTimeAdmissible extent plaquette)
    (hlink : link ∈ edgesOf plaquette) :
    linkTimeAdmissible extent link := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hlink <;>
    rcases hlink with rfl | rfl | rfl | rfl <;>
    simp only [plaquetteTimeAdmissible] at hplaquette <;>
    simp only [linkTimeAdmissible] <;>
    omega

private theorem permuteFirstAndThird {A : Type} (first second third fourth : A) :
    [third, second, first, fourth].Perm
      [first, second, third, fourth] := by
  exact (List.Perm.swap second third [first, fourth]).trans
    ((List.Perm.swap first third [fourth]).cons second |>.trans
      (List.Perm.swap first second [third, fourth]))

private theorem reflectedEdgesPerm
    (extent : Nat) (plaquette : Z4Plaq)
    (hplaquette : plaquetteTimeAdmissible extent plaquette) :
    ((edgesOf plaquette).map (timeReflectLink extent)).Perm
      (edgesOf (timeReflectPlaquette extent plaquette)) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane with
  | p01 => exact List.Perm.refl _
  | p02 => exact List.Perm.refl _
  | p12 => exact List.Perm.refl _
  | p03 =>
      have hd : d < extent := by
        simpa [plaquetteTimeAdmissible] using hplaquette
      have hshift : extent - (d + 1) + 1 = extent - d := by omega
      simpa [edgesOf, dirsOf, addE, timeReflectLink,
        timeReflectPlaquette, hshift] using
        (permuteFirstAndThird
          (((a, b, c, extent - (d + 1)), .x0) : Z4Link)
          (((a, b, c, extent - (d + 1)), .x3) : Z4Link)
          (((a, b, c, extent - d), .x0) : Z4Link)
          (((a + 1, b, c, extent - (d + 1)), .x3) : Z4Link))
  | p13 =>
      have hd : d < extent := by
        simpa [plaquetteTimeAdmissible] using hplaquette
      have hshift : extent - (d + 1) + 1 = extent - d := by omega
      simpa [edgesOf, dirsOf, addE, timeReflectLink,
        timeReflectPlaquette, hshift] using
        (permuteFirstAndThird
          (((a, b, c, extent - (d + 1)), .x1) : Z4Link)
          (((a, b, c, extent - (d + 1)), .x3) : Z4Link)
          (((a, b, c, extent - d), .x1) : Z4Link)
          (((a, b + 1, c, extent - (d + 1)), .x3) : Z4Link))
  | p23 =>
      have hd : d < extent := by
        simpa [plaquetteTimeAdmissible] using hplaquette
      have hshift : extent - (d + 1) + 1 = extent - d := by omega
      simpa [edgesOf, dirsOf, addE, timeReflectLink,
        timeReflectPlaquette, hshift] using
        (permuteFirstAndThird
          (((a, b, c, extent - (d + 1)), .x2) : Z4Link)
          (((a, b, c, extent - (d + 1)), .x3) : Z4Link)
          (((a, b, c, extent - d), .x2) : Z4Link)
          (((a, b, c + 1, extent - (d + 1)), .x3) : Z4Link))

/-- Reflection sends every genuine boundary edge to a genuine boundary edge
of the reflected plaquette.  The time-oriented cases exchange the near and
far spatial edges, which is why literal list equality would be wrong. -/
theorem timeReflectLink_mem_edgesOf_timeReflectPlaquette
    {extent : Nat} {plaquette : Z4Plaq} {link : Z4Link}
    (hplaquette : plaquetteTimeAdmissible extent plaquette)
    (hlink : link ∈ edgesOf plaquette) :
    timeReflectLink extent link ∈
      edgesOf (timeReflectPlaquette extent plaquette) := by
  have hmapped : timeReflectLink extent link ∈
      (edgesOf plaquette).map (timeReflectLink extent) :=
    List.mem_map.mpr ⟨link, hlink, rfl⟩
  exact (List.Perm.mem_iff
    (reflectedEdgesPerm extent plaquette hplaquette)).mp hmapped

/-- At the list level, reflection permutes (rather than literally preserves)
the four boundary edges of a plaquette. -/
theorem timeReflect_edgesOf_perm
    (extent : Nat) (plaquette : Z4Plaq)
    (hplaquette : plaquetteTimeAdmissible extent plaquette) :
    ((edgesOf plaquette).map (timeReflectLink extent)).Perm
      (edgesOf (timeReflectPlaquette extent plaquette)) := by
  exact reflectedEdgesPerm extent plaquette hplaquette

def boundaryCompleteSlabLinks (extent : Nat) : List Z4Link :=
  ((boundaryCompleteSlabPlaquettes extent).flatMap edgesOf).eraseDups

private theorem filteredEraseDupsNodup {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) :
    ∀ predicate : A → Bool, (xs.filter predicate).eraseDups.Nodup := by
  induction xs with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr
          ⟨?_, ih (fun item => (!(item == head)) && predicate item)⟩
        intro hmem
        have hmem' : head ∈ tail.filter
            (fun item => (!(item == head)) && predicate item) :=
          List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hmem').2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih predicate

private theorem filterTrueLocal {A : Type} :
    ∀ xs : List A, xs.filter (fun _ => true) = xs
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) : xs.eraseDups.Nodup := by
  have h := filteredEraseDupsNodup xs (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

theorem mem_boundaryCompleteSlabLinks_iff
    (extent : Nat) (link : Z4Link) :
    link ∈ boundaryCompleteSlabLinks extent ↔
      ∃ plaquette, plaquette ∈ boundaryCompleteSlabPlaquettes extent ∧
        link ∈ edgesOf plaquette := by
  simp [boundaryCompleteSlabLinks]

theorem boundaryCompleteSlabLinks_nodup (extent : Nat) :
    (boundaryCompleteSlabLinks extent).Nodup := by
  unfold boundaryCompleteSlabLinks
  exact eraseDupsNodupLocal _

theorem linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks
    {extent : Nat} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    linkTimeAdmissible extent link := by
  obtain ⟨plaquette, hplaquette, hedge⟩ :=
    (mem_boundaryCompleteSlabLinks_iff extent link).mp hlink
  exact linkTimeAdmissible_of_mem_edgesOf
    ((mem_boundaryCompleteSlabPlaquettes extent plaquette).mp hplaquette).2
    hedge

theorem timeReflectLink_mem_boundaryCompleteSlabLinks
    {extent : Nat} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    timeReflectLink extent link ∈ boundaryCompleteSlabLinks extent := by
  obtain ⟨plaquette, hplaquette, hedge⟩ :=
    (mem_boundaryCompleteSlabLinks_iff extent link).mp hlink
  apply (mem_boundaryCompleteSlabLinks_iff extent _).mpr
  exact ⟨timeReflectPlaquette extent plaquette,
    timeReflectPlaquette_mem_boundaryCompleteSlab hplaquette,
    timeReflectLink_mem_edgesOf_timeReflectPlaquette
      ((mem_boundaryCompleteSlabPlaquettes extent plaquette).mp hplaquette).2
      hedge⟩

/-- Reflection is also a permutation of the deduplicated actual-link list. -/
theorem timeReflect_boundaryCompleteSlabLinks_perm (extent : Nat) :
    ((boundaryCompleteSlabLinks extent).map
        (timeReflectLink extent)).Perm
      (boundaryCompleteSlabLinks extent) := by
  apply perm_of_nodup_mem_iff
  · apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
      (timeReflectLink extent)
      (boundaryCompleteSlabLinks extent)
      (boundaryCompleteSlabLinks_nodup extent)
    intro first hfirst second hsecond heq
    have hfirstAdmissible :=
      linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks hfirst
    have hsecondAdmissible :=
      linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks hsecond
    exact (timeReflectLink_involutive extent first hfirstAdmissible).symm.trans
      ((congrArg (timeReflectLink extent) heq).trans
        (timeReflectLink_involutive extent second hsecondAdmissible))
  · exact boundaryCompleteSlabLinks_nodup extent
  · intro link
    constructor
    · intro hlink
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hlink
      rw [← hsourceEq]
      exact timeReflectLink_mem_boundaryCompleteSlabLinks hsource
    · intro hlink
      have hreflected := timeReflectLink_mem_boundaryCompleteSlabLinks hlink
      have hadmissible :=
        linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks hlink
      exact List.mem_map.mpr
        ⟨timeReflectLink extent link, hreflected,
          timeReflectLink_involutive extent link hadmissible⟩

/-! ## 4. Finite face-spin states on the corrected slab -/

/-- A finite association list of geometric faces and representation labels.
The physical cutoff uses numerical face IDs instead; this geometric state is
the boundary-complete object on which reflection is genuinely defined. -/
abbrev SlabFaceSpinState : Type := List (Z4Plaq × Nat)

def slabFaceSpinStateAdmissible
    (extent : Nat) (state : SlabFaceSpinState) : Prop :=
  ∀ entry, entry ∈ state ->
    entry.1 ∈ boundaryCompleteSlabPlaquettes extent

def slabFaceSpinStateBounded
    (cutoff : Nat) (state : SlabFaceSpinState) : Prop :=
  ∀ entry, entry ∈ state -> entry.2 ≤ cutoff

def timeReflectSlabFaceSpinState
    (extent : Nat) (state : SlabFaceSpinState) : SlabFaceSpinState :=
  state.map fun entry =>
    (timeReflectPlaquette extent entry.1, entry.2)

theorem timeReflectSlabFaceSpinState_admissible
    {extent : Nat} {state : SlabFaceSpinState}
    (hadmissible : slabFaceSpinStateAdmissible extent state) :
    slabFaceSpinStateAdmissible extent
      (timeReflectSlabFaceSpinState extent state) := by
  intro entry hentry
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hentry
  rw [← hsourceEq]
  exact timeReflectPlaquette_mem_boundaryCompleteSlab
    (hadmissible source hsource)

theorem timeReflectSlabFaceSpinState_bounded
    {extent cutoff : Nat} {state : SlabFaceSpinState}
    (hbounded : slabFaceSpinStateBounded cutoff state) :
    slabFaceSpinStateBounded cutoff
      (timeReflectSlabFaceSpinState extent state) := by
  intro entry hentry
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hentry
  rw [← hsourceEq]
  exact hbounded source hsource

/-- The corrected finite face-spin reflection is an involution and leaves
every spin value unchanged. -/
theorem timeReflectSlabFaceSpinState_involutive
    {extent : Nat} {state : SlabFaceSpinState}
    (hadmissible : slabFaceSpinStateAdmissible extent state) :
    timeReflectSlabFaceSpinState extent
        (timeReflectSlabFaceSpinState extent state) = state := by
  induction state with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨plaquette, spin⟩ := entry
      simp only [timeReflectSlabFaceSpinState, List.map]
      have hplaquette :=
        hadmissible (plaquette, spin) List.mem_cons_self
      rw [timeReflectPlaquette_involutive extent plaquette
        ((mem_boundaryCompleteSlabPlaquettes extent plaquette).mp
          hplaquette).2]
      apply congrArg (List.cons (plaquette, spin))
      apply ih
      intro tailEntry htailEntry
      exact hadmissible tailEntry
        (List.mem_cons_of_mem (plaquette, spin) htailEntry)

/-! ## 5. Adjacent central cube surfaces in an even ambient box -/

/-- An arbitrary positive Euclidean-time shift. -/
def timeShiftVertex (shift : Nat) : Z4Vertex -> Z4Vertex
  | (a, b, c, d) => (a, b, c, d + shift)

def timeShiftLink (shift : Nat) (link : Z4Link) : Z4Link :=
  (timeShiftVertex shift link.1, link.2)

def timeShiftPlaquette (shift : Nat) (plaquette : Z4Plaq) : Z4Plaq :=
  (timeShiftVertex shift plaquette.1, plaquette.2)

theorem timeShiftVertex_addE
    (shift : Nat) (vertex : Z4Vertex) (direction : Dir4) :
    timeShiftVertex shift (addE vertex direction) =
      addE (timeShiftVertex shift vertex) direction := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction <;> simp [timeShiftVertex, addE] <;> omega

theorem edgesOf_timeShiftPlaquette
    (shift : Nat) (plaquette : Z4Plaq) :
    edgesOf (timeShiftPlaquette shift plaquette) =
      (edgesOf plaquette).map (timeShiftLink shift) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;> simp [timeShiftPlaquette, timeShiftLink,
    timeShiftVertex, edgesOf, dirsOf, addE] <;> omega

def timeShiftAdjacent (shift : Nat) {left right : Z4Plaq}
    (adjacent : z4Chain.toLattice.Adjacent left right) :
    z4Chain.toLattice.Adjacent
      (timeShiftPlaquette shift left)
      (timeShiftPlaquette shift right) := by
  refine {
    link := timeShiftLink shift adjacent.link
    on_p := ?_
    on_q := ?_
  }
  · change z4Boundary (timeShiftPlaquette shift left)
      (timeShiftLink shift adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_timeShiftPlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_p, rfl⟩
  · change z4Boundary (timeShiftPlaquette shift right)
      (timeShiftLink shift adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_timeShiftPlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_q, rfl⟩

def timeShiftChain (shift : Nat) {support : List Z4Plaq} :
    {first last : Z4Plaq} ->
      ChainIn z4Chain.toLattice support first last ->
      ChainIn z4Chain.toLattice
        (support.map (timeShiftPlaquette shift))
        (timeShiftPlaquette shift first)
        (timeShiftPlaquette shift last)
  | _, _, .refl plaquette => .refl _
  | _, _, .step adjacent hnext rest =>
      .step (timeShiftAdjacent shift adjacent)
        (List.mem_map.mpr ⟨_, hnext, rfl⟩)
        (timeShiftChain shift rest)

def centeredCubeSurface (time : Nat) : List Z4Plaq :=
  refinedUnitCubeSurface.map (timeShiftPlaquette time)

def centeredCubeSurface_connected (time : Nat) :
    connectedIn (L := z4Chain.toLattice) (centeredCubeSurface time) := by
  intro first last hfirst hlast
  obtain ⟨sourceFirst, hsourceFirst, hfirstEq⟩ :=
    decodeMapMember (timeShiftPlaquette time)
      refinedUnitCubeSurface first hfirst
  obtain ⟨sourceLast, hsourceLast, hlastEq⟩ :=
    decodeMapMember (timeShiftPlaquette time)
      refinedUnitCubeSurface last hlast
  rw [← hfirstEq, ← hlastEq]
  exact timeShiftChain time
    (refinedUnitCubeSurface_connected
      sourceFirst sourceLast hsourceFirst hsourceLast)

theorem centeredCubeSurface_timeCoordinate
    {time : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ centeredCubeSurface time) :
    plaquette.1.2.2.2 = time := by
  obtain ⟨source, hsource, hsourceEq⟩ :=
    decodeMapMember (timeShiftPlaquette time)
      refinedUnitCubeSurface plaquette hplaquette
  rw [← hsourceEq]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  have hzero := refinedUnitCubeSurface_timeCoordinate_zero hsource
  change d = 0 at hzero
  simp only [timeShiftPlaquette, timeShiftVertex]
  rw [hzero]
  exact Nat.zero_add time

theorem centeredCubeSurface_spatialPlane
    {time : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ centeredCubeSurface time) :
    plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12 := by
  obtain ⟨source, hsource, hsourceEq⟩ :=
    decodeMapMember (timeShiftPlaquette time)
      refinedUnitCubeSurface plaquette hplaquette
  rw [← hsourceEq]
  simpa [timeShiftPlaquette] using
    (refinedUnitCubeSurface_spatialPlane hsource)

theorem centeredCubeSurface_subset_box
    {time ambient : Nat} (hspace : 4 ≤ ambient) (htime : time < ambient) :
    ∀ plaquette, plaquette ∈ centeredCubeSurface time ->
      plaquette ∈ boxPlaquettes ambient := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, hsourceEq⟩ :=
    decodeMapMember (timeShiftPlaquette time)
      refinedUnitCubeSurface plaquette hplaquette
  rw [← hsourceEq]
  have hbox := refinedUnitCubeSurface_subset_box_four source hsource
  have hzero := refinedUnitCubeSurface_timeCoordinate_zero hsource
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  rw [mem_boxPlaquettes] at hbox ⊢
  simp [timeShiftPlaquette, timeShiftVertex] at hzero ⊢
  exact ⟨Nat.lt_of_lt_of_le hbox.1 hspace,
    Nat.lt_of_lt_of_le hbox.2.1 hspace,
    Nat.lt_of_lt_of_le hbox.2.2.1 hspace, by omega⟩

/-- Odd reflection extent and its even number of vertex slices. -/
def centralExtent (half : Nat) : Nat := half + half + 1

def centralAmbient (half : Nat) : Nat := centralExtent half + 1

def centralLowerCubeSurface (half : Nat) : List Z4Plaq :=
  centeredCubeSurface half

def centralUpperCubeSurface (half : Nat) : List Z4Plaq :=
  centeredCubeSurface (half + 1)

theorem centralAmbient_eq (half : Nat) :
    centralAmbient half = 2 * (half + 1) := by
  unfold centralAmbient centralExtent
  omega

theorem centralLowerCubeSurface_subset_slab
    {half : Nat} (hhalf : 1 ≤ half) :
    ∀ plaquette, plaquette ∈ centralLowerCubeSurface half ->
      plaquette ∈ boundaryCompleteSlabPlaquettes (centralExtent half) := by
  intro plaquette hplaquette
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  refine ⟨?_, ?_⟩
  · change plaquette ∈ boxPlaquettes (centralAmbient half)
    exact centeredCubeSurface_subset_box (by
      unfold centralAmbient centralExtent
      omega) (by unfold centralAmbient centralExtent; omega)
      plaquette hplaquette
  · have htime := centeredCubeSurface_timeCoordinate hplaquette
    have hplane := centeredCubeSurface_spatialPlane hplaquette
    rcases hplane with hplane | hplane | hplane
    all_goals unfold plaquetteTimeAdmissible
    all_goals rw [hplane, htime]
    all_goals unfold centralExtent
    all_goals omega

theorem centralUpperCubeSurface_subset_slab
    {half : Nat} (hhalf : 1 ≤ half) :
    ∀ plaquette, plaquette ∈ centralUpperCubeSurface half ->
      plaquette ∈ boundaryCompleteSlabPlaquettes (centralExtent half) := by
  intro plaquette hplaquette
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  refine ⟨?_, ?_⟩
  · change plaquette ∈ boxPlaquettes (centralAmbient half)
    exact centeredCubeSurface_subset_box (by
      unfold centralAmbient centralExtent
      omega) (by unfold centralAmbient centralExtent; omega)
      plaquette hplaquette
  · have htime := centeredCubeSurface_timeCoordinate hplaquette
    have hplane := centeredCubeSurface_spatialPlane hplaquette
    rcases hplane with hplane | hplane | hplane
    all_goals unfold plaquetteTimeAdmissible
    all_goals rw [hplane, htime]
    all_goals unfold centralExtent
    all_goals omega

theorem timeReflect_timeShift_lower_eq_upper
    (half : Nat) (plaquette : Z4Plaq)
    (htime : plaquette.1.2.2.2 = 0)
    (hplane : plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12) :
    timeReflectPlaquette (centralExtent half)
        (timeShiftPlaquette half plaquette) =
      timeShiftPlaquette (half + 1) plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rcases hplane with rfl | rfl | rfl <;>
    simp [centralExtent, timeReflectPlaquette,
      timeShiftPlaquette, timeShiftVertex] at htime ⊢ <;>
    omega

theorem timeReflect_timeShift_upper_eq_lower
    (half : Nat) (plaquette : Z4Plaq)
    (htime : plaquette.1.2.2.2 = 0)
    (hplane : plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12) :
    timeReflectPlaquette (centralExtent half)
        (timeShiftPlaquette (half + 1) plaquette) =
      timeShiftPlaquette half plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rcases hplane with rfl | rfl | rfl <;>
    simp [centralExtent, timeReflectPlaquette,
      timeShiftPlaquette, timeShiftVertex] at htime ⊢ <;>
    omega

/-- The two adjacent central cube surfaces are exchanged exactly, cell for
cell, by the corrected half-time reflection. -/
theorem timeReflect_centralLowerCubeSurface_eq_upper (half : Nat) :
    (centralLowerCubeSurface half).map
        (timeReflectPlaquette (centralExtent half)) =
      centralUpperCubeSurface half := by
  unfold centralLowerCubeSurface centralUpperCubeSurface centeredCubeSurface
  rw [List.map_map]
  apply List.map_congr_left
  intro plaquette hplaquette
  simp only [Function.comp_apply]
  exact timeReflect_timeShift_lower_eq_upper half plaquette
    (refinedUnitCubeSurface_timeCoordinate_zero hplaquette)
    (refinedUnitCubeSurface_spatialPlane hplaquette)

theorem timeReflect_centralUpperCubeSurface_eq_lower (half : Nat) :
    (centralUpperCubeSurface half).map
        (timeReflectPlaquette (centralExtent half)) =
      centralLowerCubeSurface half := by
  unfold centralLowerCubeSurface centralUpperCubeSurface centeredCubeSurface
  rw [List.map_map]
  apply List.map_congr_left
  intro plaquette hplaquette
  simp only [Function.comp_apply]
  exact timeReflect_timeShift_upper_eq_lower half plaquette
    (refinedUnitCubeSurface_timeCoordinate_zero hplaquette)
    (refinedUnitCubeSurface_spatialPlane hplaquette)

/-! ## 6. Canonical numerical roots and their geometric exchange -/

def centeredCubeSupportIds (ambient time : Nat) : List Nat :=
  geometricSupportIds ambient (centeredCubeSurface time)

theorem centeredCubeSupportIds_sameSupport
    {ambient time : Nat} (hspace : 4 ≤ ambient) (htime : time < ambient) :
    sameSupport
      (geometricPolymer ambient (centeredCubeSupportIds ambient time))
      (centeredCubeSurface time) := by
  unfold centeredCubeSupportIds
  exact geometricSupportIds_sameSupport
    (centeredCubeSurface_subset_box hspace htime)

theorem centeredCubeSupportIds_canonical
    {ambient time : Nat} (hspace : 4 ≤ ambient) (htime : time < ambient) :
    centeredCubeSupportIds ambient time ∈
      canonicalSurfacePolymers ambient := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · unfold centeredCubeSupportIds
    exact geometricSupportIds_mem_cutoffOneFaceSupports
      ambient (centeredCubeSurface time)
  · have hsame := centeredCubeSupportIds_sameSupport hspace htime
    have htranslatedHub : timeShiftPlaquette time refinedCubeHub ∈
        centeredCubeSurface time := by
      unfold centeredCubeSurface
      exact List.mem_map.mpr
        ⟨refinedCubeHub,
          refinedCubeCell_mem .bottomXY .origin, rfl⟩
    have hhub : timeShiftPlaquette time refinedCubeHub ∈
        geometricPolymer ambient (centeredCubeSupportIds ambient time) :=
      hsame.2 _ htranslatedHub
    obtain ⟨identifier, hidentifier, _⟩ :=
      decodeMapMember (boxPlaquetteAt ambient)
        (centeredCubeSupportIds ambient time)
        (timeShiftPlaquette time refinedCubeHub) hhub
    exact ⟨identifier, hidentifier⟩
  · unfold centeredCubeSupportIds
    exact geometricSupportIds_connected
      (centeredCubeSurface_subset_box hspace htime)
      (centeredCubeSurface_connected time)

def centralLowerCubeRoot (half : Nat) : List Nat :=
  centeredCubeSupportIds (centralAmbient half) half

def centralUpperCubeRoot (half : Nat) : List Nat :=
  centeredCubeSupportIds (centralAmbient half) (half + 1)

theorem centralLowerCubeRoot_canonical
    {half : Nat} (hhalf : 1 ≤ half) :
    centralLowerCubeRoot half ∈
      canonicalSurfacePolymers (centralAmbient half) := by
  unfold centralLowerCubeRoot
  apply centeredCubeSupportIds_canonical
  · unfold centralAmbient centralExtent
    omega
  · unfold centralAmbient centralExtent
    omega

theorem centralUpperCubeRoot_canonical
    {half : Nat} (hhalf : 1 ≤ half) :
    centralUpperCubeRoot half ∈
      canonicalSurfacePolymers (centralAmbient half) := by
  unfold centralUpperCubeRoot
  apply centeredCubeSupportIds_canonical
  · unfold centralAmbient centralExtent
    omega
  · unfold centralAmbient centralExtent
    omega

theorem centralLowerCubeRoot_sameSupport
    {half : Nat} (hhalf : 1 ≤ half) :
    sameSupport
      (geometricPolymer (centralAmbient half) (centralLowerCubeRoot half))
      (centralLowerCubeSurface half) := by
  unfold centralLowerCubeRoot centralLowerCubeSurface
  apply centeredCubeSupportIds_sameSupport
  · unfold centralAmbient centralExtent
    omega
  · unfold centralAmbient centralExtent
    omega

theorem centralUpperCubeRoot_sameSupport
    {half : Nat} (hhalf : 1 ≤ half) :
    sameSupport
      (geometricPolymer (centralAmbient half) (centralUpperCubeRoot half))
      (centralUpperCubeSurface half) := by
  unfold centralUpperCubeRoot centralUpperCubeSurface
  apply centeredCubeSupportIds_sameSupport
  · unfold centralAmbient centralExtent
    omega
  · unfold centralAmbient centralExtent
    omega

/-- Reflection exchanges the actual geometric plaquettes decoded from the two
canonical numerical roots. -/
theorem timeReflect_mem_centralUpperCubeRoot
    {half : Nat} (hhalf : 1 ≤ half) {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈
      geometricPolymer (centralAmbient half) (centralLowerCubeRoot half)) :
    timeReflectPlaquette (centralExtent half) plaquette ∈
      geometricPolymer (centralAmbient half) (centralUpperCubeRoot half) := by
  have hlower :=
    (centralLowerCubeRoot_sameSupport hhalf).1 plaquette hplaquette
  have hreflected : timeReflectPlaquette (centralExtent half) plaquette ∈
      (centralLowerCubeSurface half).map
        (timeReflectPlaquette (centralExtent half)) :=
    List.mem_map.mpr ⟨plaquette, hlower, rfl⟩
  rw [timeReflect_centralLowerCubeSurface_eq_upper] at hreflected
  exact (centralUpperCubeRoot_sameSupport hhalf).2 _ hreflected

theorem timeReflect_mem_centralLowerCubeRoot
    {half : Nat} (hhalf : 1 ≤ half) {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈
      geometricPolymer (centralAmbient half) (centralUpperCubeRoot half)) :
    timeReflectPlaquette (centralExtent half) plaquette ∈
      geometricPolymer (centralAmbient half) (centralLowerCubeRoot half) := by
  have hupper :=
    (centralUpperCubeRoot_sameSupport hhalf).1 plaquette hplaquette
  have hreflected : timeReflectPlaquette (centralExtent half) plaquette ∈
      (centralUpperCubeSurface half).map
        (timeReflectPlaquette (centralExtent half)) :=
    List.mem_map.mpr ⟨plaquette, hupper, rfl⟩
  rw [timeReflect_centralUpperCubeSurface_eq_lower] at hreflected
  exact (centralLowerCubeRoot_sameSupport hhalf).2 _ hreflected

/-! ## Axiom audit -/

#print axioms timeReflect_bottomSpatialPlaquette_not_mem_boxPlaquettes
#print axioms not_physicalFaceReflectionClosed
#print axioms no_physicalFaceReflectionReindex
#print axioms timeReflect_boxVertices_perm
#print axioms timeReflect_boundaryCompleteSlabPlaquettes_perm
#print axioms timeReflect_edgesOf_perm
#print axioms timeReflect_boundaryCompleteSlabLinks_perm
#print axioms timeReflectSlabFaceSpinState_involutive
#print axioms centeredCubeSurface_connected
#print axioms centralLowerCubeSurface_subset_slab
#print axioms centralUpperCubeSurface_subset_slab
#print axioms timeReflect_centralLowerCubeSurface_eq_upper
#print axioms centralLowerCubeRoot_canonical
#print axioms centralUpperCubeRoot_canonical
#print axioms timeReflect_mem_centralUpperCubeRoot
#print axioms timeReflect_mem_centralLowerCubeRoot

#print axioms plaquetteTimeAdmissibleDecidable
#print axioms mem_boundaryCompleteSlabPlaquettes
#print axioms boundaryCompleteSlabPlaquettes_nodup
#print axioms timeReflectPlaquette_involutive
#print axioms timeReflectPlaquette_admissible
#print axioms timeReflectPlaquette_mem_boundaryCompleteSlab
#print axioms linkTimeAdmissible_of_mem_edgesOf
#print axioms timeReflectLink_mem_edgesOf_timeReflectPlaquette
#print axioms centeredCubeSurface_subset_box
#print axioms centeredCubeSurface_timeCoordinate
#print axioms centeredCubeSurface_spatialPlane

end YMGap.Continuum.Z4HalfTimeReflectionGeometry
