/-
# Bulk placement in the ORIGINAL four-dimensional slab family

Spatial coordinates are shifted together, independently of the time shift.
The target numerical face ID is found in the actual boundary-complete list.
At half-size enlargement n and outward lag l<=n, the bulk placement shifts
space by n and time by n-l. Reflection retains the spatial shift and changes
the temporal shift to n+l. This extends, rather than identifies with, the
previous time-only embeddings.

Every endpoint of every translated plaquette edge has an explicit margin
n-l from all target box boundaries. Thus padding l+r supplies margin r as
constructive data for a fixed lag. This is geometric exhaustion, not a
comparison of actions, probability functionals, or completed norms.
-/

import YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry

namespace YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry

def shiftVertex (space time : Nat) : Z4Vertex → Z4Vertex
  | (a, b, c, d) => (a+space, b+space, c+space, d+time)

def shiftLink (space time : Nat) (link : Z4Link) : Z4Link := (shiftVertex space time link.1, link.2)

def shiftFace (space time : Nat) (p : Z4Plaq) : Z4Plaq := (shiftVertex space time p.1, p.2)

theorem shiftFace_time (time : Nat) (p : Z4Plaq) : shiftFace 0 time p = timeShiftPlaquette time p := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  rfl

theorem shiftFace_injective (space time : Nat) {p q : Z4Plaq}
    (h : shiftFace space time p = shiftFace space time q) : p = q := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  obtain ⟨⟨a', b', c', d'⟩, plane'⟩ := q
  simpa only [shiftFace, shiftVertex, Prod.mk.injEq, Nat.add_right_cancel_iff] using h

theorem shiftFace_comp (r s r' s' : Nat) (p : Z4Plaq) :
    shiftFace r' s' (shiftFace r s p) = shiftFace (r+r') (s+s') p := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  simp only [shiftFace, shiftVertex, Nat.add_assoc]

theorem shiftVertex_addE (space time : Nat) (v : Z4Vertex) (direction : Dir4) :
    shiftVertex space time (addE v direction) = addE (shiftVertex space time v) direction := by
  obtain ⟨a, b, c, d⟩ := v
  cases direction <;> simp [shiftVertex, addE] <;> omega

theorem edgesOf_shiftFace (space time : Nat) (p : Z4Plaq) :
    edgesOf (shiftFace space time p) = (edgesOf p).map (shiftLink space time) := by
  simp only [edgesOf, shiftFace, shiftLink, List.map_cons, List.map_nil, shiftVertex_addE]

theorem shiftFace_mem {source target space time : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    {p : Z4Plaq} (hp : p ∈ boundaryCompleteSlabPlaquettes source) :
    shiftFace space time p ∈ boundaryCompleteSlabPlaquettes target := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  obtain ⟨hbox, hadmissible⟩ := (mem_boundaryCompleteSlabPlaquettes _ _).mp hp
  rw [mem_boxPlaquettes] at hbox
  change a < source+1 ∧ b < source+1 ∧ c < source+1 ∧ d < source+1 at hbox
  have hd : d ≤ source := by
    cases plane <;> simp only [plaquetteTimeAdmissible] at hadmissible <;> omega
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  constructor
  · rw [mem_boxPlaquettes]
    change a+space < target+1 ∧ b+space < target+1 ∧ c+space < target+1 ∧ d+time < target+1
    exact ⟨by omega, by omega, by omega, by omega⟩
  · cases plane <;> simp only [shiftFace, shiftVertex, plaquetteTimeAdmissible] at hadmissible ⊢ <;> omega

theorem shiftLink_mem {source target space time : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    {link : Z4Link} (hl : link ∈ boundaryCompleteSlabLinks source) :
    shiftLink space time link ∈ boundaryCompleteSlabLinks target := by
  obtain ⟨p, hp, hedge⟩ := (mem_boundaryCompleteSlabLinks_iff _ _).mp hl
  refine (mem_boundaryCompleteSlabLinks_iff _ _).mpr ⟨shiftFace space time p, shiftFace_mem hr ht hp, ?_⟩
  rw [edgesOf_shiftFace]
  exact List.mem_map.mpr ⟨link, hedge, rfl⟩

def shiftFaceId (source target space time id : Nat) : Nat :=
  listIndexOf (shiftFace space time (slabPlaquetteAt source id)) (boundaryCompleteSlabPlaquettes target)

theorem shiftFaceId_physical {source target space time id : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target) (hi : id ∈ slabPhysicalFaceEdges source) :
    shiftFaceId source target space time id ∈ slabPhysicalFaceEdges target :=
  List.mem_range.mpr (listIndexOf_lt_of_mem _ _ (shiftFace_mem hr ht (slabPlaquetteAt_mem hi)))

theorem shiftFaceId_pin {source target space time id : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target) (hi : id ∈ slabPhysicalFaceEdges source) :
    slabPlaquetteAt target (shiftFaceId source target space time id) = shiftFace space time (slabPlaquetteAt source id) :=
  getD_listIndexOf_of_mem _ _ _ (shiftFace_mem hr ht (slabPlaquetteAt_mem hi))

theorem shiftFaceId_injective {source target space time i j : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    (hi : i ∈ slabPhysicalFaceEdges source) (hj : j ∈ slabPhysicalFaceEdges source)
    (h : shiftFaceId source target space time i = shiftFaceId source target space time j) : i = j := by
  apply slabPlaquetteAt_injective_on_physical hi hj
  apply shiftFace_injective space time
  rw [← shiftFaceId_pin hr ht hi, ← shiftFaceId_pin hr ht hj, h]

theorem shiftFaceId_zero {source id : Nat} (hi : id ∈ slabPhysicalFaceEdges source) :
    shiftFaceId source source 0 0 id = id := by
  change listIndexOf _ _ = id
  rw [shiftFace_time]
  exact faceId_zero hi

theorem shiftFace_lower {half n space time : Nat} (ht : time ≤ n)
    {p : Z4Plaq} (hp : plaquetteHalfSide half p = .lower) :
    plaquetteHalfSide (half+n) (shiftFace space time p) = .lower := by
  have h := lower_shift ht hp
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  cases plane <;> exact h

theorem shiftFace_reflection {half n space time : Nat} (ht : time ≤ n+n)
    {p : Z4Plaq} (hp : plaquetteTimeAdmissible (centralExtent half) p) :
    timeReflectPlaquette (centralExtent (half+n)) (shiftFace space time p) =
      shiftFace space (n+n-time) (timeReflectPlaquette (centralExtent half) p) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  cases plane <;> simp [shiftFace, shiftVertex, timeReflectPlaquette, centralExtent,
    plaquetteTimeAdmissible] at hp ⊢ <;> omega

/-- Every actual edge endpoint, including the far boundary vertices. -/
def boundaryVertices (p : Z4Plaq) : List Z4Vertex :=
  (edgesOf p).flatMap (fun link => [link.1, addE link.1 link.2])

/-- Spatial links may end at extent+1; the maximum time vertex is extent. -/
def VertexInset (extent margin : Nat) (v : Z4Vertex) : Prop :=
  margin ≤ v.1 ∧ v.1+margin ≤ extent+1 ∧
  margin ≤ v.2.1 ∧ v.2.1+margin ≤ extent+1 ∧
  margin ≤ v.2.2.1 ∧ v.2.2.1+margin ≤ extent+1 ∧
  margin ≤ v.2.2.2 ∧ v.2.2.2+margin ≤ extent

theorem boundary_vertex_inset_zero {extent : Nat} {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent) {v : Z4Vertex}
    (hv : v ∈ boundaryVertices p) : VertexInset extent 0 v := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  obtain ⟨hbox, htime⟩ := (mem_boundaryCompleteSlabPlaquettes _ _).mp hp
  rw [mem_boxPlaquettes] at hbox
  change a < extent+1 ∧ b < extent+1 ∧ c < extent+1 ∧ d < extent+1 at hbox
  obtain ⟨link, hl, hv⟩ := List.mem_flatMap.mp hv
  cases plane <;>
    simp only [plaquetteTimeAdmissible] at htime <;>
    simp only [edgesOf, dirsOf, List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals
    rcases hl with rfl | rfl | rfl | rfl
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      all_goals
        simp only [VertexInset, addE, Nat.add_zero]
        repeat' apply And.intro
        all_goals omega

theorem shifted_vertex_inset {source target margin space time : Nat}
    (hr : margin ≤ space) (ht : margin ≤ time)
    (hrtop : source+space+margin ≤ target) (httop : source+time+margin ≤ target)
    {v : Z4Vertex} (hv : VertexInset source 0 v) : VertexInset target margin (shiftVertex space time v) := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [VertexInset, shiftVertex, Nat.add_zero] at hv ⊢
  repeat' apply And.intro
  all_goals omega

theorem boundaryVertices_shiftFace (space time : Nat) (p : Z4Plaq) :
    boundaryVertices (shiftFace space time p) = (boundaryVertices p).map (shiftVertex space time) := by
  unfold boundaryVertices
  rw [edgesOf_shiftFace, List.flatMap_map, List.map_flatMap]
  apply congrArg (fun f => (edgesOf p).flatMap f)
  funext link
  simp only [List.map_cons, List.map_nil, shiftLink, shiftVertex_addE]

theorem bulk_boundary_margin {half padding lag : Nat} (hlag : lag ≤ padding)
    {p : Z4Plaq} (hp : p ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    {v : Z4Vertex} (hv : v ∈ boundaryVertices (shiftFace padding (padding-lag) p)) :
    VertexInset (centralExtent (half+padding)) (padding-lag) v := by
  rw [boundaryVertices_shiftFace] at hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  apply shifted_vertex_inset (Nat.sub_le padding lag) (Nat.le_refl _)
    (show centralExtent half+padding+(padding-lag) ≤ centralExtent (half+padding) by unfold centralExtent; omega)
    (show centralExtent half+(padding-lag)+(padding-lag) ≤ centralExtent (half+padding) by unfold centralExtent; omega)
    (boundary_vertex_inset_zero hp hu)

/-- Witness for any requested geometric margin at a fixed lag. -/
def paddingForMargin (lag radius : Nat) : Nat := lag+radius

theorem paddingForMargin_lag (lag radius : Nat) : lag ≤ paddingForMargin lag radius := by
  unfold paddingForMargin
  omega

theorem paddingForMargin_bound {half : Nat} (lag radius : Nat)
    {p : Z4Plaq} (hp : p ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    {v : Z4Vertex} (hv : v ∈ boundaryVertices (shiftFace (paddingForMargin lag radius)
      (paddingForMargin lag radius-lag) p)) :
    VertexInset (centralExtent (half+paddingForMargin lag radius)) radius v := by
  have h := bulk_boundary_margin (paddingForMargin_lag lag radius) hp hv
  simpa only [paddingForMargin, Nat.add_sub_cancel_left] using h

end YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry

#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftVertex
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftLink
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFace
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFace_time
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFace_injective
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFace_comp
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftVertex_addE
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.edgesOf_shiftFace
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFace_mem
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftLink_mem
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFaceId
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFaceId_physical
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFaceId_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFaceId_injective
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFaceId_zero
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFace_lower
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shiftFace_reflection
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.boundaryVertices
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.VertexInset
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.boundary_vertex_inset_zero
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.shifted_vertex_inset
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.boundaryVertices_shiftFace
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.bulk_boundary_margin
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.paddingForMargin
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.paddingForMargin_lag
#print axioms YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry.paddingForMargin_bound
