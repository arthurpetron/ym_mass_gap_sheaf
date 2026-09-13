/-
# Separation from the ORIGINAL embedded smaller-slab exterior

The smaller slab grows around a fixed local base face by `margin`; a further
`padding` embeds it into the comparison slab. Every original exterior face
is at L-infinity distance at least `margin` from the shifted local face.
The estimate is uniform in the OUTER padding, not decay in that padding at
fixed smaller slab. The embedded face preimage is computed by coordinate
subtraction and finite indexing, with an exact physical face-ID pin.
-/

import YMGap.Continuum.BF4ExactSlabBulkActionDressing
import YMGap.Continuum.SepLatticeZ4Linf

namespace YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

/-- A half-open base-coordinate box contained in the actual embedded slab. -/
def BaseBox (half padding : Nat) (p : Z4Plaq) : Prop :=
  ∀ m, padding ≤ cPlaq p m ∧ cPlaq p m < padding+centralExtent half

def unshiftFace (padding : Nat) (p : Z4Plaq) : Z4Plaq :=
  ((p.1.1-padding, p.1.2.1-padding, p.1.2.2.1-padding, p.1.2.2.2-padding), p.2)

theorem unshiftFace_physical {half padding : Nat} {p : Z4Plaq} (hp : BaseBox half padding p) :
    unshiftFace padding p ∈ boundaryCompleteSlabPlaquettes (centralExtent half) := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  have h0 := hp x0; have h1 := hp x1; have h2 := hp x2; have h3 := hp x3
  simp only [cPlaq, vComp] at h0 h1 h2 h3
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  constructor
  · rw [mem_boxPlaquettes]
    change a-padding < centralExtent half+1 ∧ b-padding < centralExtent half+1 ∧
      c-padding < centralExtent half+1 ∧ d-padding < centralExtent half+1
    exact ⟨by omega, by omega, by omega, by omega⟩
  · cases plane <;> simp only [unshiftFace, plaquetteTimeAdmissible] <;> omega

theorem shift_unshiftFace {half padding : Nat} {p : Z4Plaq} (hp : BaseBox half padding p) :
    shiftFace padding padding (unshiftFace padding p) = p := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  have h0 := (hp x0).1; have h1 := (hp x1).1; have h2 := (hp x2).1; have h3 := (hp x3).1
  change padding ≤ a at h0; change padding ≤ b at h1; change padding ≤ c at h2; change padding ≤ d at h3
  simp only [unshiftFace, shiftFace, shiftVertex, Nat.sub_add_cancel h0, Nat.sub_add_cancel h1,
    Nat.sub_add_cancel h2, Nat.sub_add_cancel h3]

/-- Compute a physical source identifier and its exact translated face. -/
def embeddedFacePreimage (half padding : Nat) (p : Z4Plaq) (hp : BaseBox half padding p) :
    Σ' id : Nat, (id ∈ slabPhysicalFaceEdges (centralExtent half)) ×'
      (shiftFace padding padding (slabPlaquetteAt (centralExtent half) id) = p) := by
  let source := unshiftFace padding p
  let id := listIndexOf source (boundaryCompleteSlabPlaquettes (centralExtent half))
  have hm : source ∈ boundaryCompleteSlabPlaquettes (centralExtent half) := unshiftFace_physical hp
  have hi : id ∈ slabPhysicalFaceEdges (centralExtent half) := List.mem_range.mpr (listIndexOf_lt_of_mem _ _ hm)
  refine ⟨id, hi, ?_⟩
  have he : slabPlaquetteAt (centralExtent half) id = source := getD_listIndexOf_of_mem _ _ _ hm
  rw [he]
  exact shift_unshiftFace hp

theorem baseBox_id_embedded {half padding id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges (centralExtent (half+padding)))
    (hp : BaseBox half padding (slabPlaquetteAt (centralExtent (half+padding)) id)) :
    id ∈ embeddedIds half padding := by
  obtain ⟨source, hs, he⟩ := embeddedFacePreimage half padding _ hp
  apply List.mem_map.mpr
  refine ⟨source, hs, ?_⟩
  apply slabPlaquetteAt_injective_on_physical (bulkFaceId_physical hs) hi
  rw [bulkFaceId_pin hs]
  exact he

/-- Coordinate clearance from the boundary of the EMBEDDED smaller slab. -/
def ProtectedRoot (half padding margin : Nat) (root : Z4Plaq) : Prop :=
  ∀ m, padding+margin ≤ cPlaq root m ∧ cPlaq root m+margin ≤ padding+centralExtent half

theorem near_protected_baseBox {half padding margin : Nat} {root p : Z4Plaq}
    (hr : ProtectedRoot half padding margin root) (hd : linfDist root p < margin) :
    BaseBox half padding p := by
  intro m
  have hroot := hr m
  have hdist := le_linfDist_comp root p m
  simp only [natDist] at hdist
  constructor <;> omega

theorem exterior_linf_floor {half padding margin : Nat} {root : Z4Plaq}
    (hr : ProtectedRoot half padding margin root) {id : Nat} (hi : id ∈ exteriorIds half padding) :
    margin ≤ linfDist root (slabPlaquetteAt (centralExtent (half+padding)) id) := by
  by_cases hd : margin ≤ linfDist root (slabPlaquetteAt (centralExtent (half+padding)) id)
  · exact hd
  · have hin := baseBox_id_embedded (List.mem_filter.mp hi).1
      (near_protected_baseBox hr (Nat.lt_of_not_ge hd))
    have hout : id ∉ embeddedIds half padding := by
      simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using (List.mem_filter.mp hi).2
    exact False.elim (hout hin)

theorem cPlaq_uniform_shift (padding : Nat) (p : Z4Plaq) (m : Dir4) :
    cPlaq (shiftFace padding padding p) m = cPlaq p m+padding := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  cases m <;> rfl

theorem physical_base_coordinate_le {extent : Nat} {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent) (m : Dir4) : cPlaq p m ≤ extent := by
  have hb := (mem_boundaryCompleteSlabPlaquettes _ _).mp hp |>.1
  rw [mem_boxPlaquettes] at hb
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  change a < extent+1 ∧ b < extent+1 ∧ c < extent+1 ∧ d < extent+1 at hb
  cases m <;> simp only [cPlaq, vComp] <;> omega

theorem shifted_base_protected {base : Nat} {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (margin padding : Nat) :
    ProtectedRoot (base+margin) padding margin (shiftFace (margin+padding) (margin+padding) p) := by
  intro m
  rw [cPlaq_uniform_shift]
  have h := physical_base_coordinate_le hp m
  unfold centralExtent at h ⊢
  constructor <;> omega

/-- Increasing the INNER slab around a fixed base face gives separation,
uniformly in the further OUTER padding. -/
theorem shifted_base_exterior_linf_floor {base : Nat} {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (margin padding : Nat)
    {id : Nat} (hi : id ∈ exteriorIds (base+margin) padding) :
    margin ≤ linfDist (shiftFace (margin+padding) (margin+padding) p)
      (slabPlaquetteAt (centralExtent ((base+margin)+padding)) id) :=
  exterior_linf_floor (shifted_base_protected hp margin padding) hi

end YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation

#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.BaseBox
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.unshiftFace
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.unshiftFace_physical
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.shift_unshiftFace
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.embeddedFacePreimage
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.baseBox_id_embedded
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.ProtectedRoot
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.near_protected_baseBox
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.exterior_linf_floor
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.cPlaq_uniform_shift
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.physical_base_coordinate_le
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.shifted_base_protected
#print axioms YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation.shifted_base_exterior_linf_floor
