/-
# Constructive separation from an off-center ORIGINAL slab exterior

Coordinate subtraction computes every source preimage in an interior box.
A protected root is therefore separated from every exterior face by its
given margin. Growing the smaller slab around a fixed base face supplies
this margin for every allowed outer time offset, without any offset loss.
The existing actual-core path theorem then gives the required size floor.
-/

import YMGap.Continuum.BF4ExactSlabOffsetAction
import YMGap.Continuum.BF4ExactSlabCoreDistanceFloor

namespace YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabOffsetAction
open YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation (physical_base_coordinate_le)
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor (active_core_linf_floor)
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

def coordinateOffset (P : Placement) : Dir4 → Nat
  | .x0 | .x1 | .x2 => P.padding
  | .x3 => P.time

def BaseBox (P : Placement) (p : Z4Plaq) : Prop :=
  ∀ m, coordinateOffset P m ≤ cPlaq p m ∧ cPlaq p m < coordinateOffset P m+P.source

def unshiftFace (P : Placement) (p : Z4Plaq) : Z4Plaq :=
  ((p.1.1-P.padding, p.1.2.1-P.padding, p.1.2.2.1-P.padding, p.1.2.2.2-P.time), p.2)

theorem unshiftFace_physical {P : Placement} {p : Z4Plaq} (hp : BaseBox P p) :
    unshiftFace P p ∈ boundaryCompleteSlabPlaquettes P.source := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  have h0 := hp x0; have h1 := hp x1; have h2 := hp x2; have h3 := hp x3
  simp only [coordinateOffset, cPlaq, vComp] at h0 h1 h2 h3
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  constructor
  · rw [mem_boxPlaquettes]
    change a-P.padding < P.source+1 ∧ b-P.padding < P.source+1 ∧
      c-P.padding < P.source+1 ∧ d-P.time < P.source+1
    exact ⟨by omega, by omega, by omega, by omega⟩
  · cases plane <;> simp only [unshiftFace, plaquetteTimeAdmissible] <;> omega

theorem shift_unshiftFace {P : Placement} {p : Z4Plaq} (hp : BaseBox P p) :
    shiftFace P.padding P.time (unshiftFace P p) = p := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  have h0 := (hp x0).1; have h1 := (hp x1).1; have h2 := (hp x2).1; have h3 := (hp x3).1
  change P.padding ≤ a at h0; change P.padding ≤ b at h1
  change P.padding ≤ c at h2; change P.time ≤ d at h3
  simp only [unshiftFace, shiftFace, shiftVertex, Nat.sub_add_cancel h0,
    Nat.sub_add_cancel h1, Nat.sub_add_cancel h2, Nat.sub_add_cancel h3]

def embeddedFacePreimage (P : Placement) (p : Z4Plaq) (hp : BaseBox P p) :
    Σ' id : Nat, (id ∈ slabPhysicalFaceEdges P.source) ×'
      (shiftFace P.padding P.time (slabPlaquetteAt P.source id) = p) := by
  let source := unshiftFace P p
  let id := listIndexOf source (boundaryCompleteSlabPlaquettes P.source)
  have hm : source ∈ boundaryCompleteSlabPlaquettes P.source := unshiftFace_physical hp
  have hi : id ∈ slabPhysicalFaceEdges P.source := List.mem_range.mpr (listIndexOf_lt_of_mem _ _ hm)
  refine ⟨id, hi, ?_⟩
  have he : slabPlaquetteAt P.source id = source := getD_listIndexOf_of_mem _ _ _ hm
  rw [he]
  exact shift_unshiftFace hp

theorem baseBox_id_embedded {P : Placement} {id : Nat} (hi : id ∈ slabPhysicalFaceEdges P.target)
    (hp : BaseBox P (slabPlaquetteAt P.target id)) : id ∈ embeddedIds P := by
  obtain ⟨source, hs, he⟩ := embeddedFacePreimage P _ hp
  apply List.mem_map.mpr
  refine ⟨source, hs, ?_⟩
  apply slabPlaquetteAt_injective_on_physical (P.faceId_physical hs) hi
  rw [P.faceId_pin hs]
  exact he

def ProtectedRoot (P : Placement) (margin : Nat) (root : Z4Plaq) : Prop :=
  ∀ m, coordinateOffset P m+margin ≤ cPlaq root m ∧
    cPlaq root m+margin ≤ coordinateOffset P m+P.source

theorem near_protected_baseBox {P : Placement} {margin : Nat} {root p : Z4Plaq}
    (hr : ProtectedRoot P margin root) (hd : linfDist root p < margin) : BaseBox P p := by
  intro m
  have hroot := hr m
  have hdist := le_linfDist_comp root p m
  simp only [natDist] at hdist
  constructor <;> omega

theorem exterior_linf_floor {P : Placement} {margin : Nat} {root : Z4Plaq}
    (hr : ProtectedRoot P margin root) {id : Nat} (hi : id ∈ exteriorIds P) :
    margin ≤ linfDist root (slabPlaquetteAt P.target id) := by
  by_cases hd : margin ≤ linfDist root (slabPlaquetteAt P.target id)
  · exact hd
  · have hin := baseBox_id_embedded (List.mem_filter.mp hi).1 (near_protected_baseBox hr (Nat.lt_of_not_ge hd))
    have hout : id ∉ embeddedIds P := by
      simpa only [keep, Bool.not_eq_true', decide_eq_false_iff_not] using (List.mem_filter.mp hi).2
    exact False.elim (hout hin)

theorem cPlaq_offset (P : Placement) (p : Z4Plaq) (m : Dir4) :
    cPlaq (shiftFace P.padding P.time p) m = cPlaq p m+coordinateOffset P m := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  cases m <;> rfl

theorem shifted_base_protected (P : Placement) {base : Nat} (margin : Nat)
    (hhalf : P.half=base+margin) {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) :
    ProtectedRoot P margin (shiftFace P.padding P.time (shiftFace margin margin p)) := by
  intro m
  rw [cPlaq_offset, BF4ExactSlabEmbeddedExteriorSeparation.cPlaq_uniform_shift]
  have h := physical_base_coordinate_le hp m
  unfold Placement.source
  rw [hhalf]
  unfold centralExtent at h ⊢
  constructor <;> omega

theorem protected_core_size_floor (P : Placement) {margin : Nat} {links : List Z4Link}
    (probe : ProbeCarrier links) (hr : ProtectedRoot P margin probe.animal.root) {anchor : List Nat}
    (ha : anchor ∈ activeAnchors P.target links (keep P) (slabPhysicalFaceEdges P.target)) :
    margin+1-probe.animal.support.length ≤ anchor.length := by
  have h := active_core_linf_floor probe (CayleyParentInj.range_nodup _) (fun _ hi => hi) ha (by
    intro id hi ho
    apply exterior_linf_floor hr
    refine List.mem_filter.mpr ⟨hi, ?_⟩
    change Bool.not (keep P id) = true
    rw [ho]
    rfl)
  omega

end YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation

#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.coordinateOffset
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.BaseBox
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.unshiftFace
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.unshiftFace_physical
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.shift_unshiftFace
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.embeddedFacePreimage
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.baseBox_id_embedded
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.ProtectedRoot
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.near_protected_baseBox
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.exterior_linf_floor
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.cPlaq_offset
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.shifted_base_protected
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation.protected_core_size_floor
