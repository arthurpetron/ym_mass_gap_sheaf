/-
# A unique spatial-face incidence at every incident fringe link

The original temporal faces transmit exactly the spatial links with all
three base coordinates strictly below width. Spatial plaquettes have those
same strict base bounds, but their far edges can reach the inclusive fringe.
Any such inactive incident link belongs to exactly one retained spatial
face. This includes every spatial orientation and positive-boundary corner.

A finite search of the four literal boundary edges constructs a free link
for each face which is not fully active. The consumer peels the original
face heat factor using all-spin Haar cancellation. No integral, reduced
action identity, positivity, or spectral estimate is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (faceLinkA)
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors (spatial_face_edge)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (SliceLink face_edge_box)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces temporalFaces spatialFaces_mem_iff temporalFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_mem_iff)

/-- The original inclusive slice predicate with strictly interior base
coordinates. The link may point outwards from its interior base. -/
def StrictSliceLink (width : Nat) (link : Z4Link) : Prop :=
  SliceLink width 0 link ∧ link.1.1 < width ∧ link.1.2.1 < width ∧ link.1.2.2.1 < width

instance (width : Nat) (link : Z4Link) : Decidable (StrictSliceLink width link) := by
  unfold StrictSliceLink SliceLink
  infer_instance

private theorem temporal_lower_strict {width : Nat} {face : Z4Plaq}
    (hf : face ∈ temporalFaces width) : StrictSliceLink width (faceLinkA face) := by
  obtain ⟨hx, hy, hz, ht, hd⟩ := (temporalFaces_mem_iff width face).mp hf
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;> simp only [dirsOf] at hd <;> try cases hd
  all_goals dsimp only at hx hy hz ht
  all_goals simp only [StrictSliceLink, SliceLink, faceLinkA, dirsOf]
  all_goals exact ⟨⟨(by decide), Nat.le_of_lt hx, Nat.le_of_lt hy, Nat.le_of_lt hz, ht⟩,
    hx, hy, hz⟩

/-- Active kinetic indices are exactly the strictly interior spatial bases,
on the original retained link carrier. -/
theorem active_index_iff (width : Nat) (link : Z4Link) (hl : link ∈ baseLinks width) :
    (baseLinks width).idxOf link ∈ activeBlocks width ↔ StrictSliceLink width link := by
  constructor
  · intro hi
    obtain ⟨face, hf, he⟩ := List.mem_map.mp hi
    have hs := temporal_lower_strict hf
    have hm : faceLinkA face ∈ baseLinks width := (baseLinks_mem_iff width _).mpr hs.1
    have hlink := idxOf_injective_on_members hm hl he
    exact hlink ▸ hs
  · intro hs
    rcases link with ⟨⟨x, y, z, t⟩, dir⟩
    obtain ⟨⟨hd, _, _, _, ht⟩, hx, hy, hz⟩ := hs
    change (baseLinks width).idxOf ((x, y, z, t), dir) ∈
      (temporalFaces width).map (fun face => (baseLinks width).idxOf (faceLinkA face))
    cases dir with
    | x0 =>
        exact List.mem_map.mpr ⟨((x,y,z,t), .p03),
          (temporalFaces_mem_iff width _).mpr ⟨hx,hy,hz,ht,rfl⟩, rfl⟩
    | x1 =>
        exact List.mem_map.mpr ⟨((x,y,z,t), .p13),
          (temporalFaces_mem_iff width _).mpr ⟨hx,hy,hz,ht,rfl⟩, rfl⟩
    | x2 =>
        exact List.mem_map.mpr ⟨((x,y,z,t), .p23),
          (temporalFaces_mem_iff width _).mpr ⟨hx,hy,hz,ht,rfl⟩, rfl⟩
    | x3 => exact False.elim (hd rfl)

/-- Fully active means every literal edge is transmitted, not merely the
two edges at the plaquette base. This predicate has a public decision. -/
def FullyActive (width : Nat) (face : Z4Plaq) : Prop :=
  ∀ link, link ∈ edgesOf face → (baseLinks width).idxOf link ∈ activeBlocks width

instance (width : Nat) (face : Z4Plaq) : Decidable (FullyActive width face) := by
  unfold FullyActive
  infer_instance

/-- Every edge of the retained spatial face is in the same original slice. -/
theorem spatial_face_link_mem {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) {link : Z4Link} (hl : link ∈ edgesOf face) :
    link ∈ baseLinks width := by
  obtain ⟨hx, hy, hz, ht, hd⟩ := (spatialFaces_mem_iff width face).mp hf
  have hb := face_edge_box hx hy hz hl
  have he := spatial_face_edge face hd link hl
  exact (baseLinks_mem_iff width link).mpr ⟨he.1, hb.1, hb.2.1, hb.2.2, he.2.trans ht⟩

set_option maxHeartbeats 800000 in
private theorem boundary_incident_unique {width : Nat} {p q : Z4Plaq} {link : Z4Link}
    (hp : p ∈ spatialFaces width) (hl : link ∈ edgesOf p)
    (hn : ¬ (link.1.1 < width ∧ link.1.2.1 < width ∧ link.1.2.2.1 < width))
    (hq : q ∈ spatialFaces width) (hlq : link ∈ edgesOf q) : q = p := by
  have hboundary : width ≤ link.1.1 ∨ width ≤ link.1.2.1 ∨ width ≤ link.1.2.2.1 := by
    by_cases hx : link.1.1 < width
    · by_cases hy : link.1.2.1 < width
      · exact Or.inr (Or.inr (Nat.le_of_not_gt (fun hz => hn ⟨hx,hy,hz⟩)))
      · exact Or.inr (Or.inl (Nat.le_of_not_gt hy))
    · exact Or.inl (Nat.le_of_not_gt hx)
  clear hn
  obtain ⟨hx, hy, hz, ht, hd⟩ := (spatialFaces_mem_iff width p).mp hp
  obtain ⟨hu, hv, hw, hs, hdq⟩ := (spatialFaces_mem_iff width q).mp hq
  rcases p with ⟨⟨x,y,z,t⟩, plane⟩
  rcases q with ⟨⟨u,v,w,s⟩, qplane⟩
  cases plane <;> simp only [dirsOf] at hd <;> try exact False.elim (hd rfl)
  all_goals simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals rcases hl with rfl | rfl | rfl | rfl
  all_goals dsimp only at hx hy hz ht hu hv hw hs hboundary
  all_goals try omega
  all_goals cases qplane <;> simp only [dirsOf] at hdq <;> try exact False.elim (hdq rfl)
  all_goals simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq, reduceCtorEq, and_false,
    and_true, false_or] at hlq
  all_goals simp only [Prod.mk.injEq, reduceCtorEq, and_true, and_false]
  all_goals repeat' apply And.intro
  all_goals omega

/-- Any inactive incident link is free in the complete retained spatial
face list, not just in a selected sublist or one orientation. -/
theorem inactive_incident_unique {width : Nat} {p q : Z4Plaq} {link : Z4Link}
    (hp : p ∈ spatialFaces width) (hl : link ∈ edgesOf p)
    (hinactive : (baseLinks width).idxOf link ∉ activeBlocks width)
    (hq : q ∈ spatialFaces width) (hlq : link ∈ edgesOf q) : q = p := by
  have hm := spatial_face_link_mem hp hl
  apply boundary_incident_unique hp hl _ hq hlq
  intro hc
  exact hinactive ((active_index_iff width link hm).mpr
    ⟨(baseLinks_mem_iff width link).mp hm, hc⟩)

/-- The selected free link is explicit Type-level data. -/
structure FringeFaceLeaf (width : Nat) (face : Z4Plaq) : Type where
  link : Z4Link
  on_face : link ∈ edgesOf face
  in_carrier : link ∈ baseLinks width
  inactive : (baseLinks width).idxOf link ∉ activeBlocks width
  fringe : (baseLinks width).idxOf link ∈ fringeBlocks width
  unique : ∀ q, q ∈ spatialFaces width → link ∈ edgesOf q → q = face

private def selectInactive (width : Nat) :
    (links : List Z4Link) →
    (¬ (∀ link, link ∈ links → (baseLinks width).idxOf link ∈ activeBlocks width)) →
    Σ' link : Z4Link, link ∈ links ∧ (baseLinks width).idxOf link ∉ activeBlocks width
  | [], h => False.elim (h (fun _ hm => False.elim (List.not_mem_nil hm)))
  | link::links, h =>
      if hi : (baseLinks width).idxOf link ∈ activeBlocks width then
        let rest := selectInactive width links (fun hall => h (fun other hm => by
          rcases List.mem_cons.mp hm with he | hm
          · cases he
            exact hi
          · exact hall other hm))
        ⟨rest.1, List.mem_cons_of_mem link rest.2.1, rest.2.2⟩
      else ⟨link, List.mem_cons_self, hi⟩

/-- Search the four literal edges constructively. Non-full activity
returns its free-link witness without eliminating a Prop existential. -/
def fringeFaceLeaf (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (h : ¬ FullyActive width face) : FringeFaceLeaf width face :=
  let selected := selectInactive width (edgesOf face) h
  let hm := spatial_face_link_mem hf selected.2.1
  { link := selected.1
    on_face := selected.2.1
    in_carrier := hm
    inactive := selected.2.2
    fringe := (fringeBlocks_mem_iff width _).mpr ⟨List.idxOf_lt_length_of_mem hm, selected.2.2⟩
    unique := fun _ hq hlq => inactive_incident_unique hf selected.2.1 selected.2.2 hq hlq }

#print axioms StrictSliceLink
#print axioms active_index_iff
#print axioms FullyActive
#print axioms spatial_face_link_mem
#print axioms inactive_incident_unique
#print axioms fringeFaceLeaf

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
