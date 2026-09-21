/-
# Bounded symmetric geometry of a selected-link Ward star

The literal Ward star consists of the selected link together with every link
on an original physical plaquette incident to it.  Sharing such a plaquette
is symmetric, and the raw list has at most `1 + 6 * 4 = 25` entries.  Hence
every duplicate-free finite link family has at most twenty-five occurrences
in one star row.  This is finite lattice geometry only; it asserts no
orthogonality, decay, or analytic estimate.
-/

import YMGap.Continuum.BF4ExactSlabLinkStarGeometry

namespace YMGap.Continuum.BF4ExactSlabWardStarGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- The selected physical link and all links belonging to one of its actual
incident physical plaquettes.  Repetitions are deliberately retained. -/
def starLinks (extent : Nat) (link : Z4Link) : List Z4Link :=
  link :: faceLinks extent (incidentIds extent link)

/-- Literal star adjacency.  It is reflexive and, by shared-face incidence,
symmetric. -/
def Near (extent : Nat) (link other : Z4Link) : Prop :=
  other ∈ starLinks extent link

instance nearDecidable (extent : Nat) (link other : Z4Link) :
    Decidable (Near extent link other) := inferInstanceAs (Decidable (other ∈ starLinks extent link))

theorem near_refl (extent : Nat) (link : Z4Link) : Near extent link link :=
  List.mem_cons_self

/-- Membership either is the selected link itself or is witnessed by one
common original physical face identifier. -/
theorem near_iff (extent : Nat) (link other : Z4Link) :
    Near extent link other ↔
      other = link ∨ exists id : Nat,
        id ∈ slabPhysicalFaceEdges extent ∧
          link ∈ edgesOf (slabPlaquetteAt extent id) ∧
            other ∈ edgesOf (slabPlaquetteAt extent id) := by
  constructor
  · intro h
    rcases List.mem_cons.mp h with heq | hface
    · exact Or.inl heq
    · obtain ⟨id, hid, hother⟩ := List.mem_flatMap.mp hface
      have hi := (mem_incidentIds_iff extent link id).mp hid
      exact Or.inr ⟨id, hi.1, hi.2, hother⟩
  · intro h
    rcases h with heq | ⟨id, hphysical, hlink, hother⟩
    · exact heq ▸ near_refl extent link
    · apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      exact ⟨id, (mem_incidentIds_iff extent link id).mpr
        ⟨hphysical, hlink⟩, hother⟩

theorem near_symm {extent : Nat} {link other : Z4Link}
    (h : Near extent link other) : Near extent other link := by
  rcases (near_iff extent link other).mp h with heq | ⟨id, hp, hl, ho⟩
  · subst other
    exact near_refl extent link
  · exact (near_iff extent other link).mpr (Or.inr ⟨id, hp, ho, hl⟩)

/-- The raw star list has one selected link and at most six four-link face
boundaries.  Duplicate boundary links only make the useful set smaller. -/
theorem starLinks_length_le_25 (extent : Nat) (link : Z4Link) :
    (starLinks extent link).length ≤ 25 := by
  rw [starLinks, List.length_cons, faceLinks_length]
  have h := incidentIds_length_le_six extent link
  omega

/-- A duplicate-free family contains at most twenty-five occurrences in any
one literal Ward-star row. -/
theorem row_count (extent : Nat) (link : Z4Link) (xs : List Z4Link)
    (hxs : xs.Nodup) :
    (xs.filter (fun other => decide (Near extent link other))).length ≤ 25 := by
  let row := xs.filter (fun other => decide (Near extent link other))
  have hrowNodup : row.Nodup := List.filter_sublist.nodup hxs
  have hrowSubset : ∀ other, other ∈ row → other ∈ starLinks extent link := by
    intro other hother
    have hnear := (List.mem_filter.mp hother).2
    exact of_decide_eq_true hnear
  have hlength := nodup_subset_length_le row (starLinks extent link)
    hrowNodup hrowSubset
  exact Nat.le_trans hlength (starLinks_length_le_25 extent link)

/-- The same row bound for an injectively labelled duplicate-free index
family.  This form lets consumers retain subtype membership or other data in
their score index without introducing a fallback physical link. -/
theorem row_count_injective {Index : Type} (extent : Nat) (link : Z4Link)
    (label : Index -> Z4Link)
    (hlabel : ∀ a b, label a = label b -> a = b)
    (xs : List Index) (hxs : xs.Nodup) :
    (xs.filter (fun other => decide (Near extent link (label other)))).length ≤ 25 := by
  let row := xs.filter (fun other => decide (Near extent link (label other)))
  have hrowNodup : row.Nodup := List.filter_sublist.nodup hxs
  have hmappedNodup : (row.map label).Nodup :=
    nodup_map_of_injOn label row hrowNodup
      (fun a _ b _ heq => hlabel a b heq)
  have hmappedSubset : ∀ other, other ∈ row.map label ->
      other ∈ starLinks extent link := by
    intro other hother
    obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hother
    exact of_decide_eq_true (List.mem_filter.mp hindex).2
  have hlength := nodup_subset_length_le (row.map label)
    (starLinks extent link) hmappedNodup hmappedSubset
  rw [List.length_map] at hlength
  exact Nat.le_trans hlength (starLinks_length_le_25 extent link)

end YMGap.Continuum.BF4ExactSlabWardStarGeometry

#print axioms YMGap.Continuum.BF4ExactSlabWardStarGeometry.starLinks
#print axioms YMGap.Continuum.BF4ExactSlabWardStarGeometry.Near
#print axioms YMGap.Continuum.BF4ExactSlabWardStarGeometry.near_refl
#print axioms YMGap.Continuum.BF4ExactSlabWardStarGeometry.near_iff
#print axioms YMGap.Continuum.BF4ExactSlabWardStarGeometry.near_symm
#print axioms YMGap.Continuum.BF4ExactSlabWardStarGeometry.starLinks_length_le_25
#print axioms YMGap.Continuum.BF4ExactSlabWardStarGeometry.row_count
#print axioms YMGap.Continuum.BF4ExactSlabWardStarGeometry.row_count_injective
