/-
# The concrete bounded interference neighborhood of a plaquette boundary

Two labels interfere if their boundaries meet, or if one of the selected
original action faces meets both boundaries. Noninterference excludes EVERY
link of the first boundary from the second boundary and from the second
face's entire selected action star.

The old literal Z4 neighbor enumeration supplies 24 immediate candidates and
24*24 mediated candidates. The resulting list of 600 may overcount, but it
covers every interfering label independently of the slab extent and selected
action size. A duplicate-free row therefore has length at most 600.

This is physical link geometry, not an assumed graph degree. No orthogonality
of the full interacting measure, summed dual norm or spectral gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure

namespace YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryOverlap

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure
open YMGap.Continuum.CayleyPruferInjection (nodup_subset_length_le)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPlaquetteAt)

/-- Decidable interference through the SAME selected action identifiers. -/
def interferes (extent : Nat) (ids : List Nat) (p q : Z4Plaq) : Bool :=
  touches p q || ids.any (fun id =>
    touches p (slabPlaquetteAt extent id) && touches q (slabPlaquetteAt extent id))

def Interferes (extent : Nat) (ids : List Nat) (p q : Z4Plaq) : Prop :=
  interferes extent ids p q = true

instance decidableInterferes (extent : Nat) (ids : List Nat) (p q : Z4Plaq) :
    Decidable (Interferes extent ids p q) :=
  inferInstanceAs (Decidable (interferes extent ids p q = true))

theorem interferes_iff (extent : Nat) (ids : List Nat) (p q : Z4Plaq) :
    Interferes extent ids p q ↔
      touches p q = true ∨ ∃ id, id ∈ ids ∧
        touches p (slabPlaquetteAt extent id) = true ∧
        touches q (slabPlaquetteAt extent id) = true := by
  simp only [Interferes, interferes, Bool.or_eq_true_iff,
    List.any_eq_true, Bool.and_eq_true_iff]

theorem touches_symm {p q : Z4Plaq} (h : touches p q = true) : touches q p = true := by
  obtain ⟨link, hp, hq⟩ := (touches_iff p q).mp h
  exact (touches_iff q p).mpr ⟨link, hq, hp⟩

theorem Interferes.symm {extent : Nat} {ids : List Nat} {p q : Z4Plaq}
    (h : Interferes extent ids p q) : Interferes extent ids q p := by
  rcases (interferes_iff extent ids p q).mp h with htouch | ⟨id, hi, hp, hq⟩
  · exact (interferes_iff extent ids q p).mpr (Or.inl (touches_symm htouch))
  · exact (interferes_iff extent ids q p).mpr (Or.inr ⟨id, hi, hq, hp⟩)

theorem interferes_refl (extent : Nat) (ids : List Nat) (p : Z4Plaq) :
    Interferes extent ids p p :=
  (interferes_iff extent ids p p).mpr (Or.inl
    ((touches_iff p p).mpr ⟨(p.1, (dirsOf p.2).1), List.mem_cons_self, List.mem_cons_self⟩))

theorem noninterference_symm {extent : Nat} {ids : List Nat} {p q : Z4Plaq}
    (h : ¬ Interferes extent ids p q) : ¬ Interferes extent ids q p :=
  fun hq => h (Interferes.symm hq)

theorem noninterference_ne {extent : Nat} {ids : List Nat} {p q : Z4Plaq}
    (h : ¬ Interferes extent ids p q) : p ≠ q := by
  intro he
  subst q
  exact h (interferes_refl extent ids p)

/-- Boundary separation excludes each original link, not merely one witness. -/
theorem noninterference_boundary_misses {extent : Nat} {ids : List Nat} {p q : Z4Plaq}
    (h : ¬ Interferes extent ids p q) (link : Z4Link) (hl : link ∈ edgesOf p) :
    link ∉ edgesOf q := by
  intro hq
  exact h ((interferes_iff extent ids p q).mpr
    (Or.inl ((touches_iff p q).mpr ⟨link, hl, hq⟩)))

/-- Every factor in q's selected action star misses every boundary link of p.
No independence of an already-integrated terminal message is asserted. -/
theorem noninterference_star_misses {extent : Nat} {ids : List Nat} {p q : Z4Plaq}
    (h : ¬ Interferes extent ids p q) (link : Z4Link) (hl : link ∈ edgesOf p) :
    link ∉ faceLinks extent (boundaryStar extent ids q) := by
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  have hstar := boundaryStar_mem hi
  exact h ((interferes_iff extent ids p q).mpr (Or.inr
    ⟨id, hstar.1, (touches_iff p (slabPlaquetteAt extent id)).mpr ⟨link, hl, he⟩,
      (touches_iff q (slabPlaquetteAt extent id)).mpr hstar.2⟩))

/-- The literal support list used by the other boundary's polynomial dual
contains no chosen boundary link under noninterference. -/
theorem noninterference_dualLinks_misses {extent : Nat} {ids : List Nat} {p q : Z4Plaq}
    (h : ¬ Interferes extent ids p q) (link : Z4Link) (hl : link ∈ edgesOf p) :
    link ∉ edgesOf q ++ faceLinks extent (boundaryStar extent ids q) :=
  fun hm => (List.mem_append.mp hm).elim
    (noninterference_boundary_misses h link hl) (noninterference_star_misses h link hl)

private theorem touches_mem_neighbors {p q : Z4Plaq} (h : touches p q = true) :
    q ∈ z4Nbrs p := by
  obtain ⟨link, hp, hq⟩ := (touches_iff p q).mp h
  exact z4_sound p q link (decide_eq_true hp) (decide_eq_true hq)

/-- Overcounting is intentional: 24 immediate plus 24*24 mediated candidates.
The list itself is data and has no dependence on extent or selected volume. -/
def candidates (p : Z4Plaq) : List Z4Plaq :=
  z4Nbrs p ++ (z4Nbrs p).flatMap z4Nbrs

private theorem neighbors_flatMap_length : ∀ ps : List Z4Plaq,
    (ps.flatMap z4Nbrs).length = 24 * ps.length
  | [] => rfl
  | p :: ps => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        z4Nbrs_length, neighbors_flatMap_length ps]
      omega

theorem candidates_length (p : Z4Plaq) : (candidates p).length = 600 := by
  simp only [candidates, List.length_append, neighbors_flatMap_length, z4Nbrs_length]

/-- Covers every original selected-action interferer. Physicality and nodup of
ids are unnecessary here: the universal Z4 enumeration already covers them. -/
theorem candidates_complete {extent : Nat} {ids : List Nat} {p q : Z4Plaq}
    (h : Interferes extent ids p q) : q ∈ candidates p := by
  rcases (interferes_iff extent ids p q).mp h with htouch | ⟨id, _, hp, hq⟩
  · exact List.mem_append.mpr (Or.inl (touches_mem_neighbors htouch))
  · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨slabPlaquetteAt extent id, touches_mem_neighbors hp,
        touches_mem_neighbors (touches_symm hq)⟩))

/-- Any duplicate-free sublist of actual interfering labels has bounded size. -/
theorem nodup_interfering_length_le (extent : Nat) (ids : List Nat) (p : Z4Plaq)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (h : ∀ q, q ∈ qs → Interferes extent ids p q) : qs.length ≤ 600 := by
  have hb := nodup_subset_length_le qs (candidates p) hn
    (fun q hq => candidates_complete (h q hq))
  simpa only [candidates_length] using hb

/-- The actual row selected from any finite label list. Repeated labels are
not discarded by this definition; the cardinal theorem states its nodup guard. -/
def interferenceRow (extent : Nat) (ids : List Nat) (p : Z4Plaq)
    (qs : List Z4Plaq) : List Z4Plaq :=
  qs.filter (fun q => interferes extent ids p q)

theorem interferenceRow_mem {extent : Nat} {ids : List Nat} {p q : Z4Plaq}
    {qs : List Z4Plaq} (h : q ∈ interferenceRow extent ids p qs) :
    q ∈ qs ∧ Interferes extent ids p q :=
  List.mem_filter.mp h

theorem interferenceRow_length_le (extent : Nat) (ids : List Nat) (p : Z4Plaq)
    (qs : List Z4Plaq) (hn : qs.Nodup) :
    (interferenceRow extent ids p qs).length ≤ 600 :=
  nodup_interfering_length_le extent ids p _ (List.filter_sublist.nodup hn)
    (fun _ hq => (interferenceRow_mem hq).2)

#print axioms interferes
#print axioms Interferes
#print axioms decidableInterferes
#print axioms interferes_iff
#print axioms touches_symm
#print axioms Interferes.symm
#print axioms interferes_refl
#print axioms noninterference_symm
#print axioms noninterference_ne
#print axioms noninterference_boundary_misses
#print axioms noninterference_star_misses
#print axioms noninterference_dualLinks_misses
#print axioms candidates
#print axioms candidates_length
#print axioms candidates_complete
#print axioms nodup_interfering_length_le
#print axioms interferenceRow
#print axioms interferenceRow_mem
#print axioms interferenceRow_length_le

end YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryOverlap
