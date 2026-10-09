/-
# Two distinct boundary links determine a canonical Z4 plaquette

For the nonperiodic coordinate lattice, two distinct links on the boundary
of one canonical unit plaquette identify that plaquette uniquely. Therefore,
two plaquettes with two common boundary links are equal, and distinct
plaquettes share at most one boundary link. This is finite geometry for the
source-specific mixed-link bracket reduction: an exterior face occupies at
most one slot on a given face, so a first possible bracket uses two distinct
other faces. No rate, Hessian, weighted-law, physical-gap, or Clay theorem is
asserted here.
-/

import YMGap.Continuum.ClusterCount4DProgress

namespace YMGap.Continuum.Z4DistinctPlaquetteIntersection

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress

/-- Two distinct actual boundary links determine a canonical nonperiodic
coordinate plaquette. -/
theorem two_boundary_links_determine_face (left right : Z4Plaq) (a b : Z4Link)
    (ha : a ∈ edgesOf left) (hb : b ∈ edgesOf left) (hne : a ≠ b)
    (hra : a ∈ edgesOf right) (hrb : b ∈ edgesOf right) : left = right := by
  rcases left with ⟨⟨x, y, z, t⟩, p⟩
  rcases right with ⟨⟨u, v, w, s⟩, q⟩
  cases p
  all_goals
    simp only [edgesOf, dirsOf, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl
    all_goals rcases hb with rfl | rfl | rfl | rfl
    all_goals try exact False.elim (hne rfl)
    all_goals clear hne
    all_goals cases q
    all_goals
      simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq, reduceCtorEq, and_true, and_false, false_or] at hra hrb ⊢
      repeat' constructor
      all_goals omega

/-- If two links belong to both plaquette boundaries and are distinct, the
plaquettes coincide. -/
theorem common_two_boundary_links_eq (left right : Z4Plaq) (a b : Z4Link)
    (ha : a ∈ edgesOf left) (hb : b ∈ edgesOf left) (hne : a ≠ b)
    (hra : a ∈ edgesOf right) (hrb : b ∈ edgesOf right) : left = right :=
  two_boundary_links_determine_face left right a b ha hb hne hra hrb

/-- Distinct plaquettes cannot share two distinct boundary links; hence any
two common links are equal. -/
theorem common_boundary_links_equal_of_faces_ne (left right : Z4Plaq)
    (hfaces : left ≠ right) (a b : Z4Link)
    (ha : a ∈ edgesOf left) (hb : b ∈ edgesOf left)
    (hra : a ∈ edgesOf right) (hrb : b ∈ edgesOf right) : a = b := by
  by_cases hab : a = b
  · exact hab
  · exact False.elim (hfaces
      (two_boundary_links_determine_face left right a b ha hb hab hra hrb))

end YMGap.Continuum.Z4DistinctPlaquetteIntersection

#print axioms YMGap.Continuum.Z4DistinctPlaquetteIntersection.two_boundary_links_determine_face
#print axioms YMGap.Continuum.Z4DistinctPlaquetteIntersection.common_two_boundary_links_eq
#print axioms YMGap.Continuum.Z4DistinctPlaquetteIntersection.common_boundary_links_equal_of_faces_ne
