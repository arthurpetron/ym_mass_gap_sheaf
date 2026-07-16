/-
# Ordered nesting of the finite four-dimensional box enumeration

Membership monotonicity alone is not enough for transporting the explicit
left-associated link-fusion formula between boxes: that formula sees the
order of the incident plaquettes.  The lexicographic box enumeration is in
fact nested as a `List.Sublist`.  Consequently the incident plaquettes of a
fixed geometric link also form a sublist after enlarging the box.  Later
cross-volume arguments can therefore reduce to insertion of zero-spin faces,
without assuming a general permutation invariance of the fusion tree.
-/

import YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound

namespace YMGap.Continuum.Z4NestedBoxEnumeration

open scoped List
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion

private theorem flatMap_sublist_source {α β : Type} {xs ys : List α}
    (f : α → List β) (h : xs <+ ys) :
    xs.flatMap f <+ ys.flatMap f := by
  induction h with
  | slnil => exact List.Sublist.slnil
  | cons a h ih =>
      simpa only [List.flatMap_cons] using
        List.sublist_append_of_sublist_right (l₁ := f a) ih
  | cons₂ a h ih =>
      simpa only [List.flatMap_cons] using
        (List.Sublist.append (List.Sublist.refl (f a)) ih)

private theorem flatMap_sublist_pointwise {α β : Type} (xs : List α)
    (f g : α → List β) (h : ∀ x, x ∈ xs → f x <+ g x) :
    xs.flatMap f <+ xs.flatMap g := by
  induction xs with
  | nil => exact List.Sublist.slnil
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      exact List.Sublist.append
        (h x (by simp))
        (ih (fun y hy => h y (by simp [hy])))

/-- The lexicographically enumerated vertex list of a smaller box occurs in
the same relative order in every larger box. -/
theorem boxVertices_sublist {small large : Nat} (h : small ≤ large) :
    boxVertices small <+ boxVertices large := by
  have hr : List.range small <+ List.range large :=
    List.range_sublist.mpr h
  have hd (a b c : Nat) :
      (List.range small).map (fun d => (a, b, c, d)) <+
        (List.range large).map (fun d => (a, b, c, d)) :=
    hr.map (fun d => (a, b, c, d))
  have hc (a b : Nat) :
      (List.range small).flatMap (fun c =>
        (List.range small).map (fun d => (a, b, c, d))) <+
      (List.range large).flatMap (fun c =>
        (List.range large).map (fun d => (a, b, c, d))) := by
    have hinner :
        (List.range small).flatMap (fun c =>
          (List.range small).map (fun d => (a, b, c, d))) <+
        (List.range small).flatMap (fun c =>
          (List.range large).map (fun d => (a, b, c, d))) :=
      flatMap_sublist_pointwise (List.range small)
        (fun c => (List.range small).map (fun d => (a, b, c, d)))
        (fun c => (List.range large).map (fun d => (a, b, c, d)))
        (fun c _ => hd a b c)
    exact hinner.trans
      (flatMap_sublist_source
        (fun c => (List.range large).map (fun d => (a, b, c, d))) hr)
  have hb (a : Nat) :
      (List.range small).flatMap (fun b =>
        (List.range small).flatMap (fun c =>
          (List.range small).map (fun d => (a, b, c, d)))) <+
      (List.range large).flatMap (fun b =>
        (List.range large).flatMap (fun c =>
          (List.range large).map (fun d => (a, b, c, d)))) := by
    have hinner :
        (List.range small).flatMap (fun b =>
          (List.range small).flatMap (fun c =>
            (List.range small).map (fun d => (a, b, c, d)))) <+
        (List.range small).flatMap (fun b =>
          (List.range large).flatMap (fun c =>
            (List.range large).map (fun d => (a, b, c, d)))) :=
      flatMap_sublist_pointwise (List.range small)
        (fun b => (List.range small).flatMap (fun c =>
          (List.range small).map (fun d => (a, b, c, d))))
        (fun b => (List.range large).flatMap (fun c =>
          (List.range large).map (fun d => (a, b, c, d))))
        (fun b _ => hc a b)
    exact hinner.trans
      (flatMap_sublist_source
        (fun b => (List.range large).flatMap (fun c =>
          (List.range large).map (fun d => (a, b, c, d)))) hr)
  unfold boxVertices
  have hinner :
      (List.range small).flatMap (fun a =>
        (List.range small).flatMap (fun b =>
          (List.range small).flatMap (fun c =>
            (List.range small).map (fun d => (a, b, c, d))))) <+
      (List.range small).flatMap (fun a =>
        (List.range large).flatMap (fun b =>
          (List.range large).flatMap (fun c =>
            (List.range large).map (fun d => (a, b, c, d))))) :=
    flatMap_sublist_pointwise (List.range small)
      (fun a => (List.range small).flatMap (fun b =>
        (List.range small).flatMap (fun c =>
          (List.range small).map (fun d => (a, b, c, d)))))
      (fun a => (List.range large).flatMap (fun b =>
        (List.range large).flatMap (fun c =>
          (List.range large).map (fun d => (a, b, c, d)))))
      (fun a _ => hb a)
  exact hinner.trans
    (flatMap_sublist_source
      (fun a => (List.range large).flatMap (fun b =>
        (List.range large).flatMap (fun c =>
          (List.range large).map (fun d => (a, b, c, d))))) hr)

/-- Plaquette identifiers inherit the ordered nesting of the vertex lists. -/
theorem boxPlaquettes_sublist {small large : Nat} (h : small ≤ large) :
    boxPlaquettes small <+ boxPlaquettes large := by
  unfold boxPlaquettes
  exact flatMap_sublist_source
    (fun v => z4Planes.map fun P => (v, P)) (boxVertices_sublist h)

/-- For a fixed geometric link, enlarging the box only inserts additional
incident plaquettes; it never reorders the old incident plaquettes. -/
theorem incidentBoxPlaquettes_sublist {small large : Nat}
    (h : small ≤ large) (ell : Z4Link) :
    ((boxPlaquettes small).filter fun p => decide (ell ∈ edgesOf p)) <+
      ((boxPlaquettes large).filter fun p => decide (ell ∈ edgesOf p)) :=
  (boxPlaquettes_sublist h).filter
    (fun p => decide (ell ∈ edgesOf p))

#print axioms boxVertices_sublist
#print axioms boxPlaquettes_sublist
#print axioms incidentBoxPlaquettes_sublist

end YMGap.Continuum.Z4NestedBoxEnumeration
