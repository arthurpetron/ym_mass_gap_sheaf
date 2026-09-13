/-
# Rooted cores are unchanged by arbitrary detached spectators

Explicit root paths prove idempotence of the computed core. Conversely,
a path cannot cross a literal disjoint-link split. These two directions
prove that merging a fixed core with any detached ambient selection keeps
exactly that core. The complementary selection is recovered literally,
in ambient order. No analytic or graph-connectedness input is assumed.
-/

import YMGap.Continuum.BF4ExactSlabRootedSelection
import YMGap.Continuum.FiniteSelectionMerge

namespace YMGap.Continuum.BF4ExactSlabRootedSelectionStability

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSelectionMerge
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent

private theorem chain_closed {A : Type} {adj : A → A → Bool} {support : List A}
    (good : A → Prop) (hc : ∀ a b, good a → b ∈ support → adj a b = true → good b) :
    ∀ {a b}, ChainIn adj support a b → good a → good b
  | _, _, .refl _, ha => ha
  | _, _, .step he hb rest, ha => chain_closed good hc rest (hc _ _ ha hb he)

theorem some_mem_vertices {ids : List Nat} {id : Nat} : some id ∈ vertices ids ↔ id ∈ ids := by
  simp only [vertices, List.mem_cons, List.mem_map, Option.some.injEq,
    Option.some_ne_none, false_or, exists_eq_right]

theorem vertices_mono {xs ys : List Nat} (h : ∀ id, id ∈ xs → id ∈ ys) :
    ∀ v, v ∈ vertices xs → v ∈ vertices ys := by
  intro v hv
  cases v with
  | none => exact List.mem_cons_self
  | some id => exact some_mem_vertices.mpr (h id (some_mem_vertices.mp hv))

theorem path_component (extent : Nat) (links : List Z4Link) (anchor ids : List Nat)
    (hsub : ∀ id, id ∈ anchor → id ∈ ids) (id : Nat)
    (path : ChainIn (adjacent extent links) (vertices anchor) none (some id)) :
    some id ∈ component extent links ids :=
  chain_closed (fun v => v ∈ component extent links ids)
    (fun _ _ ha hb he => rootComponent_closed_under_edge (adjacent extent links) (adjacent_sym extent links)
      (show none ∈ vertices ids from List.mem_cons_self) ha (vertices_mono hsub _ hb) he)
    path (root_mem_rootComponent _ (show none ∈ vertices ids from List.mem_cons_self))

theorem core_idempotent (extent : Nat) (links : List Z4Link) (ids : List Nat) :
    core extent links (core extent links ids) = core extent links ids := by
  apply List.filter_eq_self.mpr
  intro id hi
  exact decide_eq_true (path_component extent links _ _ (fun _ h => h) id (core_path extent links ids id hi))

theorem detached_not_anchor {extent : Nat} {links : List Z4Link} {anchor ambient : List Nat} {id : Nat}
    (hi : id ∈ detachedIds extent links anchor ambient) : id ∉ anchor := by
  intro ha
  have hd := (disjointTest_iff _ _).mp (List.mem_filter.mp hi).2
  let edge : Z4Link := ((slabPlaquetteAt extent id).1, (dirsOf (slabPlaquetteAt extent id).2).1)
  have he : edge ∈ edgesOf (slabPlaquetteAt extent id) := List.mem_cons_self
  exact hd edge (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨id, ha, he⟩)))
    (List.mem_flatMap.mpr ⟨id, List.mem_cons_self, he⟩)

theorem nodeLinks_subset {extent : Nat} {links : List Z4Link} {anchor : List Nat} {v : Option Nat}
    (hv : v ∈ vertices anchor) : ∀ link, link ∈ nodeLinks extent links v → link ∈ links++faceLinks extent anchor := by
  intro link hl
  cases v with
  | none => exact List.mem_append.mpr (Or.inl hl)
  | some id =>
      exact List.mem_append.mpr (Or.inr (faceLinks_mono
        (fun j hj => (List.mem_singleton.mp hj) ▸ (some_mem_vertices.mp hv)) link hl))

theorem adjacent_false_of_split {extent : Nat} {links : List Z4Link} {anchor extra : List Nat}
    (hd : LinksDisjoint (links++faceLinks extent anchor) (faceLinks extent extra))
    {v : Option Nat} (hv : v ∈ vertices anchor) {id : Nat} (hi : id ∈ extra) :
    adjacent extent links v (some id) = false := by
  have ht : disjointTest (nodeLinks extent links v) (nodeLinks extent links (some id)) = true :=
    (disjointTest_iff _ _).mpr (fun link hl hr => hd link (nodeLinks_subset hv link hl)
      (faceLinks_mono (fun j hj => (List.mem_singleton.mp hj) ▸ hi) link hr))
  simp only [adjacent, ht, Bool.not_true]

theorem core_subset_of_split {extent : Nat} {links : List Z4Link} {ids anchor extra : List Nat}
    (hcover : ∀ id, id ∈ ids → id ∈ anchor ∨ id ∈ extra)
    (hd : LinksDisjoint (links++faceLinks extent anchor) (faceLinks extent extra)) :
    ∀ id, id ∈ core extent links ids → id ∈ anchor := by
  intro id hi
  have hv : some id ∈ vertices anchor := chain_closed (fun v => v ∈ vertices anchor)
    (fun a b ha hb he => by
      cases b with
      | none => exact List.mem_cons_self
      | some j =>
          have hj := (core_mem_iff.mp (some_mem_vertices.mp hb)).1
          rcases hcover j hj with hj | hj
          · exact some_mem_vertices.mpr hj
          · have hf := adjacent_false_of_split hd ha hj
            rw [he] at hf
            cases hf)
    (core_path extent links ids id hi) List.mem_cons_self
  exact some_mem_vertices.mp hv

theorem core_merge {extent : Nat} {links : List Z4Link} {ambient anchor extra : List Nat}
    (hn : ambient.Nodup) (ha : anchor ∈ selections ambient)
    (hfixed : core extent links anchor = anchor)
    (he : extra ∈ selections (detachedIds extent links anchor ambient)) :
    core extent links (merge ambient anchor extra) = anchor := by
  have hsub : ∀ id, id ∈ anchor → id ∈ merge ambient anchor extra :=
    fun id hi => merge_mem_iff.mpr ⟨selected_mem ha id hi, Or.inl hi⟩
  have hd : LinksDisjoint (links++faceLinks extent anchor) (faceLinks extent extra) :=
    fun link hl hr => detached_disjoint extent links anchor ambient link hl
      (faceLinks_mono (fun id hi => selected_mem he id hi) link hr)
  apply selected_eq_of_mem_iff hn
    (sublist_selected ((selected_sublist (core_selected extent links _)).trans (selected_sublist (merge_selected _ _ _)))) ha
  intro id
  constructor
  · exact core_subset_of_split (fun _ h => (merge_mem_iff.mp h).2) hd id
  · intro hi
    have path := core_path extent links anchor id (hfixed.symm ▸ hi)
    rw [hfixed] at path
    exact core_mem_iff.mpr ⟨hsub id hi, path_component extent links anchor _ hsub id path⟩

theorem spectators_merge {extent : Nat} {links : List Z4Link} {ambient anchor extra : List Nat}
    (hn : ambient.Nodup) (ha : anchor ∈ selections ambient)
    (hfixed : core extent links anchor = anchor)
    (he : extra ∈ selections (detachedIds extent links anchor ambient)) :
    spectators extent links (merge ambient anchor extra) = extra := by
  have hc := core_merge hn ha hfixed he
  apply selected_eq_of_mem_iff hn
    (sublist_selected ((List.filter_sublist (l := merge ambient anchor extra)).trans
      (selected_sublist (merge_selected _ _ _))))
    (sublist_selected ((selected_sublist he).trans List.filter_sublist))
  intro id
  constructor
  · intro hi
    have hs := spectators_mem_iff.mp hi
    rcases (merge_mem_iff.mp hs.1).2 with hm | hm
    · have hm' : id ∈ core extent links (merge ambient anchor extra) := hc.symm ▸ hm
      exact False.elim (hs.2 (core_mem_iff.mp hm').2)
    · exact hm
  · intro hi
    have hd := selected_mem he id hi
    have hm : id ∈ merge ambient anchor extra := merge_mem_iff.mpr ⟨detached_mem hd, Or.inr hi⟩
    apply spectators_mem_iff.mpr
    refine ⟨hm, fun hp => ?_⟩
    have hm' : id ∈ core extent links (merge ambient anchor extra) := core_mem_iff.mpr ⟨hm, hp⟩
    rw [hc] at hm'
    exact detached_not_anchor hd hm'

end YMGap.Continuum.BF4ExactSlabRootedSelectionStability

#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.some_mem_vertices
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.vertices_mono
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.path_component
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.core_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.detached_not_anchor
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.nodeLinks_subset
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.adjacent_false_of_split
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.core_subset_of_split
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.core_merge
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelectionStability.spectators_merge
