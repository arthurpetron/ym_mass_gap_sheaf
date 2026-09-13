/-
# Canonical rooted selection on the ORIGINAL literal face-link graph

The extra vertex `none` carries the common probe support; `some id` carries
the four literal links of that plaquette. Adjacency means shared links.
The existing constructive graph compiler supplies the root component and
Type-valued paths. Filtering the INPUT order produces its canonical face
list and its spectator complement. Their disjointness and the exact pin to
the previously computed detached region are proved, not assumed.

This root joins both probe supports. It does not by itself prove a path
between the two probes or a geometric separation/counting bound.
-/

import YMGap.Continuum.FiniteBoolGraphRootComponent
import YMGap.Continuum.FiniteSelectionOrder
import YMGap.Continuum.BF4ExactSlabDetachedFaceRegion

namespace YMGap.Continuum.BF4ExactSlabRootedSelection

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent

def nodeLinks (extent : Nat) (links : List Z4Link) : Option Nat → List Z4Link
  | none => links
  | some id => faceLinks extent [id]

def adjacent (extent : Nat) (links : List Z4Link) (a b : Option Nat) : Bool :=
  !(disjointTest (nodeLinks extent links a) (nodeLinks extent links b))

theorem adjacent_sym (extent : Nat) (links : List Z4Link) : SymmetricAdj (adjacent extent links) := by
  intro a b
  apply congrArg Bool.not
  apply Bool.eq_iff_iff.mpr
  rw [disjointTest_iff, disjointTest_iff]
  exact ⟨fun h link hr hl => h link hl hr, fun h link hl hr => h link hr hl⟩

def vertices (ids : List Nat) : List (Option Nat) := none :: ids.map some

def component (extent : Nat) (links : List Z4Link) (ids : List Nat) : List (Option Nat) :=
  rootComponent (adjacent extent links) (vertices ids) none

def coreTest (extent : Nat) (links : List Z4Link) (ids : List Nat) (id : Nat) : Bool :=
  decide (some id ∈ component extent links ids)

def core (extent : Nat) (links : List Z4Link) (ids : List Nat) : List Nat :=
  ids.filter (coreTest extent links ids)

def spectators (extent : Nat) (links : List Z4Link) (ids : List Nat) : List Nat :=
  ids.filter (fun id => !(coreTest extent links ids id))

theorem core_mem_iff {extent : Nat} {links : List Z4Link} {ids : List Nat} {id : Nat} :
    id ∈ core extent links ids ↔ id ∈ ids ∧ some id ∈ component extent links ids := by
  simp only [core, List.mem_filter, coreTest, decide_eq_true_eq]

theorem spectators_mem_iff {extent : Nat} {links : List Z4Link} {ids : List Nat} {id : Nat} :
    id ∈ spectators extent links ids ↔ id ∈ ids ∧ some id ∉ component extent links ids := by
  simp only [spectators, List.mem_filter, coreTest, Bool.not_eq_true', decide_eq_false_iff_not]

theorem core_selected (extent : Nat) (links : List Z4Link) (ids : List Nat) :
    core extent links ids ∈ selections ids := filter_selected _ _

theorem split_perm (extent : Nat) (links : List Z4Link) (ids : List Nat) :
    (core extent links ids ++ spectators extent links ids).Perm ids := List.filter_append_perm _ _

/-- Every retained face has an explicit root path staying in the retained core. -/
def core_path (extent : Nat) (links : List Z4Link) (ids : List Nat) (id : Nat)
    (hi : id ∈ core extent links ids) :
    ChainIn (adjacent extent links) (vertices (core extent links ids)) none (some id) := by
  have hr : none ∈ vertices ids := List.mem_cons_self
  have path := rootComponent_connected (adjacent extent links) (adjacent_sym extent links) hr
    none (some id) (root_mem_rootComponent _ hr) (core_mem_iff.mp hi).2
  apply ChainIn.mono (small := component extent links ids) _ path
  intro point hp
  cases point with
  | none => exact List.mem_cons_self
  | some j =>
      have hv := rootComponent_subset (adjacent extent links) hr hp
      have hj : j ∈ ids := by simpa only [vertices, List.mem_cons, List.mem_map, Option.some.injEq,
        Option.some_ne_none, false_or, exists_eq_right] using hv
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, core_mem_iff.mpr ⟨hj, hp⟩, rfl⟩)

theorem component_spectator_disjoint (extent : Nat) (links : List Z4Link) (ids : List Nat)
    (source : Option Nat) (hs : source ∈ component extent links ids)
    (id : Nat) (hi : id ∈ spectators extent links ids) :
    LinksDisjoint (nodeLinks extent links source) (faceLinks extent [id]) := by
  have hedge := rootComponent_adj_false_of_not_mem (adjacent extent links) (adjacent_sym extent links)
    (show none ∈ vertices ids from List.mem_cons_self) hs
    (show some id ∈ vertices ids from List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨id, (spectators_mem_iff.mp hi).1, rfl⟩))
    (spectators_mem_iff.mp hi).2
  apply (disjointTest_iff _ _).mp
  simpa only [adjacent, nodeLinks, Bool.not_eq_false'] using hedge

theorem split_disjoint (extent : Nat) (links : List Z4Link) (ids : List Nat) :
    LinksDisjoint (links ++ faceLinks extent (core extent links ids))
      (faceLinks extent (spectators extent links ids)) := by
  intro link hl hr
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hr
  have he' : link ∈ faceLinks extent [id] := List.mem_flatMap.mpr ⟨id, List.mem_cons_self, he⟩
  rcases List.mem_append.mp hl with hl | hl
  · exact component_spectator_disjoint extent links ids none
      (root_mem_rootComponent _ (show none ∈ vertices ids from List.mem_cons_self)) id hi link hl he'
  · obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp hl
    exact component_spectator_disjoint extent links ids (some j) (core_mem_iff.mp hj).2 id hi link
      (List.mem_flatMap.mpr ⟨j, List.mem_cons_self, he⟩) he'

/-- The complement is literally the existing detached-region filter, in input order. -/
theorem spectators_eq_detached (extent : Nat) (links : List Z4Link) (ids : List Nat) :
    spectators extent links ids = detachedIds extent links (core extent links ids) ids := by
  apply List.filter_congr
  intro id hi
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro ht
    have hs : id ∈ spectators extent links ids := List.mem_filter.mpr ⟨hi, ht⟩
    apply (disjointTest_iff _ _).mpr
    intro link hl hr
    apply split_disjoint extent links ids link hl
    exact faceLinks_mono (fun j hj => (List.mem_singleton.mp hj) ▸ hs) link hr
  · intro ht
    have hd := (disjointTest_iff _ _).mp ht
    have hn : some id ∉ component extent links ids := by
      intro hc
      have hm : id ∈ core extent links ids := core_mem_iff.mpr ⟨hi, hc⟩
      let edge : Z4Link := ((slabPlaquetteAt extent id).1, (dirsOf (slabPlaquetteAt extent id).2).1)
      have he : edge ∈ edgesOf (slabPlaquetteAt extent id) := List.mem_cons_self
      exact hd edge (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨id, hm, he⟩)))
        (List.mem_flatMap.mpr ⟨id, List.mem_cons_self, he⟩)
    simp only [coreTest, decide_eq_false hn, Bool.not_false]

end YMGap.Continuum.BF4ExactSlabRootedSelection

#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.nodeLinks
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.adjacent
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.adjacent_sym
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.vertices
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.component
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.coreTest
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.core
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.spectators
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.core_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.spectators_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.core_selected
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.split_perm
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.core_path
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.component_spectator_disjoint
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.split_disjoint
#print axioms YMGap.Continuum.BF4ExactSlabRootedSelection.spectators_eq_detached
