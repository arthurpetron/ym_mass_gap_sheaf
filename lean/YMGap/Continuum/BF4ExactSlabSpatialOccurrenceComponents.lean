/-
# The original projected spatial graph has at most S/2 components

Vertices are the original replica-tagged spatial occurrences, not distinct
projected faces. Edges mean a shared projected boundary link. The existing
finite graph algorithm constructs internally connected, pairwise separated
components. Their total mass is exactly S, and every component of a nonzero
original pair has an explicit pair of distinct vertices. Consequently there
are at most S/2 components, at all spins and volumes.

These are actual components of the source. The forest-code injection and
the full six-or-more-face remainder bound remain open.
-/

import YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors
import YMGap.Continuum.FiniteBoolGraphComponentMass
import YMGap.Continuum.BF4ExactSlabCollarDegreeBound

namespace YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphComponentMass

local infix:50 " ≈ " => Q'.eqv
local instance : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))

def adjacent (x y : Occurrence) : Bool := !(disjointTest (edgesOf (project x)) (edgesOf (project y)))

theorem adjacent_of_link (x y : Occurrence) (link : Z4Link)
    (hx : link ∈ edgesOf (project x)) (hy : link ∈ edgesOf (project y)) : adjacent x y=true := by
  cases hd : disjointTest (edgesOf (project x)) (edgesOf (project y)) with
  | false => simp only [adjacent,hd,Bool.not_false]
  | true => exact False.elim ((disjointTest_iff _ _).mp hd link hx hy)

def adjacent_link (x y : Occurrence) (h : adjacent x y=true) :
    Σ' link : Z4Link, (link ∈ edgesOf (project x)) ×' (link ∈ edgesOf (project y)) :=
  sharedLink _ _ (by simpa only [adjacent,Bool.not_eq_true'] using h)

theorem adjacent_symm : SymmetricAdj adjacent := by
  intro x y
  have hforward : adjacent x y=true → adjacent y x=true := fun h =>
    let link := adjacent_link x y h
    adjacent_of_link y x link.1 link.2.2 link.2.1
  have hbackward : adjacent y x=true → adjacent x y=true := fun h =>
    let link := adjacent_link y x h
    adjacent_of_link x y link.1 link.2.2 link.2.1
  cases hxy : adjacent x y <;> cases hyx : adjacent y x <;>
    simp only [hxy,hyx,Bool.false_eq_true] at hforward hbackward ⊢
  · exact False.elim (hbackward True.intro)
  · exact False.elim (hforward True.intro)

theorem original_edge_mem_neighbors {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (x y : Occurrence) (hy : y ∈ occurrences margin pair) (he : adjacent x y=true) :
    y ∈ neighbors margin x := by
  let link := adjacent_link x y he
  exact original_neighbor_mem hs hp x y hy link.1 link.2.1 link.2.2

def original_graph_neighbor (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (x : Occurrence) (hx : x ∈ occurrences margin pair) :
    Σ' y : Occurrence, y ∈ occurrences margin pair ∧ y ≠ x ∧ adjacent x y=true := by
  let link : Z4Link := ((project x).1,(dirsOf (project x).2).1)
  have hl : link ∈ edgesOf (project x) := List.mem_cons_self
  let selected := original_neighbor margin pair hne x hx link hl
  exact ⟨selected.1,selected.2.1,selected.2.2.1,
    adjacent_of_link x selected.1 link hl selected.2.2.2⟩

def components (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : List (List Occurrence) :=
  graphComponents adjacent (occurrences margin pair)

theorem original_component_mass (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    mass (components margin pair)=pairSpatial margin pair :=
  (graph_mass adjacent _).trans (occurrences_length margin pair)

def original_components_connected (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    AllConnected adjacent (components margin pair) :=
  graphComponents_allConnected adjacent adjacent_symm _

theorem original_components_separated (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    DistinctSeparated adjacent (components margin pair) :=
  graphComponents_distinctSeparated adjacent adjacent_symm _

def original_component_pair (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (component : List Occurrence) (hc : component ∈ components margin pair) :
    Σ' x : Occurrence, Σ' y : Occurrence, x ∈ component ∧ y ∈ component ∧ y ≠ x :=
  componentPair adjacent adjacent_symm _ (original_graph_neighbor margin pair hne) component hc

theorem original_component_minimum_two (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (component : List Occurrence) (hc : component ∈ components margin pair) : 2 ≤ component.length :=
  component_minimum_two adjacent adjacent_symm _ (original_graph_neighbor margin pair hne) component hc

theorem original_component_count (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) :
    2*(components margin pair).length ≤ pairSpatial margin pair := by
  rw [← occurrences_length]
  exact twice_component_count_le adjacent adjacent_symm _ (original_graph_neighbor margin pair hne)

end YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents

#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.adjacent
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.adjacent_of_link
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.adjacent_link
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.adjacent_symm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.original_edge_mem_neighbors
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.original_graph_neighbor
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.components
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.original_component_mass
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.original_components_connected
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.original_components_separated
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.original_component_pair
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.original_component_minimum_two
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents.original_component_count
