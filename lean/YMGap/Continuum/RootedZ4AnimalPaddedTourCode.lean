/-
# A reusable padded-tour compiler for rooted Z4 animals

The existing strand-component tour compiler is tied to one particular seed
presentation.  The mathematics it uses is more general: a root plaquette, a
duplicate-free finite support containing that root, and a Type-valued witness
that the support is internally connected.

This module packages precisely those inputs as `RootedZ4AnimalData` and runs
the constructive BFS, faithful-neighbour reindexing, Euler tour, and inert
backtrack padding.  Given a support bound `support.length <= budget`, the
result is a deterministic word in the common carrier of cardinality

  `25 ^ (2 * budget) = 625 ^ budget`,

and decoding the word from the supplied root recovers exactly the original
support.  No animal witness is hidden in `Exists`; every object needed by the
compiler remains Type-valued data.

Constructive contract: finite list recursion and the existing Type-valued
connectivity/adjacency witnesses only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, enlarged
heartbeat budget, or trusted external computation.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode

namespace YMGap.Continuum.RootedZ4AnimalPaddedTourCode

set_option autoImplicit false

open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.DecodeTourSound
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SpanningTreeBuild

/-! ## 1. The minimal Type-valued rooted-animal input -/

/-- The exact data consumed by the deterministic Z4 animal compiler. -/
structure RootedZ4AnimalData : Type where
  /-- The plaquette from which the decoder starts. -/
  root : Z4Plaq
  /-- The finite geometric support to encode. -/
  support : List Z4Plaq
  /-- The decoder root is genuinely in the support. -/
  root_mem : root ∈ support
  /-- The support represents a set rather than a multiset. -/
  support_nodup : support.Nodup
  /-- Every two support plaquettes are connected inside the support. -/
  connected : connectedIn (L := z4Chain.toLattice) support

/-! ## 2. Construct the faithful spanning tree -/

/-- The one-root initial BFS state. -/
def rootedZ4AnimalInitialState (animal : RootedZ4AnimalData) :
    BFSState z4Chain animal.root animal.support :=
  initBFS (BL := z4Chain) animal.root animal.support animal.root_mem

/-- The full support size is valid fuel for the initial state. -/
theorem rootedZ4AnimalInitialState_fuel (animal : RootedZ4AnimalData) :
    animal.support.length <= animal.support.length +
      (RTree.nodes (rootedZ4AnimalInitialState animal).tree).length :=
  Nat.le_add_right _ _

/-- The deterministic BFS result, retaining its Type-valued coverage map. -/
def rootedZ4AnimalSpanningResult (animal : RootedZ4AnimalData) :
    Σ' state : BFSState z4Chain animal.root animal.support,
      forall plaquette, plaquette ∈ animal.support ->
        plaquette ∈ RTree.nodes state.tree :=
  grow (BL := z4Chain) (p := animal.root) (X := animal.support)
    animal.connected animal.root_mem animal.support.length
    (rootedZ4AnimalInitialState animal)
    (rootedZ4AnimalInitialState_fuel animal)

/-- The invariant-carrying terminal BFS state. -/
def rootedZ4AnimalSpanningState (animal : RootedZ4AnimalData) :
    BFSState z4Chain animal.root animal.support :=
  (rootedZ4AnimalSpanningResult animal).1

/-- The terminal tree covers every supplied support plaquette. -/
theorem rootedZ4AnimalSpanningState_covers
    (animal : RootedZ4AnimalData) (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ animal.support) :
    plaquette ∈ RTree.nodes (rootedZ4AnimalSpanningState animal).tree :=
  (rootedZ4AnimalSpanningResult animal).2 plaquette hplaquette

/-- The raw adjacency-annotated spanning tree. -/
def rootedZ4AnimalRawTree (animal : RootedZ4AnimalData) : RTree z4Chain :=
  (rootedZ4AnimalSpanningState animal).tree

/-- The raw tree retains the supplied root. -/
theorem rootedZ4AnimalRawTree_root (animal : RootedZ4AnimalData) :
    RTree.root (rootedZ4AnimalRawTree animal) = animal.root :=
  (rootedZ4AnimalSpanningState animal).root_eq

/-- The raw tree and supplied animal have the same support set. -/
theorem rootedZ4AnimalRawTree_sameSupport (animal : RootedZ4AnimalData) :
    sameSupport animal.support (RTree.nodes (rootedZ4AnimalRawTree animal)) :=
  ⟨rootedZ4AnimalSpanningState_covers animal,
    (rootedZ4AnimalSpanningState animal).sub⟩

/-- The raw tree has exactly the supplied animal cardinality. -/
theorem rootedZ4AnimalRawTree_nodes_length (animal : RootedZ4AnimalData) :
    (RTree.nodes (rootedZ4AnimalRawTree animal)).length =
      animal.support.length := by
  apply Nat.le_antisymm
  · exact nodup_subset_length_le
      (RTree.nodes (rootedZ4AnimalRawTree animal)) animal.support
      (rootedZ4AnimalSpanningState animal).nodup
      (rootedZ4AnimalSpanningState animal).sub
  · exact nodup_subset_length_le animal.support
      (RTree.nodes (rootedZ4AnimalRawTree animal)) animal.support_nodup
      (fun plaquette hplaquette =>
        rootedZ4AnimalSpanningState_covers animal plaquette hplaquette)

/-- The raw tree contains no repeated plaquettes. -/
theorem rootedZ4AnimalRawTree_nodes_nodup (animal : RootedZ4AnimalData) :
    (RTree.nodes (rootedZ4AnimalRawTree animal)).Nodup :=
  (rootedZ4AnimalSpanningState animal).nodup

/-- Every raw tree edge retains its actual lattice-adjacency witness. -/
def rootedZ4AnimalRawTree_adjacentEdges (animal : RootedZ4AnimalData) :
    AdjacentEdges (rootedZ4AnimalRawTree animal) :=
  (rootedZ4AnimalSpanningState animal).adj

/-- Reindex every raw edge by its first genuine neighbour index. -/
def rootedZ4AnimalTree (animal : RootedZ4AnimalData) : RTree z4Chain :=
  reindex (rootedZ4AnimalRawTree animal)
    (rootedZ4AnimalRawTree_adjacentEdges animal)

/-- Faithful reindexing preserves the supplied root. -/
theorem rootedZ4AnimalTree_root (animal : RootedZ4AnimalData) :
    RTree.root (rootedZ4AnimalTree animal) = animal.root := by
  unfold rootedZ4AnimalTree
  rw [reindex_root]
  exact rootedZ4AnimalRawTree_root animal

/-- Faithful reindexing preserves the raw node list literally. -/
theorem rootedZ4AnimalTree_nodes (animal : RootedZ4AnimalData) :
    RTree.nodes (rootedZ4AnimalTree animal) =
      RTree.nodes (rootedZ4AnimalRawTree animal) := by
  unfold rootedZ4AnimalTree
  exact reindex_nodes _ _

/-- The faithful tree still has exactly the supplied animal support. -/
theorem rootedZ4AnimalTree_sameSupport (animal : RootedZ4AnimalData) :
    sameSupport animal.support (RTree.nodes (rootedZ4AnimalTree animal)) := by
  rw [rootedZ4AnimalTree_nodes]
  exact rootedZ4AnimalRawTree_sameSupport animal

/-- The faithful tree retains the exact support cardinality. -/
theorem rootedZ4AnimalTree_nodes_length (animal : RootedZ4AnimalData) :
    (RTree.nodes (rootedZ4AnimalTree animal)).length =
      animal.support.length := by
  rw [rootedZ4AnimalTree_nodes]
  exact rootedZ4AnimalRawTree_nodes_length animal

/-- The faithful tree remains duplicate-free. -/
theorem rootedZ4AnimalTree_nodes_nodup (animal : RootedZ4AnimalData) :
    (RTree.nodes (rootedZ4AnimalTree animal)).Nodup := by
  rw [rootedZ4AnimalTree_nodes]
  exact rootedZ4AnimalRawTree_nodes_nodup animal

/-- Every reindexed edge resolves through the literal Z4 neighbour list. -/
theorem rootedZ4AnimalTree_faithful (animal : RootedZ4AnimalData) :
    Faithful (rootedZ4AnimalTree animal) := by
  unfold rootedZ4AnimalTree
  exact reindex_faithful _ _

/-! ## 3. Exact and padded tour words -/

/-- The deterministic 25-symbol Euler-tour word of the supplied animal. -/
def rootedZ4AnimalTourCode (animal : RootedZ4AnimalData) :
    List (Fin (z4Chain.D + 1)) :=
  RTree.tour (rootedZ4AnimalTree animal)

/-- The exact word has the tree-Euler length. -/
theorem rootedZ4AnimalTourCode_length (animal : RootedZ4AnimalData) :
    (rootedZ4AnimalTourCode animal).length =
      2 * (animal.support.length - 1) := by
  unfold rootedZ4AnimalTourCode
  rw [RTree.tour_length, rootedZ4AnimalTree_nodes_length]

/-- Decoding the exact word from the supplied root recovers its support. -/
theorem rootedZ4AnimalTourCode_decode_sameSupport
    (animal : RootedZ4AnimalData) :
    sameSupport animal.support
      (decode z4Chain animal.root (rootedZ4AnimalTourCode animal)) := by
  have hsound := decode_tour_sound z4Chain
    (rootedZ4AnimalTree animal)
    (rootedZ4AnimalTree_faithful animal)
    (rootedZ4AnimalTree_nodes_nodup animal)
  rw [rootedZ4AnimalTree_root animal] at hsound
  exact sameSupport_trans (rootedZ4AnimalTree_sameSupport animal) hsound

/-- The exact word fits within twice any supplied support budget. -/
theorem rootedZ4AnimalTourCode_length_le_two_mul_budget
    (animal : RootedZ4AnimalData) (budget : Nat)
    (hbudget : animal.support.length <= budget) :
    (rootedZ4AnimalTourCode animal).length <= 2 * budget := by
  rw [rootedZ4AnimalTourCode_length]
  omega

/-- The inert backtrack padding needed to reach the common budget length. -/
def rootedZ4AnimalTourPadding (animal : RootedZ4AnimalData)
    (budget : Nat) : Nat :=
  2 * budget - (rootedZ4AnimalTourCode animal).length

/-- The animal tour padded to the common budget-indexed word length. -/
def rootedZ4AnimalPaddedTourCode (animal : RootedZ4AnimalData)
    (budget : Nat) : List (Fin (z4Chain.D + 1)) :=
  rootedZ4AnimalTourCode animal ++
    List.replicate (rootedZ4AnimalTourPadding animal budget)
      (backtrackSymbol z4Chain)

/-- A padded word has exactly twice its supplied support budget. -/
theorem rootedZ4AnimalPaddedTourCode_length
    (animal : RootedZ4AnimalData) (budget : Nat)
    (hbudget : animal.support.length <= budget) :
    (rootedZ4AnimalPaddedTourCode animal budget).length = 2 * budget := by
  unfold rootedZ4AnimalPaddedTourCode rootedZ4AnimalTourPadding
  rw [List.length_append, List.length_replicate]
  have hfit := rootedZ4AnimalTourCode_length_le_two_mul_budget
    animal budget hbudget
  omega

/-- Backtrack padding preserves the exact support decoded from the root. -/
theorem rootedZ4AnimalPaddedTourCode_decode_sameSupport
    (animal : RootedZ4AnimalData) (budget : Nat) :
    sameSupport animal.support
      (decode z4Chain animal.root
        (rootedZ4AnimalPaddedTourCode animal budget)) := by
  unfold rootedZ4AnimalPaddedTourCode
  rw [decode_append_replicate_backtrack]
  exact rootedZ4AnimalTourCode_decode_sameSupport animal

/-! ## 4. The common `625 ^ budget` carrier -/

/-- Every padded tour uses the existing fixed 25-symbol word carrier. -/
def rootedZ4AnimalPaddedTourCarrier (budget : Nat) :
    List (List (Fin (z4Chain.D + 1))) :=
  componentPlaquettePaddedTourCarrier budget

/-- Every budget-fitting animal compiles into the common carrier. -/
theorem rootedZ4AnimalPaddedTourCode_mem_carrier
    (animal : RootedZ4AnimalData) (budget : Nat)
    (hbudget : animal.support.length <= budget) :
    rootedZ4AnimalPaddedTourCode animal budget ∈
      rootedZ4AnimalPaddedTourCarrier budget := by
  unfold rootedZ4AnimalPaddedTourCarrier
    componentPlaquettePaddedTourCarrier
  exact mem_choiceSeqs_of_length _ _ _
    (rootedZ4AnimalPaddedTourCode_length animal budget hbudget)

/-- The common shape carrier has exactly `625 ^ budget` words. -/
theorem rootedZ4AnimalPaddedTourCarrier_length (budget : Nat) :
    (rootedZ4AnimalPaddedTourCarrier budget).length = 625 ^ budget := by
  unfold rootedZ4AnimalPaddedTourCarrier
  exact componentPlaquettePaddedTourCarrier_length budget

/-- At a common root, equal padded codes force support equality up to
membership, even when the two animal presentations have different list order. -/
theorem rootedZ4AnimalPaddedTourCode_eq_sameSupport
    (left right : RootedZ4AnimalData) (leftBudget rightBudget : Nat)
    (hroot : left.root = right.root)
    (hcode : rootedZ4AnimalPaddedTourCode left leftBudget =
      rootedZ4AnimalPaddedTourCode right rightBudget) :
    sameSupport (L := z4Chain.toLattice) left.support right.support := by
  have hleft := rootedZ4AnimalPaddedTourCode_decode_sameSupport
    left leftBudget
  have hright := rootedZ4AnimalPaddedTourCode_decode_sameSupport
    right rightBudget
  rw [hroot, hcode] at hleft
  exact sameSupport_trans hleft (sameSupport_symm hright)

#print axioms RootedZ4AnimalData
#print axioms rootedZ4AnimalInitialState
#print axioms rootedZ4AnimalSpanningResult
#print axioms rootedZ4AnimalRawTree_sameSupport
#print axioms rootedZ4AnimalTree_faithful
#print axioms rootedZ4AnimalTourCode
#print axioms rootedZ4AnimalTourCode_decode_sameSupport
#print axioms rootedZ4AnimalPaddedTourCode
#print axioms rootedZ4AnimalPaddedTourCode_length
#print axioms rootedZ4AnimalPaddedTourCode_decode_sameSupport
#print axioms rootedZ4AnimalPaddedTourCode_mem_carrier
#print axioms rootedZ4AnimalPaddedTourCarrier_length
#print axioms rootedZ4AnimalPaddedTourCode_eq_sameSupport

end YMGap.Continuum.RootedZ4AnimalPaddedTourCode
