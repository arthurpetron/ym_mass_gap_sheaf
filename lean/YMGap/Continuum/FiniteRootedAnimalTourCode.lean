/-
# A canonical tour code for any finite rooted lattice animal

The component-specific tour compiler already contains a constructive BFS
spanning-tree algorithm.  This module exposes the underlying mathematical
construction at its natural generality: any duplicate-free, internally
connected finite support with a chosen member root has a deterministic
faithful tree and Euler-tour word.

Padding that word to `2 * massBudget` backtracks preserves its decoded support.
If the support has at most `massBudget` sites, the word lies in a carrier of
cardinality

  ((D + 1)^2)^massBudget.

For the genuine 4D plaquette graph (`D = 24`) this is `625^massBudget`.

Constructive contract: all connectivity and trees are Type-valued data; the
construction uses finite BFS and explicit decoding only, with no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode

namespace YMGap.Continuum.FiniteRootedAnimalTourCode

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

/-! ## 1. Type-valued rooted animal data -/

/-- A finite support with an explicit root, no duplicates, and constructive
internal paths between all of its members. -/
structure RootedConnectedAnimal (BL : BddLattice) : Type where
  root : BL.toLattice.Plaquette
  support : Polymer BL.toLattice
  root_mem : root ∈ support
  support_nodup : support.Nodup
  connected : connectedIn support

/-! ## 2. Deterministic spanning tree and faithful tour -/

def rootedAnimalInitialState
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    BFSState BL animal.root animal.support :=
  initBFS animal.root animal.support animal.root_mem

def rootedAnimalSpanningResult
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    Σ' state : BFSState BL animal.root animal.support,
      ∀ plaquette, plaquette ∈ animal.support →
        plaquette ∈ RTree.nodes state.tree :=
  grow animal.connected animal.root_mem animal.support.length
    (rootedAnimalInitialState animal) (Nat.le_add_right _ _)

def rootedAnimalSpanningState
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    BFSState BL animal.root animal.support :=
  (rootedAnimalSpanningResult animal).1

theorem rootedAnimalSpanningState_covers
    {BL : BddLattice} (animal : RootedConnectedAnimal BL)
    (plaquette : BL.toLattice.Plaquette)
    (hplaquette : plaquette ∈ animal.support) :
    plaquette ∈ RTree.nodes (rootedAnimalSpanningState animal).tree :=
  (rootedAnimalSpanningResult animal).2 plaquette hplaquette

def rootedAnimalRawTree
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) : RTree BL :=
  (rootedAnimalSpanningState animal).tree

theorem rootedAnimalRawTree_root
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    RTree.root (rootedAnimalRawTree animal) = animal.root :=
  (rootedAnimalSpanningState animal).root_eq

theorem rootedAnimalRawTree_sameSupport
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    sameSupport animal.support (RTree.nodes (rootedAnimalRawTree animal)) :=
  ⟨rootedAnimalSpanningState_covers animal,
    (rootedAnimalSpanningState animal).sub⟩

theorem rootedAnimalRawTree_nodes_length
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    (RTree.nodes (rootedAnimalRawTree animal)).length =
      animal.support.length := by
  apply Nat.le_antisymm
  · exact AdjSpanningBuild.nodup_subset_length_le
      (RTree.nodes (rootedAnimalRawTree animal)) animal.support
      (rootedAnimalSpanningState animal).nodup
      (rootedAnimalSpanningState animal).sub
  · exact AdjSpanningBuild.nodup_subset_length_le
      animal.support (RTree.nodes (rootedAnimalRawTree animal))
      animal.support_nodup
      (rootedAnimalSpanningState_covers animal)

theorem rootedAnimalRawTree_nodes_nodup
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    (RTree.nodes (rootedAnimalRawTree animal)).Nodup :=
  (rootedAnimalSpanningState animal).nodup

def rootedAnimalRawTree_adjacentEdges
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    AdjacentEdges (rootedAnimalRawTree animal) :=
  (rootedAnimalSpanningState animal).adj

/-- Reindex the BFS tree by literal neighbor positions so the existing
decoder follows every edge. -/
def rootedAnimalTree
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) : RTree BL :=
  reindex (rootedAnimalRawTree animal)
    (rootedAnimalRawTree_adjacentEdges animal)

theorem rootedAnimalTree_root
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    RTree.root (rootedAnimalTree animal) = animal.root := by
  unfold rootedAnimalTree
  rw [reindex_root]
  exact rootedAnimalRawTree_root animal

theorem rootedAnimalTree_nodes
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    RTree.nodes (rootedAnimalTree animal) =
      RTree.nodes (rootedAnimalRawTree animal) := by
  unfold rootedAnimalTree
  exact reindex_nodes _ _

theorem rootedAnimalTree_sameSupport
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    sameSupport animal.support (RTree.nodes (rootedAnimalTree animal)) := by
  rw [rootedAnimalTree_nodes]
  exact rootedAnimalRawTree_sameSupport animal

theorem rootedAnimalTree_nodes_length
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    (RTree.nodes (rootedAnimalTree animal)).length =
      animal.support.length := by
  rw [rootedAnimalTree_nodes]
  exact rootedAnimalRawTree_nodes_length animal

theorem rootedAnimalTree_nodes_nodup
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    (RTree.nodes (rootedAnimalTree animal)).Nodup := by
  rw [rootedAnimalTree_nodes]
  exact rootedAnimalRawTree_nodes_nodup animal

theorem rootedAnimalTree_faithful
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    Faithful (rootedAnimalTree animal) := by
  unfold rootedAnimalTree
  exact reindex_faithful _ _

/-- Deterministic Euler-tour word of the rooted animal. -/
def rootedAnimalTourCode
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    List (Fin (BL.D + 1)) :=
  RTree.tour (rootedAnimalTree animal)

theorem rootedAnimalTourCode_length
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    (rootedAnimalTourCode animal).length =
      2 * (animal.support.length - 1) := by
  unfold rootedAnimalTourCode
  rw [RTree.tour_length, rootedAnimalTree_nodes_length]

/-- Decoding from the fixed root recovers exactly the animal support. -/
theorem rootedAnimalTourCode_decode_sameSupport
    {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    sameSupport animal.support
      (decode BL animal.root (rootedAnimalTourCode animal)) := by
  have hsound := decode_tour_sound BL
    (rootedAnimalTree animal)
    (rootedAnimalTree_faithful animal)
    (rootedAnimalTree_nodes_nodup animal)
  rw [rootedAnimalTree_root animal] at hsound
  exact sameSupport_trans
    (rootedAnimalTree_sameSupport animal) hsound

/-! ## 3. A common mass-budget carrier -/

/-- Pad the exact tour with inert backtracks to the common length
`2 * massBudget`. -/
def rootedAnimalPaddedTourCode
    {BL : BddLattice} (animal : RootedConnectedAnimal BL)
    (massBudget : Nat) : List (Fin (BL.D + 1)) :=
  rootedAnimalTourCode animal ++
    List.replicate
      (2 * massBudget - (rootedAnimalTourCode animal).length)
      (backtrackSymbol BL)

theorem rootedAnimalPaddedTourCode_length
    {BL : BddLattice} (animal : RootedConnectedAnimal BL)
    (massBudget : Nat)
    (hsupport : animal.support.length ≤ massBudget) :
    (rootedAnimalPaddedTourCode animal massBudget).length =
      2 * massBudget := by
  have hfit : (rootedAnimalTourCode animal).length ≤
      2 * massBudget := by
    rw [rootedAnimalTourCode_length]
    omega
  unfold rootedAnimalPaddedTourCode
  simp only [List.length_append, List.length_replicate]
  omega

theorem rootedAnimalPaddedTourCode_decode_sameSupport
    {BL : BddLattice} (animal : RootedConnectedAnimal BL)
    (massBudget : Nat) :
    sameSupport animal.support
      (decode BL animal.root
        (rootedAnimalPaddedTourCode animal massBudget)) := by
  unfold rootedAnimalPaddedTourCode
  rw [decode_append_replicate_backtrack]
  exact rootedAnimalTourCode_decode_sameSupport animal

/-- Every word over the `D+1` descend/backtrack alphabet at the common
mass-budget length. -/
def rootedAnimalPaddedTourCarrier
    (BL : BddLattice) (massBudget : Nat) :
    List (List (Fin (BL.D + 1))) :=
  choiceSeqs (BL.D + 1) (2 * massBudget)

theorem rootedAnimalPaddedTourCode_mem_carrier
    {BL : BddLattice} (animal : RootedConnectedAnimal BL)
    (massBudget : Nat)
    (hsupport : animal.support.length ≤ massBudget) :
    rootedAnimalPaddedTourCode animal massBudget ∈
      rootedAnimalPaddedTourCarrier BL massBudget := by
  unfold rootedAnimalPaddedTourCarrier
  exact mem_choiceSeqs_of_length _ _ _
    (rootedAnimalPaddedTourCode_length animal massBudget hsupport)

theorem rootedAnimalPaddedTourCarrier_length
    (BL : BddLattice) (massBudget : Nat) :
    (rootedAnimalPaddedTourCarrier BL massBudget).length =
      ((BL.D + 1) ^ 2) ^ massBudget := by
  unfold rootedAnimalPaddedTourCarrier
  rw [choiceSeqs_length]
  rw [Nat.pow_mul]

/-- At the genuine 4D plaquette degree, the global shape carrier is exactly
`625^massBudget`. -/
theorem z4RootedAnimalPaddedTourCarrier_length (massBudget : Nat) :
    (rootedAnimalPaddedTourCarrier z4Chain massBudget).length =
      625 ^ massBudget := by
  rw [rootedAnimalPaddedTourCarrier_length]
  rfl

/-- At a common root, equality of padded words forces equality of decoded
support sets. -/
theorem rootedAnimalPaddedTourCode_eq_sameSupport
    {BL : BddLattice}
    (left right : RootedConnectedAnimal BL)
    (massBudget : Nat)
    (hroot : left.root = right.root)
    (hcode : rootedAnimalPaddedTourCode left massBudget =
      rootedAnimalPaddedTourCode right massBudget) :
    sameSupport left.support right.support := by
  have hleft := rootedAnimalPaddedTourCode_decode_sameSupport
    left massBudget
  have hright := rootedAnimalPaddedTourCode_decode_sameSupport
    right massBudget
  rw [hroot, hcode] at hleft
  exact sameSupport_trans hleft (sameSupport_symm hright)

end YMGap.Continuum.FiniteRootedAnimalTourCode

#print axioms YMGap.Continuum.FiniteRootedAnimalTourCode.rootedAnimalSpanningResult
#print axioms YMGap.Continuum.FiniteRootedAnimalTourCode.rootedAnimalTourCode
#print axioms YMGap.Continuum.FiniteRootedAnimalTourCode.rootedAnimalTourCode_decode_sameSupport
#print axioms YMGap.Continuum.FiniteRootedAnimalTourCode.rootedAnimalPaddedTourCode_mem_carrier
#print axioms YMGap.Continuum.FiniteRootedAnimalTourCode.z4RootedAnimalPaddedTourCarrier_length
#print axioms YMGap.Continuum.FiniteRootedAnimalTourCode.rootedAnimalPaddedTourCode_eq_sameSupport
