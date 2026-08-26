/-
# Deterministic Euler-tour codes for rooted strand-component animals

`CompactDualSlabFaceStrandComponentAnimal` projects every rooted physical
strand component to a genuine degree-24 Z4 plaquette animal.  This module runs
the existing constructive spanning-tree builder on that particular animal,
reindexes every tree edge by its first literal neighbour index, and takes the
tree's depth-first Euler tour.

The result is data, not merely propositional existence: every seed has a
deterministic word over the 25-symbol descend/backtrack alphabet.  Its length is
exactly twice one less than the deduplicated plaquette-support size, it belongs
to the existing `codes z4Chain` carrier, and decoding it from the literal root
recovers exactly the geometric component support.

Constructive contract: finite list recursion and the existing Type-valued
connectivity/adjacency witnesses only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimalTourCode

set_option autoImplicit false

open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
open YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.DecodeTourSound
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SpanningTreeBuild
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Run the constructive spanning-tree builder on the component animal -/

/-- The single-root initial BFS state for the component animal. -/
def componentPlaquetteInitialState
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    BFSState z4Chain
      (slabPlaquetteAt extent seed.root.faceId)
      (componentPlaquetteSupport seed) :=
  initBFS (BL := z4Chain)
    (slabPlaquetteAt extent seed.root.faceId)
    (componentPlaquetteSupport seed)
    (rootPlaquette_mem_componentPlaquetteSupport seed)

/-- The full support size is valid fuel for the one-root initial state. -/
theorem componentPlaquetteInitialState_fuel
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (componentPlaquetteSupport seed).length <=
      (componentPlaquetteSupport seed).length +
        (RTree.nodes (componentPlaquetteInitialState seed).tree).length :=
  Nat.le_add_right _ _

/-- The complete deterministic output of the BFS growth recursion for one
component's geometric support. -/
def componentPlaquetteSpanningResult
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    Σ' state : BFSState z4Chain
        (slabPlaquetteAt extent seed.root.faceId)
        (componentPlaquetteSupport seed),
      forall plaquette, plaquette ∈ componentPlaquetteSupport seed ->
        plaquette ∈ RTree.nodes state.tree :=
  grow (BL := z4Chain)
    (p := slabPlaquetteAt extent seed.root.faceId)
    (X := componentPlaquetteSupport seed)
    (componentPlaquetteSupport_connected seed)
    (rootPlaquette_mem_componentPlaquetteSupport seed)
    (componentPlaquetteSupport seed).length
    (componentPlaquetteInitialState seed)
    (componentPlaquetteInitialState_fuel seed)

/-- The invariant-carrying final BFS state. -/
def componentPlaquetteSpanningState
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    BFSState z4Chain
      (slabPlaquetteAt extent seed.root.faceId)
      (componentPlaquetteSupport seed) :=
  (componentPlaquetteSpanningResult seed).1

/-- The final BFS tree covers the entire component animal. -/
theorem componentPlaquetteSpanningState_covers
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ componentPlaquetteSupport seed) :
    plaquette ∈ RTree.nodes (componentPlaquetteSpanningState seed).tree := by
  exact (componentPlaquetteSpanningResult seed).2 plaquette hplaquette

/-- The raw adjacency-annotated spanning tree produced by BFS. -/
def componentPlaquetteRawTree
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : RTree z4Chain :=
  (componentPlaquetteSpanningState seed).tree

/-- The raw tree retains the selected component root. -/
theorem componentPlaquetteRawTree_root
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    RTree.root (componentPlaquetteRawTree seed) =
      slabPlaquetteAt extent seed.root.faceId :=
  (componentPlaquetteSpanningState seed).root_eq

/-- The raw tree has exactly the geometric component support. -/
theorem componentPlaquetteRawTree_sameSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    sameSupport (componentPlaquetteSupport seed)
      (RTree.nodes (componentPlaquetteRawTree seed)) :=
  ⟨componentPlaquetteSpanningState_covers seed,
    (componentPlaquetteSpanningState seed).sub⟩

/-- The raw tree node list has exactly the animal's cardinality. -/
theorem componentPlaquetteRawTree_nodes_length
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (RTree.nodes (componentPlaquetteRawTree seed)).length =
      (componentPlaquetteSupport seed).length := by
  apply Nat.le_antisymm
  · exact nodup_subset_length_le
      (RTree.nodes (componentPlaquetteRawTree seed))
      (componentPlaquetteSupport seed)
      (componentPlaquetteSpanningState seed).nodup
      (componentPlaquetteSpanningState seed).sub
  · exact nodup_subset_length_le
      (componentPlaquetteSupport seed)
      (RTree.nodes (componentPlaquetteRawTree seed))
      (componentPlaquetteSupport_nodup seed)
      (fun plaquette hplaquette =>
        componentPlaquetteSpanningState_covers seed plaquette hplaquette)

/-- The raw tree has no repeated plaquette nodes. -/
theorem componentPlaquetteRawTree_nodes_nodup
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (RTree.nodes (componentPlaquetteRawTree seed)).Nodup :=
  (componentPlaquetteSpanningState seed).nodup

/-- Every raw tree edge carries its genuine Z4 adjacency witness. -/
def componentPlaquetteRawTree_adjacentEdges
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    AdjacentEdges (componentPlaquetteRawTree seed) :=
  (componentPlaquetteSpanningState seed).adj

/-! ## 2. Faithful reindexing and the deterministic tour word -/

/-- Reindex the raw tree by the first genuine index of each adjacent child.
This is the tree the existing decoder can follow literally. -/
def componentPlaquetteTree
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : RTree z4Chain :=
  reindex (componentPlaquetteRawTree seed)
    (componentPlaquetteRawTree_adjacentEdges seed)

/-- Faithful reindexing preserves the selected root. -/
theorem componentPlaquetteTree_root
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    RTree.root (componentPlaquetteTree seed) =
      slabPlaquetteAt extent seed.root.faceId := by
  unfold componentPlaquetteTree
  rw [reindex_root]
  exact componentPlaquetteRawTree_root seed

/-- Faithful reindexing preserves the raw tree's literal node list. -/
theorem componentPlaquetteTree_nodes
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    RTree.nodes (componentPlaquetteTree seed) =
      RTree.nodes (componentPlaquetteRawTree seed) := by
  unfold componentPlaquetteTree
  exact reindex_nodes _ _

/-- The faithful tree still has exactly the component's support. -/
theorem componentPlaquetteTree_sameSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    sameSupport (componentPlaquetteSupport seed)
      (RTree.nodes (componentPlaquetteTree seed)) := by
  rw [componentPlaquetteTree_nodes]
  exact componentPlaquetteRawTree_sameSupport seed

/-- The faithful tree node count is the geometric support size. -/
theorem componentPlaquetteTree_nodes_length
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (RTree.nodes (componentPlaquetteTree seed)).length =
      (componentPlaquetteSupport seed).length := by
  rw [componentPlaquetteTree_nodes]
  exact componentPlaquetteRawTree_nodes_length seed

/-- The faithful tree remains duplicate-free. -/
theorem componentPlaquetteTree_nodes_nodup
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (RTree.nodes (componentPlaquetteTree seed)).Nodup := by
  rw [componentPlaquetteTree_nodes]
  exact componentPlaquetteRawTree_nodes_nodup seed

/-- Every reindexed tree edge resolves through the literal Z4 neighbour list. -/
theorem componentPlaquetteTree_faithful
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    Faithful (componentPlaquetteTree seed) := by
  unfold componentPlaquetteTree
  exact reindex_faithful _ _

/-- The deterministic 25-symbol Euler-tour word of the component animal. -/
def componentPlaquetteTourCode
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    List (Fin (z4Chain.D + 1)) :=
  RTree.tour (componentPlaquetteTree seed)

/-- The tour word has the exact tree-Euler length. -/
theorem componentPlaquetteTourCode_length
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (componentPlaquetteTourCode seed).length =
      2 * ((componentPlaquetteSupport seed).length - 1) := by
  unfold componentPlaquetteTourCode
  rw [RTree.tour_length, componentPlaquetteTree_nodes_length]

/-- The production tour is a literal member of the existing complete
degree-24 animal-code carrier at the geometric support size. -/
theorem componentPlaquetteTourCode_mem_codes
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    componentPlaquetteTourCode seed ∈
      codes z4Chain (componentPlaquetteSupport seed).length :=
  mem_codes_of_length z4Chain _ _
    (componentPlaquetteTourCode_length seed)

/-! ## 3. Exact decode support -/

/-- **Shape-code contraction.**  Decoding the deterministic tour from its
literal selected root recovers exactly the component's geometric plaquette
support. -/
theorem componentPlaquetteTourCode_decode_sameSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    sameSupport (componentPlaquetteSupport seed)
      (decode z4Chain (slabPlaquetteAt extent seed.root.faceId)
        (componentPlaquetteTourCode seed)) := by
  have hsound := decode_tour_sound z4Chain
    (componentPlaquetteTree seed)
    (componentPlaquetteTree_faithful seed)
    (componentPlaquetteTree_nodes_nodup seed)
  rw [componentPlaquetteTree_root seed] at hsound
  exact sameSupport_trans
    (componentPlaquetteTree_sameSupport seed) hsound

#print axioms componentPlaquetteInitialState
#print axioms componentPlaquetteInitialState_fuel
#print axioms componentPlaquetteSpanningResult
#print axioms componentPlaquetteSpanningState
#print axioms componentPlaquetteSpanningState_covers
#print axioms componentPlaquetteRawTree
#print axioms componentPlaquetteRawTree_root
#print axioms componentPlaquetteRawTree_sameSupport
#print axioms componentPlaquetteRawTree_nodes_length
#print axioms componentPlaquetteRawTree_nodes_nodup
#print axioms componentPlaquetteRawTree_adjacentEdges
#print axioms componentPlaquetteTree
#print axioms componentPlaquetteTree_root
#print axioms componentPlaquetteTree_nodes
#print axioms componentPlaquetteTree_sameSupport
#print axioms componentPlaquetteTree_nodes_length
#print axioms componentPlaquetteTree_nodes_nodup
#print axioms componentPlaquetteTree_faithful
#print axioms componentPlaquetteTourCode
#print axioms componentPlaquetteTourCode_length
#print axioms componentPlaquetteTourCode_mem_codes
#print axioms componentPlaquetteTourCode_decode_sameSupport

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimalTourCode
