/-
# Half-edge occurrences in an ordered resolved trivalent network

An internal strand continuation first needs the two *positions* carrying a
shared graph-edge identifier.  This module separates that position-level
question from the bounded strand slot.

A `ResolvedNetworkHalfEdge` is a vertex position and one of its three legs.
All half-edges are explicitly enumerated.  Mapping that enumeration to edge
identifiers is proved equal to the flattened edge word of the original
ordered vertex list.  Consequently the exact physical/internal occurrence
counts of `CanonicalLinkEdgeOccurrenceMultiplicity` transfer without loss to
the actual resolved network, including its proof-indexed vertex list.

Constructive contract: finite dependent indices, explicit list enumeration,
and decidable filtering only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity

namespace YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState

/-! ## 1. The finite half-edge carrier -/

/-- A trivalent leg at one bounded position of a resolved network. -/
structure ResolvedNetworkHalfEdge
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) : Type where
  vertexIndex : Fin network.resolved.length
  leg : TrivalentLeg
  deriving DecidableEq

/-- The selected resolved vertex. -/
def ResolvedNetworkHalfEdge.vertex
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (halfEdge : ResolvedNetworkHalfEdge network) : TrivalentVertex :=
  (resolvedVertexAt network halfEdge.vertexIndex).vertex

/-- The graph-edge identifier at this half-edge. -/
def ResolvedNetworkHalfEdge.edgeId
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (halfEdge : ResolvedNetworkHalfEdge network) : Nat :=
  vertexEdgeId halfEdge.vertex halfEdge.leg

/-- The three half-edges at one bounded vertex position. -/
def halfEdgesAt
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (index : Fin network.resolved.length) :
    List (ResolvedNetworkHalfEdge network) :=
  [⟨index, .a⟩, ⟨index, .b⟩, ⟨index, .c⟩]

/-- Every half-edge of the ordered resolved network. -/
def allResolvedNetworkHalfEdges
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) :
    List (ResolvedNetworkHalfEdge network) :=
  (List.finRange network.resolved.length).flatMap
    (halfEdgesAt network)

/-- The half-edge enumeration is exhaustive. -/
theorem ResolvedNetworkHalfEdge.mem_all
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (halfEdge : ResolvedNetworkHalfEdge network) :
    halfEdge ∈ allResolvedNetworkHalfEdges network := by
  cases halfEdge with
  | mk index leg =>
      apply List.mem_flatMap.mpr
      refine ⟨index, List.mem_finRange index, ?_⟩
      cases leg <;> simp [halfEdgesAt]

private theorem map_nodup_of_injective {A B : Type}
    (f : A -> B) (hinjective : ∀ {left right}, f left = f right -> left = right) :
    ∀ {entries : List A}, entries.Nodup -> (entries.map f).Nodup
  | [], _ => List.nodup_nil
  | head :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
        have hsame := hinjective heq.symm
        subst item
        exact hparts.1 hitem
      · exact map_nodup_of_injective f hinjective hparts.2

private theorem finRange_nodup : ∀ n : Nat, (List.finRange n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.finRange_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, _, heq⟩ := List.mem_map.mp hmem
        have hvalue := congrArg Fin.val heq
        simp at hvalue
      · exact map_nodup_of_injective Fin.succ
          (fun heq => Fin.ext (by
            have hvalue := congrArg Fin.val heq
            simpa using hvalue))
          (finRange_nodup n)

private theorem halfEdgesAt_nodup
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (index : Fin network.resolved.length) :
    (halfEdgesAt network index).Nodup := by
  simp [halfEdgesAt]

private theorem mem_halfEdgesAt_vertexIndex
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    {index : Fin network.resolved.length}
    {halfEdge : ResolvedNetworkHalfEdge network}
    (hmem : halfEdge ∈ halfEdgesAt network index) :
    halfEdge.vertexIndex = index := by
  simp [halfEdgesAt] at hmem
  rcases hmem with rfl | rfl | rfl <;> rfl

private theorem flatMap_halfEdgesAt_nodup
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) :
    ∀ {indices : List (Fin network.resolved.length)},
      indices.Nodup ->
      (indices.flatMap (halfEdgesAt network)).Nodup
  | [], _ => List.nodup_nil
  | index :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨halfEdgesAt_nodup network index,
        flatMap_halfEdgesAt_nodup network hparts.2, ?_⟩
      intro left hleft right hright heq
      obtain ⟨otherIndex, hotherIndex, hrightAt⟩ :=
        List.mem_flatMap.mp hright
      have hleftIndex := mem_halfEdgesAt_vertexIndex hleft
      have hrightIndex : right.vertexIndex = index :=
        (congrArg ResolvedNetworkHalfEdge.vertexIndex heq).symm.trans
          hleftIndex
      have hrightAtIndex := mem_halfEdgesAt_vertexIndex hrightAt
      have hotherIndexEq : otherIndex = index :=
        hrightAtIndex.symm.trans hrightIndex
      rw [hotherIndexEq] at hotherIndex
      exact hparts.1 hotherIndex

/-- No half-edge position is duplicated by the explicit enumeration. -/
theorem allResolvedNetworkHalfEdges_nodup
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) :
    (allResolvedNetworkHalfEdges network).Nodup :=
  flatMap_halfEdgesAt_nodup network
    (finRange_nodup network.resolved.length)

/-! ## 2. Exact recovery of the original edge word -/

private theorem finRange_map_get {A : Type} (entries : List A) :
    (List.finRange entries.length).map entries.get = entries := by
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using
    (List.ofFn_getElem (xs := entries))

/-- Mapping the enumerated half-edges to identifiers gives exactly the
flattened edge word of the resolved vertex list. -/
theorem allResolvedNetworkHalfEdges_map_edgeId
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) :
    (allResolvedNetworkHalfEdges network).map
        ResolvedNetworkHalfEdge.edgeId =
      network.resolved.flatMap
        (fun resolved => vertexEdgeIds resolved.vertex) := by
  unfold allResolvedNetworkHalfEdges
  rw [List.map_flatMap]
  change (List.finRange network.resolved.length).flatMap
      (fun index =>
        vertexEdgeIds (network.resolved.get index).vertex) = _
  rw [← List.flatMap_map]
  have hgetVertices :
      (List.finRange network.resolved.length).map
          (fun index => (network.resolved.get index).vertex) =
        network.resolved.map (fun resolved => resolved.vertex) := by
    change (List.finRange network.resolved.length).map
        ((fun resolved => resolved.vertex) ∘ network.resolved.get) = _
    rw [← List.map_map]
    rw [finRange_map_get]
  rw [hgetVertices]
  rw [List.flatMap_map]

/-- The resolved edge word is exactly the edge word of the original ordered
vertex list. -/
theorem resolvedNetworkEdgeWord_eq
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) :
    network.resolved.flatMap
        (fun resolved => vertexEdgeIds resolved.vertex) =
      vertices.flatMap vertexEdgeIds := by
  rw [← List.flatMap_map]
  rw [network.vertices_exact]

/-! ## 3. Fibers of a graph-edge identifier -/

/-- All half-edge positions carrying a selected graph-edge identifier. -/
def halfEdgesOnEdge
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (edge : Nat) : List (ResolvedNetworkHalfEdge network) :=
  (allResolvedNetworkHalfEdges network).filter
    (fun halfEdge => decide (halfEdge.edgeId = edge))

/-- Filtering to one edge preserves distinct half-edge positions. -/
theorem halfEdgesOnEdge_nodup
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (edge : Nat) :
    (halfEdgesOnEdge network edge).Nodup :=
  (allResolvedNetworkHalfEdges_nodup network).filter _

private theorem length_filter_eq_count_map {A : Type}
    (entries : List A) (code : A -> Nat) (target : Nat) :
    (entries.filter (fun entry => decide (code entry = target))).length =
      (entries.map code).count target := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      by_cases heq : code head = target
      · simp [heq, ih]
      · simp [heq, ih]

/-- Fiber cardinality is exactly the occurrence count in the original
ordered vertex word. -/
theorem halfEdgesOnEdge_length
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (edge : Nat) :
    (halfEdgesOnEdge network edge).length =
      (vertices.flatMap vertexEdgeIds).count edge := by
  unfold halfEdgesOnEdge
  rw [length_filter_eq_count_map]
  rw [allResolvedNetworkHalfEdges_map_edgeId]
  rw [resolvedNetworkEdgeWord_eq]

/-! ## 4. Canonical link consequences -/

/-- A physical identifier has one half-edge in the actual resolved canonical
network. -/
theorem canonicalLinkResolved_halfEdgesOnEdge_length_physical
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge < degree) :
    (halfEdgesOnEdge
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) edge).length = 1 := by
  rw [halfEdgesOnEdge_length]
  exact canonicalLinkEdgeOccurrences_count_physical hdegree hedge

/-- A genuine internal identifier has exactly two half-edges in the actual
resolved canonical network. -/
theorem canonicalLinkResolved_halfEdgesOnEdge_length_internal
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree) :
    (halfEdgesOnEdge
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) edge).length = 2 := by
  rw [halfEdgesOnEdge_length]
  exact canonicalLinkEdgeOccurrences_count_internal hdegree hedge

#print axioms ResolvedNetworkHalfEdge
#print axioms ResolvedNetworkHalfEdge.vertex
#print axioms ResolvedNetworkHalfEdge.edgeId
#print axioms halfEdgesAt
#print axioms allResolvedNetworkHalfEdges
#print axioms ResolvedNetworkHalfEdge.mem_all
#print axioms allResolvedNetworkHalfEdges_nodup
#print axioms allResolvedNetworkHalfEdges_map_edgeId
#print axioms resolvedNetworkEdgeWord_eq
#print axioms halfEdgesOnEdge
#print axioms halfEdgesOnEdge_nodup
#print axioms halfEdgesOnEdge_length
#print axioms canonicalLinkResolved_halfEdgesOnEdge_length_physical
#print axioms canonicalLinkResolved_halfEdgesOnEdge_length_internal

end YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges
