/-
# Removing unused normalized-vacuum coordinates from vertex Cartesian sums

The production resolver reserves more numerical identifiers than a given
link valence uses.  For the canonical identifier transport it is convenient
to enumerate the whole reserved block, but those unused coordinates must not
leave a spurious factor equal to the size of the label window.

This file proves the exact constructive cylinder identity needed to remove
one such coordinate.  A normalized vacuum coefficient kills every nonzero
spin, while freshness makes the surviving spin-zero update equal to the tail
labelling.  Edge-order invariance then gives a removal theorem for a vacuum
coordinate occurring anywhere in a duplicate-free presentation.
-/

import YMGap.Continuum.Z4CanonicalLinkCartesianTransport
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility

namespace YMGap.Continuum.Z4VertexCartesianVacuumRemoval

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_congr_mem {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, h => by
      change f x + listQSum f xs ≈ g x + listQSum g xs
      exact Q'.add_eqv_congr'
        (h x List.mem_cons_self)
        (listQSum_congr_mem xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem listQSum_zero {A : Type} {f : A → Q'}
    (hf : ∀ x, f x ≈ 0) : ∀ xs, listQSum f xs ≈ 0
  | [] => Q'.eqv_refl 0
  | x :: xs => by
      change f x + listQSum f xs ≈ 0
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' (hf x) (listQSum_zero hf xs))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

/-- Generic vertex-only Cartesian sum, separated out so coordinate deletion
can be stated independently of any particular link presentation. -/
def vertexCartesianSum {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : Q' :=
  listQSum
    (graphVertexProject vertices (packetGraphBareAmplitude edges packet))
    (boundedEdgeLabellings K edges)

private theorem eliminateLinks_eq_on (f g : Nat → Q') : ∀ edges,
    (∀ edge, edge ∈ edges → f edge = g edge) →
      eliminateLinks f edges = eliminateLinks g edges
  | [], _ => rfl
  | edge :: rest, h => by
      have hedge := h edge List.mem_cons_self
      have hrest : ∀ e, e ∈ rest → f e = g e :=
        fun e he => h e (List.mem_cons_of_mem edge he)
      simp only [eliminateLinks]
      rw [hedge, eliminateLinks_eq_on f g rest hrest]

private theorem setEdgeLabel_current (label : EdgeLabelling) (edge : Nat) :
    setEdgeLabel label edge (label edge) = label := by
  funext e
  by_cases he : e = edge
  · subst e
    simp [setEdgeLabel]
  · simp [setEdgeLabel, he]

private theorem graphVertexProject_bare_packet_eq_on {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (A B : Nat → CharacterPacket K)
    (hAB : ∀ edge, edge ∈ edges → A edge = B edge)
    (label : EdgeLabelling) :
    graphVertexProject vertices (packetGraphBareAmplitude edges A) label =
      graphVertexProject vertices (packetGraphBareAmplitude edges B) label := by
  have hbare : packetGraphBareAmplitude edges A label =
      packetGraphBareAmplitude edges B label := by
    unfold packetGraphBareAmplitude
    apply eliminateLinks_eq_on
    intro edge hedge
    rw [hAB edge hedge]
  unfold graphVertexProject
  rw [hbare]

/-- Packet families that agree on the enumerated coordinates give literally
the same vertex Cartesian sum. -/
theorem vertexCartesianSum_packet_eq_on {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (A B : Nat → CharacterPacket K)
    (hAB : ∀ edge, edge ∈ edges → A edge = B edge) :
    vertexCartesianSum edges vertices A =
      vertexCartesianSum edges vertices B := by
  unfold vertexCartesianSum
  apply congrArg
    (fun f => listQSum f (boundedEdgeLabellings K edges))
  funext label
  exact graphVertexProject_bare_packet_eq_on edges vertices A B hAB label

private theorem graphVertexProject_bare_edge_perm {K : Nat}
    (vertices : List TrivalentVertex) (packet : Nat → CharacterPacket K)
    (label : EdgeLabelling) {A B : List Nat} (hperm : A.Perm B) :
    graphVertexProject vertices (packetGraphBareAmplitude A packet) label ≈
      graphVertexProject vertices (packetGraphBareAmplitude B packet) label := by
  unfold graphVertexProject
  by_cases hadmissible : verticesAdmissibleB vertices label = true
  · rw [if_pos hadmissible, if_pos hadmissible]
    exact packetGraphBareAmplitude_edge_perm packet label hperm
  · rw [if_neg hadmissible, if_neg hadmissible]
    exact Q'.eqv_refl 0

/-- The vertex-only Cartesian sum is independent of the order in which its
distinct (or even repeated) coordinate identifiers are enumerated. -/
theorem vertexCartesianSum_edge_perm {K : Nat}
    (vertices : List TrivalentVertex) (packet : Nat → CharacterPacket K)
    {A B : List Nat} (hperm : A.Perm B) :
    vertexCartesianSum A vertices packet ≈
      vertexCartesianSum B vertices packet := by
  unfold vertexCartesianSum
  refine Q'.eqv_trans _
    (listQSum
      (graphVertexProject vertices (packetGraphBareAmplitude B packet))
      (boundedEdgeLabellings K A)) _ ?_ ?_
  · exact listQSum_congr
      (fun label =>
        graphVertexProject_bare_edge_perm vertices packet label hperm) _
  · exact listQSum_bounded_perm K
      (graphVertexProject vertices (packetGraphBareAmplitude B packet)) hperm

private theorem eliminateLinks_extendByVacuum_fresh {K newEdge : Nat}
    (P : Nat → CharacterPacket K) (label : EdgeLabelling) :
    ∀ edges, newEdge ∉ edges →
      eliminateLinks
          (fun edge => coeffAt (extendByVacuum newEdge P edge) (label edge))
          edges =
        eliminateLinks (fun edge => coeffAt (P edge) (label edge)) edges
  | [], _ => rfl
  | edge :: rest, hfresh => by
      have hne : edge ≠ newEdge := by
        intro h
        subst edge
        exact hfresh List.mem_cons_self
      have hrest : newEdge ∉ rest := by
        intro hmem
        exact hfresh (List.mem_cons_of_mem edge hmem)
      simp only [eliminateLinks]
      rw [eliminateLinks_extendByVacuum_fresh P label rest hrest]
      simp [extendByVacuum, hne]

private theorem vacuum_head_spin_ne_zero {K : Nat}
    (newEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (tail : EdgeLabelling)
    (spin : Nat) (hspin : spin ≠ 0) :
    graphVertexProject vertices
        (packetGraphBareAmplitude (newEdge :: edges)
          (extendByVacuum newEdge P))
        (setEdgeLabel tail newEdge spin) ≈ 0 := by
  have hbare : packetGraphBareAmplitude (newEdge :: edges)
      (extendByVacuum newEdge P) (setEdgeLabel tail newEdge spin) ≈ 0 := by
    unfold packetGraphBareAmplitude
    rw [eliminateLinks]
    rw [show setEdgeLabel tail newEdge spin newEdge = spin by
      simp [setEdgeLabel]]
    change coeffAt (extendByVacuum newEdge P newEdge) spin *
        eliminateLinks
          (fun edge => coeffAt (extendByVacuum newEdge P edge)
            (setEdgeLabel tail newEdge spin edge)) edges ≈ 0
    rw [coeffAt_extendByVacuum_newEdge, if_neg hspin]
    exact Q'.zero_mul_eqv _
  unfold graphVertexProject
  by_cases hadmissible : verticesAdmissibleB vertices
      (setEdgeLabel tail newEdge spin) = true
  · rw [if_pos hadmissible]
    exact hbare
  · rw [if_neg hadmissible]
    exact Q'.eqv_refl 0

private theorem vacuum_head_spin_zero {K : Nat}
    (newEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (label : EdgeLabelling)
    (hfresh : newEdge ∉ edges)
    (hlabel : label ∈ boundedEdgeLabellings K edges) :
    graphVertexProject vertices
        (packetGraphBareAmplitude (newEdge :: edges)
          (extendByVacuum newEdge P))
        (setEdgeLabel label newEdge 0) ≈
      graphVertexProject vertices
        (packetGraphBareAmplitude edges P) label := by
  have hzero : label newEdge = 0 :=
    (boundedEdgeLabellings_sound K edges label hlabel).2 newEdge hfresh
  rw [← hzero, setEdgeLabel_current]
  have hbare : packetGraphBareAmplitude (newEdge :: edges)
      (extendByVacuum newEdge P) label ≈
        packetGraphBareAmplitude edges P label := by
    unfold packetGraphBareAmplitude
    change coeffAt (extendByVacuum newEdge P newEdge) (label newEdge) *
        eliminateLinks
          (fun edge => coeffAt (extendByVacuum newEdge P edge)
            (label edge)) edges ≈
      eliminateLinks (fun edge => coeffAt (P edge) (label edge)) edges
    rw [hzero, coeffAt_extendByVacuum_newEdge, if_pos rfl,
      eliminateLinks_extendByVacuum_fresh P label edges hfresh]
    exact Q'.one_mul_eqv _
  unfold graphVertexProject
  by_cases hadmissible : verticesAdmissibleB vertices label = true
  · rw [if_pos hadmissible, if_pos hadmissible]
    exact hbare
  · rw [if_neg hadmissible, if_neg hadmissible]
    exact Q'.eqv_refl 0

/-- Head-form normalized-vacuum cylinder identity for the vertex-only sum. -/
theorem vertexCartesianSum_vacuum_head {K : Nat}
    (newEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (hfresh : newEdge ∉ edges) :
    vertexCartesianSum (newEdge :: edges) vertices
        (extendByVacuum newEdge P) ≈
      vertexCartesianSum edges vertices P := by
  let slice : Nat → Q' := fun spin =>
    listQSum
      (fun label => graphVertexProject vertices
        (packetGraphBareAmplitude (newEdge :: edges)
          (extendByVacuum newEdge P))
        (setEdgeLabel label newEdge spin))
      (boundedEdgeLabellings K edges)
  have hcollapse : fsum slice (K + 1) ≈ slice 0 := by
    apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    · intro spin hspin
      dsimp [slice]
      apply listQSum_zero
      intro label
      exact vacuum_head_spin_ne_zero
        newEdge edges vertices P label spin hspin
    · exact Nat.succ_pos K
  unfold vertexCartesianSum
  refine Q'.eqv_trans _ (fsum slice (K + 1)) _ ?_ ?_
  · exact listQSum_bounded_cons K newEdge edges _
  · refine Q'.eqv_trans _ (slice 0) _ hcollapse ?_
    apply listQSum_congr_mem
    intro label hmem
    exact vacuum_head_spin_zero
      newEdge edges vertices P label hfresh hmem

/-- Remove a normalized-vacuum coordinate occurring anywhere in an edge
presentation.  The permutation hypothesis records its unique extraction as
the head of the remaining coordinate list. -/
theorem vertexCartesianSum_remove_vacuum {K : Nat}
    (newEdge : Nat) (A B : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K)
    (hperm : A.Perm (newEdge :: B)) (hfresh : newEdge ∉ B)
    (hvacuum : packet newEdge = vacuumPacket K) :
    vertexCartesianSum A vertices packet ≈
      vertexCartesianSum B vertices packet := by
  let extended := extendByVacuum newEdge packet
  have hagree : ∀ edge, edge ∈ A → packet edge = extended edge := by
    intro edge _
    by_cases hedge : edge = newEdge
    · subst edge
      simp [extended, extendByVacuum, hvacuum]
    · simp [extended, extendByVacuum, hedge]
  refine Q'.eqv_trans _ (vertexCartesianSum A vertices extended) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (vertexCartesianSum_packet_eq_on A vertices packet extended hagree)
  · refine Q'.eqv_trans _
      (vertexCartesianSum (newEdge :: B) vertices extended) _
      (vertexCartesianSum_edge_perm vertices extended hperm) ?_
    exact vertexCartesianSum_vacuum_head
      newEdge B vertices packet hfresh

/-- Remove a whole duplicate-free list of normalized-vacuum coordinates.
The displayed permutation is also a checkable certificate that the retained
coordinate list has exactly the intended complement. -/
theorem vertexCartesianSum_remove_vacuum_list {K : Nat}
    (vacuumEdges A B : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K)
    (hperm : A.Perm (vacuumEdges ++ B))
    (hnodup : (vacuumEdges ++ B).Nodup)
    (hvacuum : ∀ edge, edge ∈ vacuumEdges →
      packet edge = vacuumPacket K) :
    vertexCartesianSum A vertices packet ≈
      vertexCartesianSum B vertices packet := by
  induction vacuumEdges generalizing A with
  | nil =>
      simpa only [List.nil_append] using
        vertexCartesianSum_edge_perm vertices packet hperm
  | cons edge rest ih =>
      have hshape : A.Perm (edge :: (rest ++ B)) := by
        simpa only [List.cons_append] using hperm
      have htailNodup : (rest ++ B).Nodup := by
        exact (List.nodup_cons.mp (by
          simpa only [List.cons_append] using hnodup)).2
      have hfresh : edge ∉ rest ++ B := by
        exact (List.nodup_cons.mp (by
          simpa only [List.cons_append] using hnodup)).1
      have hedgeVacuum : packet edge = vacuumPacket K :=
        hvacuum edge List.mem_cons_self
      refine Q'.eqv_trans _
        (vertexCartesianSum (rest ++ B) vertices packet) _ ?_ ?_
      · exact vertexCartesianSum_remove_vacuum
          edge A (rest ++ B) vertices packet hshape hfresh hedgeVacuum
      · apply ih (A := rest ++ B)
        · exact List.Perm.refl _
        · exact htailNodup
        · intro e he
          exact hvacuum e (List.mem_cons_of_mem edge he)

end YMGap.Continuum.Z4VertexCartesianVacuumRemoval

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4VertexCartesianVacuumRemoval.vertexCartesianSum_packet_eq_on
#print axioms YMGap.Continuum.Z4VertexCartesianVacuumRemoval.vertexCartesianSum_edge_perm
#print axioms YMGap.Continuum.Z4VertexCartesianVacuumRemoval.vertexCartesianSum_vacuum_head
#print axioms YMGap.Continuum.Z4VertexCartesianVacuumRemoval.vertexCartesianSum_remove_vacuum
#print axioms YMGap.Continuum.Z4VertexCartesianVacuumRemoval.vertexCartesianSum_remove_vacuum_list
