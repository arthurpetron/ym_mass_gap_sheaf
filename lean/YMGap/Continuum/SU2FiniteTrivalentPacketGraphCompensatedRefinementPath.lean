/-
# Certified finite paths of compensated graph refinements

The local history theorem is packaged here into a state, a certified
identity-refinement move, and an inductive finite path.  Every move updates
the graph, vertices, packets, and reciprocal history together.  The complete
integer-time correlator is exactly invariant along every such finite path.

This is the finite-path core required by a graph-volume directed system.  It
does not yet prove common refinements for arbitrary graphs, volume-uniform
spectral bounds, or existence of an infinite-volume colimit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementHistoryCorrelator

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementHistoryCorrelator

local infix:50 " ≈ " => Q'.eqv

/-- A finite packet graph together with every copied-edge reciprocal already
accumulated by its refinement history. -/
structure CompensatedGraphState (K : Nat) where
  edges : List Nat
  vertices : List TrivalentVertex
  packet : Nat → CharacterPacket K
  copiedEdges : List Nat
  copied_mem : ∀ edge, edge ∈ copiedEdges → edge ∈ edges

/-- The positive finite spectral model carried by a compensated graph state. -/
def CompensatedGraphState.spectralModel {K : Nat}
    (S : CompensatedGraphState K) : SpectralModel :=
  historyPacketGraphSpectralModel
    S.copiedEdges S.edges S.vertices S.packet

/-- The complete integer-time correlator carried by a compensated state. -/
def CompensatedGraphState.corr {K : Nat}
    (S : CompensatedGraphState K) (n : Nat) : Q' :=
  SpectralGap.corr S.spectralModel n

/-- All freshness, incidence, and vertex-avoidance data needed for one
interacting trivalent identity refinement of a state. -/
structure IdentityRefinementMove {K : Nat} (S : CompensatedGraphState K) where
  oldEdge : Nat
  newEdge : Nat
  vacuumEdge : Nat
  old_mem : oldEdge ∈ S.edges
  new_fresh : newEdge ∉ S.edges
  vacuum_fresh : vacuumEdge ∉ S.edges
  new_ne_old : newEdge ≠ oldEdge
  vacuum_ne_old : vacuumEdge ≠ oldEdge
  new_ne_vacuum : newEdge ≠ vacuumEdge
  vertices_avoid_new : VerticesAvoid newEdge S.vertices
  vertices_avoid_vacuum : VerticesAvoid vacuumEdge S.vertices

private theorem old_edges_mem_refined (newEdge vacuumEdge edge : Nat)
    (edges : List Nat) (h : edge ∈ edges) :
    edge ∈ identityRefinedEdges newEdge vacuumEdge edges := by
  exact List.mem_cons_of_mem vacuumEdge
    (List.mem_cons_of_mem newEdge h)

/-- Apply one certified move and add its subdivided edge to the reciprocal
history. -/
def IdentityRefinementMove.next {K : Nat} {S : CompensatedGraphState K}
    (M : IdentityRefinementMove S) : CompensatedGraphState K where
  edges := identityRefinedEdges M.newEdge M.vacuumEdge S.edges
  vertices := identityRefinedVertices
    M.oldEdge M.newEdge M.vacuumEdge S.vertices
  packet := identityRefinedPacket M.newEdge M.vacuumEdge S.packet
  copiedEdges := M.oldEdge :: S.copiedEdges
  copied_mem := by
    intro edge h
    simp only [List.mem_cons] at h
    rcases h with rfl | hrest
    · exact old_edges_mem_refined _ _ _ _ M.old_mem
    · exact old_edges_mem_refined _ _ _ _ (S.copied_mem edge hrest)

/-- One certified compensated move preserves the complete correlator at
every integer time. -/
theorem IdentityRefinementMove.next_corr {K : Nat}
    {S : CompensatedGraphState K} (M : IdentityRefinementMove S) (n : Nat) :
    M.next.corr n ≈ S.corr n := by
  unfold CompensatedGraphState.corr CompensatedGraphState.spectralModel
    IdentityRefinementMove.next
  exact history_packetGraph_corr_identity_refinement S.copiedEdges
    M.oldEdge M.newEdge M.vacuumEdge S.edges S.vertices S.packet n
    M.old_mem M.new_fresh M.vacuum_fresh M.new_ne_old M.vacuum_ne_old
    M.new_ne_vacuum M.vertices_avoid_new M.vertices_avoid_vacuum
    S.copied_mem

/-- A typed finite path generated solely by certified compensated identity
refinements. -/
inductive CompensatedRefinementPath {K : Nat} :
    CompensatedGraphState K → CompensatedGraphState K → Prop
  | refl (S : CompensatedGraphState K) : CompensatedRefinementPath S S
  | step {S T : CompensatedGraphState K}
      (M : IdentityRefinementMove S)
      (tail : CompensatedRefinementPath M.next T) :
      CompensatedRefinementPath S T

/-- The terminal correlator of every certified finite refinement path is
exactly the initial correlator. -/
theorem CompensatedRefinementPath.corr_invariant {K : Nat}
    {S T : CompensatedGraphState K}
    (path : CompensatedRefinementPath S T) (n : Nat) :
    T.corr n ≈ S.corr n := by
  induction path with
  | refl S => exact Q'.eqv_refl _
  | step M tail ih =>
      exact Q'.eqv_trans _ _ _ ih (M.next_corr n)

/-- Concatenation of certified finite refinement paths. -/
theorem CompensatedRefinementPath.trans {K : Nat}
    {S T U : CompensatedGraphState K}
    (left : CompensatedRefinementPath S T)
    (right : CompensatedRefinementPath T U) :
    CompensatedRefinementPath S U := by
  induction left with
  | refl _ => exact right
  | step M tail ih => exact .step M (ih right)

/-- Correlator invariance respects path concatenation without an additional
normalization or coherence defect. -/
theorem CompensatedRefinementPath.trans_corr {K : Nat}
    {S T U : CompensatedGraphState K}
    (left : CompensatedRefinementPath S T)
    (right : CompensatedRefinementPath T U) (n : Nat) :
    U.corr n ≈ S.corr n :=
  (left.trans right).corr_invariant n

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath.IdentityRefinementMove.next_corr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath.CompensatedRefinementPath.corr_invariant
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath.CompensatedRefinementPath.trans_corr
