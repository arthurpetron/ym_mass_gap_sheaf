/-
# Nonbacktracking topology of one canonical link-strand advance

The canonical left-fusion graph is a finite path.  The key local fact behind
termination is not a numerical computation: at one canonical vertex, a
genuine internal edge occupies a unique leg.  Therefore crossing an internal
edge reaches a different vertex, and the following local trivalent mate
cannot select the same internal edge again.

This module proves precisely that nonbacktracking invariant for the actual
proof-indexed resolved network.  The next module can consume it to contract a
bounded walk to a physical terminal.

Constructive contract: the seven geometric valence cases and explicit
trivalent legs only.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkStrandStep

namespace YMGap.Continuum.CanonicalLinkStrandPathTopology

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Internal identifiers occupy unique legs at each path vertex -/

/-- At a canonical left-fusion vertex, a genuine internal edge identifier
cannot occur on two different legs.  This is the exact local path-topology
fact; the only repeated coordinate in the low-valence syntax is a vacuum
terminator, never an internal edge. -/
theorem canonicalVertex_internal_leg_injective
    {degree edge : Nat} (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    {vertex : TrivalentVertex}
    (hvertex : vertex ∈ canonicalLinkVertices degree)
    {left right : TrivalentLeg}
    (hleft : vertexEdgeId vertex left = edge)
    (hright : vertexEdgeId vertex right = edge) :
    left = right := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
    subst edge
    change vertex ∈ [(0, 1, 5), (5, 2, 3)] at hvertex
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvertex
    rcases hvertex with rfl | rfl
    all_goals
      cases left <;> cases right <;>
        simp_all [vertexEdgeId]
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
    rcases hedge with rfl | rfl
    all_goals
      change vertex ∈ [(0, 1, 6), (6, 2, 7), (7, 3, 4)] at hvertex
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvertex
      rcases hvertex with rfl | rfl | rfl
      all_goals
        cases left <;> cases right <;>
          simp_all [vertexEdgeId]
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
    rcases hedge with rfl | rfl | rfl
    all_goals
      change vertex ∈
        [(0, 1, 7), (7, 2, 8), (8, 3, 9), (9, 4, 5)] at hvertex
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvertex
      rcases hvertex with rfl | rfl | rfl | rfl
      all_goals
        cases left <;> cases right <;>
          simp_all [vertexEdgeId]

/-! ## 2. Same-slot crossing changes the path vertex -/

/-- Transport across a genuine internal edge reaches the other vertex of the
path, never another leg at the same vertex. -/
theorem canonicalInternalStrandContinue_vertexIndex_ne
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence :
      CanonicalInternalStrandPort edge external auxiliary hallowed) :
    (canonicalInternalStrandContinue
        hdegree hallowed hedge occurrence).1.vertexIndex ≠
      occurrence.1.vertexIndex := by
  let crossed := canonicalInternalStrandContinue
    hdegree hallowed hedge occurrence
  change crossed.1.vertexIndex ≠ occurrence.1.vertexIndex
  intro hindex
  have hvertexEq : crossed.1.vertex = occurrence.1.vertex := by
    unfold ResolvedNetworkPort.vertex
    rw [hindex]
  have hcrossedEdge : vertexEdgeId occurrence.1.vertex crossed.1.leg = edge := by
    have hedgeEq := crossed.2
    unfold ResolvedNetworkPort.edgeId at hedgeEq
    rw [hvertexEq] at hedgeEq
    exact hedgeEq
  have hsourceEdge : vertexEdgeId occurrence.1.vertex occurrence.1.leg =
      edge := occurrence.2
  have hleg : crossed.1.leg = occurrence.1.leg :=
    canonicalVertex_internal_leg_injective hdegree hedge
      (resolvedNetworkPort_vertex_mem occurrence.1)
      hcrossedEdge hsourceEdge
  have hport : crossed.1 = occurrence.1 := by
    apply resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq
    · unfold resolvedNetworkPortHalfEdge
      congr
    · exact canonicalInternalStrandContinue_slot
        hdegree hallowed hedge occurrence
  apply canonicalInternalStrandContinue_ne_self
    hdegree hallowed hedge occurrence
  exact Subtype.ext hport

/-! ## 3. The local mate forbids immediate edge backtracking -/

/-- At a port on a genuine internal edge, the local trivalent mate cannot
remain on that same edge identifier. -/
theorem localMate_edgeId_ne_of_internal
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hedge : occurrence.edgeId ∈ canonicalInternalFusionEdges degree) :
    occurrence.localMate.edgeId ≠ occurrence.edgeId := by
  intro hedgeEq
  have hleg : occurrence.localMate.leg = occurrence.leg :=
    canonicalVertex_internal_leg_injective hdegree hedge
      (resolvedNetworkPort_vertex_mem occurrence)
      hedgeEq rfl
  exact occurrence.localMate_leg_ne hleg

/-- One internal branch of the total dynamics changes vertex and then leaves
the crossed edge.  This is the nonbacktracking invariant consumed by finite
path contraction. -/
theorem canonicalInternalAdvance_nonbacktracking
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence :
      CanonicalInternalStrandPort edge external auxiliary hallowed) :
    let crossed := canonicalInternalStrandContinue
      hdegree hallowed hedge occurrence
    crossed.1.vertexIndex ≠ occurrence.1.vertexIndex ∧
      crossed.1.localMate.vertexIndex = crossed.1.vertexIndex ∧
      crossed.1.localMate.edgeId ≠ edge := by
  dsimp only
  refine ⟨canonicalInternalStrandContinue_vertexIndex_ne
      hdegree hallowed hedge occurrence,
    ResolvedNetworkPort.localMate_vertexIndex _, ?_⟩
  have hne := localMate_edgeId_ne_of_internal
    hdegree hallowed
    (canonicalInternalStrandContinue
      hdegree hallowed hedge occurrence).1
    (by
      rw [(canonicalInternalStrandContinue
        hdegree hallowed hedge occurrence).2]
      exact hedge)
  exact fun heq => hne (heq.trans
    (canonicalInternalStrandContinue
      hdegree hallowed hedge occurrence).2.symm)

#print axioms canonicalVertex_internal_leg_injective
#print axioms canonicalInternalStrandContinue_vertexIndex_ne
#print axioms localMate_edgeId_ne_of_internal
#print axioms canonicalInternalAdvance_nonbacktracking

end YMGap.Continuum.CanonicalLinkStrandPathTopology
