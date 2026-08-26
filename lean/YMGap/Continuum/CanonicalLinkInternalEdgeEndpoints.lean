/-
# Exact endpoints of canonical internal fusion edges

For a canonical left-fusion chain, internal identifier `edge` joins the two
consecutive vertex positions

    edge - (degree + 1),  edge - (degree + 1) + 1.

This module proves that formula for actual proof-indexed half-edges and then
deduces that same-slot continuation crosses between adjacent vertices.  It is
the arithmetic path certificate needed to turn nonbacktracking into bounded
termination.

Constructive contract: the literal degree-four, degree-five, and degree-six
chains only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkStrandPathTopology

namespace YMGap.Continuum.CanonicalLinkInternalEdgeEndpoints

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalHalfEdgeSwap
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkStrandPathTopology
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-- The zero-based left endpoint of a canonical internal identifier. -/
def canonicalInternalEdgeLeftIndex (degree edge : Nat) : Nat :=
  edge - (degree + 1)

private theorem halfEdgeIndex_lt_vertexCount
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (halfEdge : ResolvedNetworkHalfEdge
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    halfEdge.vertexIndex.val < (canonicalLinkVertices degree).length := by
  have hbound := halfEdge.vertexIndex.isLt
  exact Eq.mp
    (congrArg (fun length => halfEdge.vertexIndex.val < length)
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed).length_eq)
    hbound

/-- Every actual half-edge over an internal identifier lies at one of its two
displayed consecutive endpoint positions. -/
theorem canonicalInternalHalfEdge_vertexIndex_endpoints
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (halfEdge : CanonicalInternalHalfEdge edge external auxiliary hallowed) :
    halfEdge.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree edge ∨
      halfEdge.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree edge + 1 := by
  have hedgeId : halfEdge.1.edgeId = edge :=
    (mem_halfEdgesOnEdge_iff _ _).mp halfEdge.2
  unfold ResolvedNetworkHalfEdge.edgeId
    ResolvedNetworkHalfEdge.vertex at hedgeId
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
    have hbound := halfEdgeIndex_lt_vertexCount halfEdge.1
    change halfEdge.1.vertexIndex.val < 2 at hbound
    unfold canonicalInternalEdgeLeftIndex
    omega
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
    rcases hedge with rfl | rfl
    · have hbound := halfEdgeIndex_lt_vertexCount halfEdge.1
      change halfEdge.1.vertexIndex.val < 3 at hbound
      have hindex : halfEdge.1.vertexIndex.val = 0 ∨
          halfEdge.1.vertexIndex.val = 1 ∨
          halfEdge.1.vertexIndex.val = 2 := by omega
      rcases hindex with hzero | hone | htwo
      · exact Or.inl (by
          unfold canonicalInternalEdgeLeftIndex
          omega)
      · exact Or.inr (by
          unfold canonicalInternalEdgeLeftIndex
          omega)
      · have hfin : halfEdge.1.vertexIndex = ⟨2, by omega⟩ :=
          Fin.ext htwo
        rw [hfin] at hedgeId
        change vertexEdgeId (7, 3, 4) halfEdge.1.leg = 6 at hedgeId
        cases hleg : halfEdge.1.leg <;>
          simp [hleg, vertexEdgeId] at hedgeId
    · have hbound := halfEdgeIndex_lt_vertexCount halfEdge.1
      change halfEdge.1.vertexIndex.val < 3 at hbound
      have hindex : halfEdge.1.vertexIndex.val = 0 ∨
          halfEdge.1.vertexIndex.val = 1 ∨
          halfEdge.1.vertexIndex.val = 2 := by omega
      rcases hindex with hzero | hone | htwo
      · have hfin : halfEdge.1.vertexIndex = ⟨0, by omega⟩ :=
          Fin.ext hzero
        rw [hfin] at hedgeId
        change vertexEdgeId (0, 1, 6) halfEdge.1.leg = 7 at hedgeId
        cases hleg : halfEdge.1.leg <;>
          simp [hleg, vertexEdgeId] at hedgeId
      · exact Or.inl (by
          unfold canonicalInternalEdgeLeftIndex
          omega)
      · exact Or.inr (by
          unfold canonicalInternalEdgeLeftIndex
          omega)
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
    rcases hedge with rfl | rfl | rfl
    · have hbound := halfEdgeIndex_lt_vertexCount halfEdge.1
      change halfEdge.1.vertexIndex.val < 4 at hbound
      have hindex : halfEdge.1.vertexIndex.val = 0 ∨
          halfEdge.1.vertexIndex.val = 1 ∨
          halfEdge.1.vertexIndex.val = 2 ∨
          halfEdge.1.vertexIndex.val = 3 := by omega
      rcases hindex with hzero | hone | htwo | hthree
      · exact Or.inl (by
          unfold canonicalInternalEdgeLeftIndex
          omega)
      · exact Or.inr (by
          unfold canonicalInternalEdgeLeftIndex
          omega)
      · have hfin : halfEdge.1.vertexIndex = ⟨2, by omega⟩ :=
          Fin.ext htwo
        rw [hfin] at hedgeId
        change vertexEdgeId (8, 3, 9) halfEdge.1.leg = 7 at hedgeId
        cases hleg : halfEdge.1.leg <;>
          simp [hleg, vertexEdgeId] at hedgeId
      · have hfin : halfEdge.1.vertexIndex = ⟨3, by omega⟩ :=
          Fin.ext hthree
        rw [hfin] at hedgeId
        change vertexEdgeId (9, 4, 5) halfEdge.1.leg = 7 at hedgeId
        cases hleg : halfEdge.1.leg <;>
          simp [hleg, vertexEdgeId] at hedgeId
    · have hbound := halfEdgeIndex_lt_vertexCount halfEdge.1
      change halfEdge.1.vertexIndex.val < 4 at hbound
      have hindex : halfEdge.1.vertexIndex.val = 0 ∨
          halfEdge.1.vertexIndex.val = 1 ∨
          halfEdge.1.vertexIndex.val = 2 ∨
          halfEdge.1.vertexIndex.val = 3 := by omega
      rcases hindex with hzero | hone | htwo | hthree
      · have hfin : halfEdge.1.vertexIndex = ⟨0, by omega⟩ :=
          Fin.ext hzero
        rw [hfin] at hedgeId
        change vertexEdgeId (0, 1, 7) halfEdge.1.leg = 8 at hedgeId
        cases hleg : halfEdge.1.leg <;>
          simp [hleg, vertexEdgeId] at hedgeId
      · exact Or.inl (by
          unfold canonicalInternalEdgeLeftIndex
          omega)
      · exact Or.inr (by
          unfold canonicalInternalEdgeLeftIndex
          omega)
      · have hfin : halfEdge.1.vertexIndex = ⟨3, by omega⟩ :=
          Fin.ext hthree
        rw [hfin] at hedgeId
        change vertexEdgeId (9, 4, 5) halfEdge.1.leg = 8 at hedgeId
        cases hleg : halfEdge.1.leg <;>
          simp [hleg, vertexEdgeId] at hedgeId
    · have hbound := halfEdgeIndex_lt_vertexCount halfEdge.1
      change halfEdge.1.vertexIndex.val < 4 at hbound
      have hindex : halfEdge.1.vertexIndex.val = 0 ∨
          halfEdge.1.vertexIndex.val = 1 ∨
          halfEdge.1.vertexIndex.val = 2 ∨
          halfEdge.1.vertexIndex.val = 3 := by omega
      rcases hindex with hzero | hone | htwo | hthree
      · have hfin : halfEdge.1.vertexIndex = ⟨0, by omega⟩ :=
          Fin.ext hzero
        rw [hfin] at hedgeId
        change vertexEdgeId (0, 1, 7) halfEdge.1.leg = 9 at hedgeId
        cases hleg : halfEdge.1.leg <;>
          simp [hleg, vertexEdgeId] at hedgeId
      · have hfin : halfEdge.1.vertexIndex = ⟨1, by omega⟩ :=
          Fin.ext hone
        rw [hfin] at hedgeId
        change vertexEdgeId (7, 2, 8) halfEdge.1.leg = 9 at hedgeId
        cases hleg : halfEdge.1.leg <;>
          simp [hleg, vertexEdgeId] at hedgeId
      · exact Or.inl (by
          unfold canonicalInternalEdgeLeftIndex
          omega)
      · exact Or.inr (by
          unfold canonicalInternalEdgeLeftIndex
          omega)

/-- Same-slot continuation across an internal identifier moves between
adjacent vertex positions. -/
theorem canonicalInternalStrandContinue_vertexIndex_adjacent
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
    crossed.1.vertexIndex.val + 1 = occurrence.1.vertexIndex.val ∨
      occurrence.1.vertexIndex.val + 1 = crossed.1.vertexIndex.val := by
  dsimp only
  have hsource := canonicalInternalHalfEdge_vertexIndex_endpoints
    hdegree hallowed hedge (canonicalInternalStrandHalfEdge occurrence)
  change occurrence.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree edge ∨
      occurrence.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree edge + 1 at hsource
  have htarget := canonicalInternalHalfEdge_vertexIndex_endpoints
    hdegree hallowed hedge
      (canonicalInternalStrandHalfEdge
        (canonicalInternalStrandContinue
          hdegree hallowed hedge occurrence))
  change
    (canonicalInternalStrandContinue
        hdegree hallowed hedge occurrence).1.vertexIndex.val =
          canonicalInternalEdgeLeftIndex degree edge ∨
      (canonicalInternalStrandContinue
        hdegree hallowed hedge occurrence).1.vertexIndex.val =
          canonicalInternalEdgeLeftIndex degree edge + 1 at htarget
  have hne := canonicalInternalStrandContinue_vertexIndex_ne
    hdegree hallowed hedge occurrence
  have hneVal :
      (canonicalInternalStrandContinue
        hdegree hallowed hedge occurrence).1.vertexIndex.val ≠
      occurrence.1.vertexIndex.val := by
    intro heq
    apply hne
    exact Fin.ext heq
  rcases hsource with hsource | hsource <;>
    rcases htarget with htarget | htarget <;> omega

#print axioms canonicalInternalEdgeLeftIndex
#print axioms canonicalInternalHalfEdge_vertexIndex_endpoints
#print axioms canonicalInternalStrandContinue_vertexIndex_adjacent

end YMGap.Continuum.CanonicalLinkInternalEdgeEndpoints
