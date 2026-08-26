/-
# Strict progress of successive canonical strand advances

The abstract monotone-path rank now meets the actual proof-indexed strand
dynamics.  If a second internal crossing returned to the vertex preceding the
first crossing, the two distinct internal identifiers would have the same two
consecutive endpoints.  Endpoint-pair uniqueness and faithfulness of the
canonical identifier coordinate rule this out.

Consequently every pair of successive internal advances strictly decreases
the explicit end-distance rank.  This is the canonical well-foundedness
certificate consumed by the terminal extractor.

Constructive contract: equality transport between actual dependent ports and
the already-proved natural path lemmas only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkStrandMonotonePath

namespace YMGap.Continuum.CanonicalLinkStrandStrictProgress

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalEdgeEndpoints
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkStrandMonotonePath
open YMGap.Continuum.CanonicalLinkStrandPathTopology
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

/-! ## 1. Every actual port has a bounded path coordinate -/

/-- The proof-indexed vertex coordinate of every canonical resolved port is
strictly below the number of vertices in the displayed fusion path. -/
theorem canonicalResolvedPort_vertexIndex_lt_vertexCount
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    occurrence.vertexIndex.val < (canonicalLinkVertices degree).length := by
  have hbound := occurrence.vertexIndex.isLt
  exact Eq.mp
    (congrArg (fun length => occurrence.vertexIndex.val < length)
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed).length_eq)
    hbound

/-! ## 2. Two internal advances cannot return to the preceding vertex -/

/-- Two successive canonical internal crossings cannot return to the vertex
preceding the first crossing.  Such a return would make their two distinct
edge identifiers share the same consecutive endpoint pair. -/
theorem canonicalSuccessiveInternalCrossing_no_return
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence :
      CanonicalInternalStrandPort edge external auxiliary hallowed)
    (hnextInternal :
      (canonicalInternalStrandContinue
        hdegree hallowed hedge occurrence).1.localMate.edgeId ∈
          canonicalInternalFusionEdges degree) :
    let firstCrossed := canonicalInternalStrandContinue
      hdegree hallowed hedge occurrence
    let nextSource : CanonicalInternalStrandPort
        firstCrossed.1.localMate.edgeId external auxiliary hallowed :=
      ⟨firstCrossed.1.localMate, rfl⟩
    let secondCrossed := canonicalInternalStrandContinue
      hdegree hallowed hnextInternal nextSource
    secondCrossed.1.vertexIndex ≠ occurrence.1.vertexIndex := by
  dsimp only
  let firstCrossed := canonicalInternalStrandContinue
    hdegree hallowed hedge occurrence
  let current := firstCrossed.1.localMate
  let nextSource : CanonicalInternalStrandPort
      current.edgeId external auxiliary hallowed := ⟨current, rfl⟩
  let secondCrossed := canonicalInternalStrandContinue
    hdegree hallowed hnextInternal nextSource
  change secondCrossed.1.vertexIndex ≠ occurrence.1.vertexIndex
  intro hreturn

  have hfirstNe := canonicalInternalStrandContinue_vertexIndex_ne
    hdegree hallowed hedge occurrence
  have hdistinct : occurrence.1.vertexIndex.val ≠
      firstCrossed.1.vertexIndex.val := by
    intro heq
    exact hfirstNe (Fin.ext heq.symm)

  have hsource₁ := canonicalInternalHalfEdge_vertexIndex_endpoints
    hdegree hallowed hedge (canonicalInternalStrandHalfEdge occurrence)
  change occurrence.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree edge ∨
      occurrence.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree edge + 1 at hsource₁

  have htarget₁ := canonicalInternalHalfEdge_vertexIndex_endpoints
    hdegree hallowed hedge
      (canonicalInternalStrandHalfEdge firstCrossed)
  change firstCrossed.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree edge ∨
      firstCrossed.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree edge + 1 at htarget₁

  have hsource₂ := canonicalInternalHalfEdge_vertexIndex_endpoints
    hdegree hallowed hnextInternal
      (canonicalInternalStrandHalfEdge nextSource)
  change current.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree current.edgeId ∨
      current.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree current.edgeId + 1 at hsource₂
  have hcurrentVertex : current.vertexIndex =
      firstCrossed.1.vertexIndex :=
    ResolvedNetworkPort.localMate_vertexIndex firstCrossed.1
  rw [hcurrentVertex] at hsource₂

  have htarget₂ := canonicalInternalHalfEdge_vertexIndex_endpoints
    hdegree hallowed hnextInternal
      (canonicalInternalStrandHalfEdge secondCrossed)
  change secondCrossed.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree current.edgeId ∨
      secondCrossed.1.vertexIndex.val =
        canonicalInternalEdgeLeftIndex degree current.edgeId + 1 at htarget₂
  rw [hreturn] at htarget₂

  have hleft := consecutiveEndpointPair_leftIndex_unique hdistinct
    hsource₁ htarget₁ htarget₂ hsource₂
  have hedgeEq : edge = current.edgeId :=
    canonicalInternalEdgeLeftIndex_injective
      hdegree hedge hnextInternal hleft
  have hedgeNe : current.edgeId ≠ edge :=
    (canonicalInternalAdvance_nonbacktracking
      hdegree hallowed hedge occurrence).2.2
  exact hedgeNe hedgeEq.symm

/-! ## 3. The actual canonical rank decreases -/

/-- Two successive internal strand crossings strictly decrease the abstract
end-distance rank on the actual canonical fusion path. -/
theorem canonicalSuccessiveInternalCrossing_rank_decreases
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence :
      CanonicalInternalStrandPort edge external auxiliary hallowed)
    (hnextInternal :
      (canonicalInternalStrandContinue
        hdegree hallowed hedge occurrence).1.localMate.edgeId ∈
          canonicalInternalFusionEdges degree) :
    let firstCrossed := canonicalInternalStrandContinue
      hdegree hallowed hedge occurrence
    let nextSource : CanonicalInternalStrandPort
        firstCrossed.1.localMate.edgeId external auxiliary hallowed :=
      ⟨firstCrossed.1.localMate, rfl⟩
    let secondCrossed := canonicalInternalStrandContinue
      hdegree hallowed hnextInternal nextSource
    natPathRank (canonicalLinkVertices degree).length
        firstCrossed.1.vertexIndex.val secondCrossed.1.vertexIndex.val <
      natPathRank (canonicalLinkVertices degree).length
        occurrence.1.vertexIndex.val firstCrossed.1.vertexIndex.val := by
  dsimp only
  let firstCrossed := canonicalInternalStrandContinue
    hdegree hallowed hedge occurrence
  let current := firstCrossed.1.localMate
  let nextSource : CanonicalInternalStrandPort
      current.edgeId external auxiliary hallowed := ⟨current, rfl⟩
  let secondCrossed := canonicalInternalStrandContinue
    hdegree hallowed hnextInternal nextSource
  change natPathRank (canonicalLinkVertices degree).length
        firstCrossed.1.vertexIndex.val secondCrossed.1.vertexIndex.val <
      natPathRank (canonicalLinkVertices degree).length
        occurrence.1.vertexIndex.val firstCrossed.1.vertexIndex.val
  apply natPathRank_strictly_decreases
  · have hadjacent := canonicalInternalStrandContinue_vertexIndex_adjacent
      hdegree hallowed hedge occurrence
    change firstCrossed.1.vertexIndex.val + 1 =
          occurrence.1.vertexIndex.val ∨
        occurrence.1.vertexIndex.val + 1 =
          firstCrossed.1.vertexIndex.val at hadjacent
    unfold NatPathAdjacent
    exact hadjacent.symm
  · have hadjacent := canonicalInternalStrandContinue_vertexIndex_adjacent
      hdegree hallowed hnextInternal nextSource
    change secondCrossed.1.vertexIndex.val + 1 = current.vertexIndex.val ∨
        current.vertexIndex.val + 1 = secondCrossed.1.vertexIndex.val at hadjacent
    have hcurrentVertex : current.vertexIndex =
        firstCrossed.1.vertexIndex :=
      ResolvedNetworkPort.localMate_vertexIndex firstCrossed.1
    unfold NatPathAdjacent
    rw [hcurrentVertex] at hadjacent
    exact hadjacent.symm
  · have hnoReturn := canonicalSuccessiveInternalCrossing_no_return
      hdegree hallowed hedge occurrence hnextInternal
    intro heq
    exact hnoReturn (Fin.ext heq)
  · exact canonicalResolvedPort_vertexIndex_lt_vertexCount secondCrossed.1

#print axioms canonicalResolvedPort_vertexIndex_lt_vertexCount
#print axioms canonicalSuccessiveInternalCrossing_no_return
#print axioms canonicalSuccessiveInternalCrossing_rank_decreases

end YMGap.Continuum.CanonicalLinkStrandStrictProgress
