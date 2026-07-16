/-
# Actual-link Cartesian transport to the canonical resolver

The generic identifier and finite-Fubini theorems are instantiated here on
one physical link of the finite box.  Canonical coordinates consist of the
physical range followed by the same eight-coordinate reserved block as the
production geometry.  Coordinates used as internal channels carry the exact
all-ones packet; the terminator and unused reserved coordinates carry the
normalized vacuum packet, so adjoining the full reserved block creates no
multiplicity.

The resulting theorem identifies the literal Cartesian graph sum on the
actual plaquette and reserved identifiers with the canonical consecutive-
identifier sum.  All statements use the enlarged `6*K` fusion-complete
window and the real `linkResolutionVertices` syntax.

Honest scope: the actual/canonical reindexing is closed.  The remaining local
frontier is the canonical `fuseChain` sum versus the left-associated explicit
kernel.
-/

import YMGap.Continuum.Z4GraphIdentifierCartesianTransport
import YMGap.Continuum.Z4LeftAssociatedExplicitKernel

namespace YMGap.Continuum.Z4CanonicalLinkCartesianTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4GraphIdentifierCartesianTransport
open YMGap.Continuum.Z4LinkIdentifierFreshness

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical and transported packet families -/

/-- Packet family on canonical consecutive identifiers.  The condition
`offset + 3 ≤ degree` is exactly the condition that the corresponding
auxiliary coordinate occurs in `fuseLabels`. -/
def canonicalLinkGraphPacket {K : Nat} (P : CharacterPacket K)
    (degree : Nat) : Nat → CharacterPacket (linkAuxiliaryCutoff K) :=
  fun edge =>
    if edge < degree then facePacketAtLinkCutoff P
    else
      let offset := edge - degree
      if offset = 0 then vacuumPacket (linkAuxiliaryCutoff K)
      else if offset + 3 ≤ degree then
        allOnesPacket (linkAuxiliaryCutoff K)
      else vacuumPacket (linkAuxiliaryCutoff K)

/-- The same packet convention on arbitrary actual physical identifiers and
a consecutive reserved block. -/
def transportedActualLinkPacket {K : Nat} (P : CharacterPacket K)
    (physicalCount : Nat) (labels : List Nat) (base : Nat) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K) :=
  fun edge =>
    if edge < physicalCount then facePacketAtLinkCutoff P
    else
      let offset := edge - base
      if offset = 0 then vacuumPacket (linkAuxiliaryCutoff K)
      else if offset + 3 ≤ labels.length then
        allOnesPacket (linkAuxiliaryCutoff K)
      else vacuumPacket (linkAuxiliaryCutoff K)

/-- Packet values agree on every coordinate of the canonical-to-actual
renaming. -/
theorem transportedActualLinkPacket_rename_eq {K : Nat}
    (P : CharacterPacket K) (physicalCount : Nat)
    (labels : List Nat) (base edge : Nat)
    (hphysical : ∀ e, e ∈ labels → e < physicalCount)
    (hbase : physicalCount ≤ base)
    (hedge : edge ∈ canonicalLocalCoordinates labels.length) :
    transportedActualLinkPacket P physicalCount labels base
        (localIdentifierRename labels base edge) =
      canonicalLinkGraphPacket P labels.length edge := by
  unfold canonicalLocalCoordinates at hedge
  rcases List.mem_append.mp hedge with hphysicalEdge | hblockEdge
  · have hedgeLt : edge < labels.length := List.mem_range.mp hphysicalEdge
    have hmapped : localIdentifierRename labels base edge ∈ labels := by
      have hmappedInRange :
          localIdentifierRename labels base edge ∈
            (List.range labels.length).map
              (localIdentifierRename labels base) :=
        List.mem_map.mpr ⟨edge, hphysicalEdge, rfl⟩
      rw [map_localIdentifierRename_range labels base] at hmappedInRange
      exact hmappedInRange
    have hactualLt := hphysical _ hmapped
    unfold transportedActualLinkPacket canonicalLinkGraphPacket
    rw [if_pos hactualLt, if_pos hedgeLt]
  · obtain ⟨j, hj, hedgeEq⟩ := List.mem_map.mp hblockEdge
    rw [← hedgeEq]
    have hrename :
        localIdentifierRename labels base (labels.length + j) = base + j :=
      localIdentifierRename_length_add labels base j
    have hactualNotPhysical : ¬ base + j < physicalCount := by omega
    have hcanonicalNotPhysical : ¬ labels.length + j < labels.length := by
      omega
    unfold transportedActualLinkPacket canonicalLinkGraphPacket
    rw [hrename, if_neg hactualNotPhysical, if_neg hcanonicalNotPhysical]
    simp only [Nat.add_sub_cancel_left]

/-! ## 2. Coverage of the canonical resolver -/

theorem canonicalFuseLabels_verticesCovered {degree : Nat}
    (hdegree : degree ≤ linkIncidenceBound) :
    VerticesCoveredBy (canonicalLocalCoordinates degree)
      (fuseLabels degree (degree + 1) (List.range degree)) := by
  intro v hv edge hedge
  obtain hvac | hphysical | ⟨j, hedgeEq, hj⟩ :=
    fuseLabels_vertex_edge_classify degree (degree + 1)
      (List.range degree) v edge hv hedge
  · subst edge
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), by simp⟩
  · exact List.mem_append_left _ hphysical
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨j + 1, List.mem_range.mpr ?_, ?_⟩
    · unfold linkIncidenceBound at hdegree
      simp only [List.length_range] at hj
      omega
    · omega

/-! ## 3. The actual and canonical vertex-Cartesian sums -/

def canonicalLinkVertexCartesianSum {K : Nat} (P : CharacterPacket K)
    (degree : Nat) : Q' :=
  listQSum
    (graphVertexProject
      (fuseLabels degree (degree + 1) (List.range degree))
      (packetGraphBareAmplitude (canonicalLocalCoordinates degree)
        (canonicalLinkGraphPacket P degree)))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (canonicalLocalCoordinates degree))

def actualLinkVertexCartesianSum {K : Nat} (P : CharacterPacket K)
    (n i : Nat) (ell : Z4Link) : Q' :=
  let labels := incidentPlaqIds n ell
  listQSum
    (graphVertexProject (linkResolutionVertices n i ell)
      (packetGraphBareAmplitude
        (labels ++ linkBlockEdges n i)
        (transportedActualLinkPacket P (plaquetteEdgeCount n)
          labels (linkBlockBase n i))))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (labels ++ linkBlockEdges n i))

/-- **Actual-link Cartesian identifier transport.** -/
theorem actualLinkVertexCartesianSum_eq_canonical {K : Nat}
    (P : CharacterPacket K) (n i : Nat) (ell : Z4Link) :
    actualLinkVertexCartesianSum P n i ell ≈
      canonicalLinkVertexCartesianSum P (incidentPlaqIds n ell).length := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let f := localIdentifierRename labels base
  let edges := canonicalLocalCoordinates degree
  let vertices := fuseLabels degree (degree + 1) (List.range degree)
  have himageNodup : (edges.map f).Nodup := by
    dsimp [edges, f, degree, labels, base]
    exact renamed_canonicalLocalCoordinates_nodup n i ell
  have hinj : InjectiveOnList f edges :=
    injectiveOnList_of_map_nodup f edges himageNodup
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  have hcover : VerticesCoveredBy edges vertices := by
    dsimp [edges, vertices]
    exact canonicalFuseLabels_verticesCovered hdegree
  have hpacket : ∀ edge, edge ∈ edges →
      transportedActualLinkPacket P (plaquetteEdgeCount n) labels base
          (f edge) = canonicalLinkGraphPacket P degree edge := by
    intro edge hedge
    apply transportedActualLinkPacket_rename_eq
    · intro e he
      exact incidentPlaqId_lt_count he
    · exact linkBlockBase_ge_count n i
    · exact hedge
  have htransport := vertexCartesianSum_rename
    (K := linkAuxiliaryCutoff K) f edges vertices
    (canonicalLinkGraphPacket P degree)
    (transportedActualLinkPacket P (plaquetteEdgeCount n) labels base)
    hinj hcover hpacket
  have hedges : edges.map f = labels ++ linkBlockEdges n i := by
    dsimp [edges, f, degree, labels, base]
    exact map_canonicalLocalCoordinates_actual n i ell
  have hvertices : vertices.map (mapTrivalentVertex f) =
      linkResolutionVertices n i ell := by
    dsimp [vertices, f, degree, labels, base]
    exact canonical_linkResolutionVertices_map n i ell
  rw [hedges, hvertices] at htransport
  exact htransport

end YMGap.Continuum.Z4CanonicalLinkCartesianTransport

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalLinkCartesianTransport.transportedActualLinkPacket_rename_eq
#print axioms YMGap.Continuum.Z4CanonicalLinkCartesianTransport.canonicalFuseLabels_verticesCovered
#print axioms YMGap.Continuum.Z4CanonicalLinkCartesianTransport.actualLinkVertexCartesianSum_eq_canonical
