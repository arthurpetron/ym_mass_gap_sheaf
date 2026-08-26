/-
# One total strand step in an accepted canonical link network

Every typed port in the canonical resolved chain is either a physical
terminal or lies on a genuine internal fusion edge; the vacuum terminator
cannot carry a bounded port.  This module packages that exhaustive statement
as data and immediately consumes it: physical ports stop, while internal
ports cross by the same-slot continuation and then take their local
trivalent mate.

This is the one-step dynamics for the forthcoming nonbacktracking path
contraction.  It is not merely another edge classification.

Constructive contract: Boolean/decidable case splits on explicit finite
coordinates only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkInternalStrandContinuation
import YMGap.Continuum.Z4ActualLinkUsedPacketBridge

namespace YMGap.Continuum.CanonicalLinkStrandStep

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.Z4ActualLinkUsedPacketBridge
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Every dependent port lies on an original graph vertex -/

/-- The vertex selected from a resolved network still belongs to the exact
original ordered vertex list. -/
theorem resolvedNetworkPort_vertex_mem
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    occurrence.vertex ∈ vertices := by
  let selected := resolvedVertexAt network occurrence.vertexIndex
  have hresolved : selected ∈ network.resolved :=
    List.get_mem network.resolved occurrence.vertexIndex
  have hmapped : selected.vertex ∈
      network.resolved.map (fun resolved => resolved.vertex) :=
    List.mem_map.mpr ⟨selected, hresolved, rfl⟩
  exact Eq.mp
    (congrArg (fun entries => selected.vertex ∈ entries)
      network.vertices_exact)
    hmapped

/-- A port's edge identifier is one of the three identifiers of its selected
vertex. -/
theorem resolvedNetworkPort_vertexContains
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    VertexContains occurrence.edgeId occurrence.vertex := by
  cases occurrence with
  | mk index port =>
      cases port <;>
        simp [ResolvedNetworkPort.edgeId, ResolvedNetworkPort.vertex,
          ResolvedNetworkPort.leg, vertexEdgeId,
          TrivalentStrandPort.leg, VertexContains]

/-- Hence every port in the canonical resolved network lies over a coordinate
actually read by the production chain. -/
theorem canonicalResolvedPort_edge_mem_used
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    occurrence.edgeId ∈ canonicalUsedCoordinates degree :=
  canonicalUsed_verticesCovered hdegree occurrence.vertex
    (resolvedNetworkPort_vertex_mem occurrence) occurrence.edgeId
    (resolvedNetworkPort_vertexContains occurrence)

/-! ## 2. Total physical/internal classification -/

/-- A genuine internal fusion identifier cannot be physical. -/
theorem canonicalInternalFusionEdge_not_lt
    {degree edge : Nat} (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalInternalFusionEdges degree) :
    ¬ edge < degree := by
  have hauxiliary : edge ∈ canonicalUsedAuxiliaryCoordinates degree :=
    (List.mem_filter.mp hedge).1
  obtain ⟨offset, hedgeEq, _⟩ :=
    canonicalUsedAuxiliary_coordinate_shape hdegree hauxiliary
  omega

/-- The two possible locations of an actual typed canonical-link port. -/
inductive CanonicalResolvedPortClass
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) : Type
  | physical (hedge : occurrence.edgeId < degree)
  | internal (hedge : occurrence.edgeId ∈
      canonicalInternalFusionEdges degree)

/-- Constructively classify every actual port.  The impossible third case is
the used vacuum terminator, whose accepted label is zero and hence has no
bounded port. -/
def canonicalResolvedPortClassify
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    CanonicalResolvedPortClass occurrence := by
  by_cases hphysical : occurrence.edgeId < degree
  · exact .physical hphysical
  by_cases hinternal : occurrence.edgeId ∈
      canonicalInternalFusionEdges degree
  · exact .internal hinternal
  have hused := canonicalResolvedPort_edge_mem_used
    hdegree hallowed occurrence
  have hclass := canonicalUsedCoordinate_classify hdegree hused
  have hterminator : occurrence.edgeId = degree := by
    rcases hclass with hphysical' | hterminator | hinternal'
    · exact False.elim (hphysical hphysical')
    · exact hterminator
    · exact False.elim (hinternal hinternal')
  have hauxiliary : occurrence.edgeId ∈
      canonicalUsedAuxiliaryCoordinates degree := by
    rw [canonicalUsedCoordinates_eq_range_append_auxiliary hdegree] at hused
    rcases List.mem_append.mp hused with hrange | hauxiliary
    · exact False.elim (hphysical (List.mem_range.mp hrange))
    · exact hauxiliary
  have hterminatorUsed : degree ∈
      canonicalUsedAuxiliaryCoordinates degree := by
    simpa only [hterminator] using hauxiliary
  exact False.elim
    ((no_resolved_port_on_used_terminator
      hallowed hterminatorUsed occurrence) hterminator)

/-! ## 3. The actual stop-or-advance compiler -/

/-- Physical strand terminals in one accepted canonical link network. -/
abbrev CanonicalPhysicalStrandPort
    {degree : Nat} (external auxiliary : EdgeLabelling)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true) :=
  { occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) //
    occurrence.edgeId < degree }

/-- One total step of the link-strand dynamics.  A physical port is returned
as a terminal.  An internal port crosses its edge without changing slot and
then takes the local trivalent mate at the adjacent endpoint. -/
def canonicalLinkStrandStep
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    CanonicalPhysicalStrandPort external auxiliary hallowed ⊕
      ResolvedNetworkPort
        (canonicalLinkResolvedStrandNetwork
          degree external auxiliary hallowed) :=
  match canonicalResolvedPortClassify hdegree hallowed occurrence with
  | .physical hedge => Sum.inl ⟨occurrence, hedge⟩
  | .internal hedge =>
      let internal : CanonicalInternalStrandPort occurrence.edgeId
          external auxiliary hallowed := ⟨occurrence, rfl⟩
      Sum.inr
        (canonicalInternalStrandContinue
          hdegree hallowed hedge internal).1.localMate

/-- On a known physical port, the total step stops at that identical port. -/
theorem canonicalLinkStrandStep_of_physical
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hphysical : occurrence.edgeId < degree) :
    canonicalLinkStrandStep hdegree hallowed occurrence =
      Sum.inl ⟨occurrence, hphysical⟩ := by
  simp [canonicalLinkStrandStep, canonicalResolvedPortClassify, hphysical]

/-- On a known internal port, the total step is exactly same-slot crossing
followed by the local trivalent mate. -/
theorem canonicalLinkStrandStep_of_internal
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : occurrence.edgeId ∈ canonicalInternalFusionEdges degree) :
    canonicalLinkStrandStep hdegree hallowed occurrence =
      Sum.inr
        (canonicalInternalStrandContinue hdegree hallowed hinternal
          (⟨occurrence, rfl⟩ : CanonicalInternalStrandPort
            occurrence.edgeId external auxiliary hallowed)).1.localMate := by
  have hnotPhysical :=
    canonicalInternalFusionEdge_not_lt hdegree hinternal
  simp [canonicalLinkStrandStep, canonicalResolvedPortClassify,
    hnotPhysical, hinternal]

#print axioms resolvedNetworkPort_vertex_mem
#print axioms resolvedNetworkPort_vertexContains
#print axioms canonicalResolvedPort_edge_mem_used
#print axioms canonicalInternalFusionEdge_not_lt
#print axioms CanonicalResolvedPortClass
#print axioms canonicalResolvedPortClassify
#print axioms CanonicalPhysicalStrandPort
#print axioms canonicalLinkStrandStep
#print axioms canonicalLinkStrandStep_of_physical
#print axioms canonicalLinkStrandStep_of_internal

end YMGap.Continuum.CanonicalLinkStrandStep
