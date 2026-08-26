/-
# Strand-resolved accepted fusion paths at one corrected-slab link

`CompactDualSlabFineIntertwinerWitness` exposes each local SU(2) invariant
multiplicity as a finite list of accepted canonical auxiliary labellings.
`SU2TrivalentStrandPeeling` resolves one admissible trivalent vertex into its
three unique strand bundles.  This module joins those two facts.

First, any finite trivalent graph whose Boolean fusion guard is true is
compiled into a `Type`-valued list of resolved vertices.  The compiler keeps
the original vertex identifiers exactly, so shared auxiliary channels remain
visible.  It is then specialized to every literal member of
`slabLinkFusionWitnesses`: an accepted corrected-slab link witness returns the
strand resolution of every vertex in its canonical left-fusion chain.

This is the local-network layer needed before a global strand can be followed
from link to link through a plaquette copy.  It does not yet choose compatible
copies across the four boundary links of a face, close a strand component, or
peel a complete BF4 configuration.

Constructive contract: recursion on explicit finite lists and decidable
Boolean guards only.  No `Classical.*`, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
import YMGap.Continuum.SU2FusionSupportAddition
import YMGap.Continuum.SU2TrivalentStrandPeeling

namespace YMGap.Continuum.CompactDualSlabLinkStrandResolution

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.SU2TrivalentStrandPeeling
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Resolve every vertex of an admissible finite graph -/

/-- One original trivalent vertex together with its explicit strand data
under a fixed edge labelling. -/
structure ResolvedTrivalentVertex (label : EdgeLabelling) : Type where
  vertex : TrivalentVertex
  strands :
    TrivalentStrandResolution
      (label vertex.1) (label vertex.2.1) (label vertex.2.2)

/-- Recursively resolve every vertex of a Boolean-admissible trivalent graph.
The natural data in each resolution are computed from the displayed labels;
the guard proof is used only to certify their balance equations. -/
def resolveAdmissibleVertices (label : EdgeLabelling) :
    (vertices : List TrivalentVertex) ->
      verticesAdmissibleB vertices label = true ->
        List (ResolvedTrivalentVertex label)
  | [], _ => []
  | vertex :: rest, hadmissible =>
      let parts :=
        (verticesAdmissibleB_cons_true_iff
          vertex rest label).mp hadmissible
      { vertex := vertex
        strands :=
          canonicalTrivalentStrandResolution
            (label vertex.1) (label vertex.2.1) (label vertex.2.2)
            parts.1 } ::
        resolveAdmissibleVertices label rest parts.2

/-- The compiler preserves the complete ordered vertex list exactly. -/
theorem resolveAdmissibleVertices_map_vertex
    (label : EdgeLabelling) :
    forall (vertices : List TrivalentVertex)
      (hadmissible : verticesAdmissibleB vertices label = true),
      (resolveAdmissibleVertices label vertices hadmissible).map
          (fun resolved => resolved.vertex) =
        vertices
  | [], _ => rfl
  | vertex :: rest, hadmissible => by
      let parts :=
        (verticesAdmissibleB_cons_true_iff
          vertex rest label).mp hadmissible
      change vertex ::
          (resolveAdmissibleVertices label rest parts.2).map
            (fun resolved => resolved.vertex) =
        vertex :: rest
      rw [resolveAdmissibleVertices_map_vertex label rest parts.2]

/-- A resolved finite graph packages the vertexwise strand data together with
the exact ordered-support equation consumed by later incidence code. -/
structure ResolvedTrivalentNetwork
    (vertices : List TrivalentVertex) (label : EdgeLabelling) : Type where
  resolved : List (ResolvedTrivalentVertex label)
  vertices_exact : resolved.map (fun item => item.vertex) = vertices

/-- Compile a true finite-graph fusion guard into an exact resolved network. -/
def resolvedTrivalentNetworkOfAdmissible
    (vertices : List TrivalentVertex) (label : EdgeLabelling)
    (hadmissible : verticesAdmissibleB vertices label = true) :
    ResolvedTrivalentNetwork vertices label where
  resolved := resolveAdmissibleVertices label vertices hadmissible
  vertices_exact :=
    resolveAdmissibleVertices_map_vertex label vertices hadmissible

/-- Resolution introduces neither missing nor duplicate vertices. -/
theorem ResolvedTrivalentNetwork.length_eq
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) :
    network.resolved.length = vertices.length := by
  have hlength := congrArg List.length network.vertices_exact
  simpa only [List.length_map] using hlength

/-! ## 2. The canonical one-link fusion chain -/

/-- The canonical consecutive-identifier trivalent chain at valence
`degree`. -/
def canonicalLinkVertices (degree : Nat) : List TrivalentVertex :=
  fuseLabels degree (degree + 1) (List.range degree)

/-- Overlay the fixed external spins with one canonical auxiliary witness. -/
def canonicalLinkLabelling
    (degree : Nat) (external auxiliary : EdgeLabelling) : EdgeLabelling :=
  overlayOn (List.range degree) external auxiliary

/-- The vertex half of the accepted canonical-link guard. -/
theorem canonicalLinkConditionalAllowedB_vertices_admissible
    (degree : Nat) (external auxiliary : EdgeLabelling)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    verticesAdmissibleB
        (canonicalLinkVertices degree)
        (canonicalLinkLabelling degree external auxiliary) = true := by
  unfold canonicalLinkConditionalAllowedB at hallowed
  unfold canonicalLinkVertices canonicalLinkLabelling
  exact ((Bool.and_eq_true _ _).mp hallowed).1

/-- Every accepted canonical auxiliary labelling compiles to the complete
strand-resolved left-fusion chain at that link. -/
def canonicalLinkResolvedStrandNetwork
    (degree : Nat) (external auxiliary : EdgeLabelling)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    ResolvedTrivalentNetwork
      (canonicalLinkVertices degree)
      (canonicalLinkLabelling degree external auxiliary) :=
  resolvedTrivalentNetworkOfAdmissible
    (canonicalLinkVertices degree)
    (canonicalLinkLabelling degree external auxiliary)
    (canonicalLinkConditionalAllowedB_vertices_admissible
      degree external auxiliary hallowed)

/-! ## 3. Specialization to a literal corrected-slab witness -/

/-- Membership in the production witness list exposes its exact canonical
fusion guard. -/
theorem slabLinkFusionWitness_mem_allowed
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem :
      auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    canonicalLinkConditionalAllowedB
        (slabIncidentPlaqIds extent link).length
        (slabLinkExternalSpins extent physical link)
        auxiliary = true := by
  unfold slabLinkFusionWitnesses at hmem
  exact (List.mem_filter.mp hmem).2

/-- A literal accepted corrected-slab link-intertwiner witness returns the
strand resolution of every trivalent vertex in its production chain. -/
def slabLinkResolvedStrandNetwork
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem :
      auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    ResolvedTrivalentNetwork
      (canonicalLinkVertices
        (slabIncidentPlaqIds extent link).length)
      (canonicalLinkLabelling
        (slabIncidentPlaqIds extent link).length
        (slabLinkExternalSpins extent physical link)
        auxiliary) :=
  canonicalLinkResolvedStrandNetwork
    (slabIncidentPlaqIds extent link).length
    (slabLinkExternalSpins extent physical link)
    auxiliary
    (slabLinkFusionWitness_mem_allowed
      K extent physical link auxiliary hmem)

/-- In particular, the resolved production witness has exactly as many
entries as the canonical trivalent chain. -/
theorem slabLinkResolvedStrandNetwork_length
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem :
      auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    (slabLinkResolvedStrandNetwork
        K extent physical link auxiliary hmem).resolved.length =
      (canonicalLinkVertices
        (slabIncidentPlaqIds extent link).length).length :=
  (slabLinkResolvedStrandNetwork
    K extent physical link auxiliary hmem).length_eq

#print axioms resolveAdmissibleVertices
#print axioms resolveAdmissibleVertices_map_vertex
#print axioms resolvedTrivalentNetworkOfAdmissible
#print axioms ResolvedTrivalentNetwork.length_eq
#print axioms canonicalLinkConditionalAllowedB_vertices_admissible
#print axioms canonicalLinkResolvedStrandNetwork
#print axioms slabLinkFusionWitness_mem_allowed
#print axioms slabLinkResolvedStrandNetwork
#print axioms slabLinkResolvedStrandNetwork_length

end YMGap.Continuum.CompactDualSlabLinkStrandResolution
