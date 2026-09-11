/-
# The first physical ports of a canonical link resolver

Every canonical left-fusion chain of valence at least two begins with the
physical edge identifiers `0` and `1` on the `a` and `b` legs of vertex zero.
This file makes those two dependent half-edges explicit in the actual resolved
network.  The upper valence bound is the geometric four-dimensional bound and
lets the finite canonical chain reduce without any classical search.

The result is the position-level interface needed to identify a root-first
ordered link with an explicit stretched trivalent vertex.  It does not yet
identify the label on the third leg or compute the local strand mate.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges

namespace YMGap.Continuum.CanonicalLinkFirstVertexPorts

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity

/-! ## 1. Vertex zero in the resolved canonical chain -/

/-- The first resolved vertex of a canonical link of valence between two and
six. -/
def canonicalLinkFirstVertexIndex
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    Fin (canonicalLinkResolvedStrandNetwork
      degree external auxiliary hallowed).resolved.length :=
  ⟨0, by
    rw [(canonicalLinkResolvedStrandNetwork
      degree external auxiliary hallowed).length_eq]
    unfold linkIncidenceBound at hdegreeUpper
    have hdegreeCases : degree = 2 ∨ degree = 3 ∨ degree = 4 ∨
        degree = 5 ∨ degree = 6 := by
      omega
    rcases hdegreeCases with rfl | rfl | rfl | rfl | rfl <;> decide⟩

@[simp] theorem canonicalLinkFirstVertexIndex_val
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    (canonicalLinkFirstVertexIndex
      hdegreeLower hdegreeUpper hallowed).val = 0 :=
  rfl

/-! ## 2. The first two physical half-edges -/

/-- Physical identifier zero is the `a` leg at vertex zero. -/
def canonicalLinkFirstAHalfEdge
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    ResolvedNetworkHalfEdge
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) where
  vertexIndex := canonicalLinkFirstVertexIndex
    hdegreeLower hdegreeUpper hallowed
  leg := .a

/-- Physical identifier one is the `b` leg at vertex zero. -/
def canonicalLinkFirstBHalfEdge
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    ResolvedNetworkHalfEdge
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) where
  vertexIndex := canonicalLinkFirstVertexIndex
    hdegreeLower hdegreeUpper hallowed
  leg := .b

@[simp] theorem canonicalLinkFirstAHalfEdge_vertexIndex
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    (canonicalLinkFirstAHalfEdge
      hdegreeLower hdegreeUpper hallowed).vertexIndex.val = 0 :=
  rfl

@[simp] theorem canonicalLinkFirstBHalfEdge_vertexIndex
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    (canonicalLinkFirstBHalfEdge
      hdegreeLower hdegreeUpper hallowed).vertexIndex.val = 0 :=
  rfl

@[simp] theorem canonicalLinkFirstAHalfEdge_leg
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    (canonicalLinkFirstAHalfEdge
      hdegreeLower hdegreeUpper hallowed).leg = .a :=
  rfl

@[simp] theorem canonicalLinkFirstBHalfEdge_leg
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    (canonicalLinkFirstBHalfEdge
      hdegreeLower hdegreeUpper hallowed).leg = .b :=
  rfl

@[simp] theorem canonicalLinkFirstAHalfEdge_edgeId
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    (canonicalLinkFirstAHalfEdge
      hdegreeLower hdegreeUpper hallowed).edgeId = 0 := by
  unfold linkIncidenceBound at hdegreeUpper
  have hdegreeCases : degree = 2 ∨ degree = 3 ∨ degree = 4 ∨
      degree = 5 ∨ degree = 6 := by
    omega
  rcases hdegreeCases with rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem canonicalLinkFirstBHalfEdge_edgeId
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegreeLower : 2 ≤ degree)
    (hdegreeUpper : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    (canonicalLinkFirstBHalfEdge
      hdegreeLower hdegreeUpper hallowed).edgeId = 1 := by
  unfold linkIncidenceBound at hdegreeUpper
  have hdegreeCases : degree = 2 ∨ degree = 3 ∨ degree = 4 ∨
      degree = 5 ∨ degree = 6 := by
    omega
  rcases hdegreeCases with rfl | rfl | rfl | rfl | rfl <;> rfl

end YMGap.Continuum.CanonicalLinkFirstVertexPorts

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CanonicalLinkFirstVertexPorts.canonicalLinkFirstVertexIndex
#print axioms
  YMGap.Continuum.CanonicalLinkFirstVertexPorts.canonicalLinkFirstAHalfEdge_edgeId
#print axioms
  YMGap.Continuum.CanonicalLinkFirstVertexPorts.canonicalLinkFirstBHalfEdge_edgeId
