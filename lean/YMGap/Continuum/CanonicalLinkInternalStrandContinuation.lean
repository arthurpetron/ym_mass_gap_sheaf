/-
# Same-slot strand continuation across an internal canonical link edge

The internal half-edge transposition becomes a strand continuation by carrying
the source copy number unchanged to the other endpoint.  This module makes
that sentence literal: a half-edge plus a slot below its edge label rebuilds a
unique typed `ResolvedNetworkPort`, and the canonical two-endpoint swap lifts
to a fixed-point-free involution of the ports over a selected internal edge.

Constructive contract: dependent reconstruction from explicit finite indices
only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkInternalHalfEdgeSwap

namespace YMGap.Continuum.CanonicalLinkInternalStrandContinuation

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalHalfEdgeSwap
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState

/-! ## 1. Ports are exactly a half-edge plus a bounded slot -/

/-- Forget a port's slot while retaining its bounded vertex and leg. -/
def resolvedNetworkPortHalfEdge
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    ResolvedNetworkHalfEdge network where
  vertexIndex := occurrence.vertexIndex
  leg := occurrence.leg

/-- Forgetting the slot does not change the graph-edge identifier. -/
@[simp] theorem resolvedNetworkPortHalfEdge_edgeId
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    (resolvedNetworkPortHalfEdge occurrence).edgeId = occurrence.edgeId :=
  rfl

/-- Rebuild the unique typed port at a half-edge and bounded slot. -/
def resolvedNetworkHalfEdgePortAt
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (halfEdge : ResolvedNetworkHalfEdge network) (slot : Nat)
    (hslot : slot < label halfEdge.edgeId) :
    ResolvedNetworkPort network := by
  cases halfEdge with
  | mk index leg =>
      cases leg with
      | a => exact ⟨index, .onA ⟨slot, hslot⟩⟩
      | b => exact ⟨index, .onB ⟨slot, hslot⟩⟩
      | c => exact ⟨index, .onC ⟨slot, hslot⟩⟩

/-- Rebuilding at a half-edge retains that half-edge exactly. -/
@[simp] theorem resolvedNetworkHalfEdgePortAt_halfEdge
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (halfEdge : ResolvedNetworkHalfEdge network) (slot : Nat)
    (hslot : slot < label halfEdge.edgeId) :
    resolvedNetworkPortHalfEdge
        (resolvedNetworkHalfEdgePortAt halfEdge slot hslot) = halfEdge := by
  cases halfEdge with
  | mk index leg => cases leg <;> rfl

/-- Rebuilding at a half-edge retains the selected slot. -/
@[simp] theorem resolvedNetworkHalfEdgePortAt_slot
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (halfEdge : ResolvedNetworkHalfEdge network) (slot : Nat)
    (hslot : slot < label halfEdge.edgeId) :
    (resolvedNetworkHalfEdgePortAt halfEdge slot hslot).slot = slot := by
  cases halfEdge with
  | mk index leg => cases leg <;> rfl

/-- Rebuilding at a half-edge retains its graph-edge identifier. -/
@[simp] theorem resolvedNetworkHalfEdgePortAt_edgeId
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (halfEdge : ResolvedNetworkHalfEdge network) (slot : Nat)
    (hslot : slot < label halfEdge.edgeId) :
    (resolvedNetworkHalfEdgePortAt halfEdge slot hslot).edgeId =
      halfEdge.edgeId := by
  cases halfEdge with
  | mk index leg => cases leg <;> rfl

/-- A port's slot is bounded at its forgotten half-edge. -/
theorem resolvedNetworkPortSlot_lt_halfEdgeLabel
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    occurrence.slot < label (resolvedNetworkPortHalfEdge occurrence).edgeId := by
  rw [resolvedNetworkPortHalfEdge_edgeId]
  exact occurrence.slot_lt_edgeLabel

/-- Forgetting and rebuilding with the original slot is the identity. -/
theorem resolvedNetworkPortAt_halfEdge_slot
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    resolvedNetworkHalfEdgePortAt (resolvedNetworkPortHalfEdge occurrence)
        occurrence.slot (resolvedNetworkPortSlot_lt_halfEdgeLabel occurrence) =
      occurrence := by
  cases occurrence with
  | mk index port => cases port <;> rfl

/-- A half-edge and slot determine a network port uniquely. -/
theorem resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    {left right : ResolvedNetworkPort network}
    (hhalfEdge : resolvedNetworkPortHalfEdge left =
      resolvedNetworkPortHalfEdge right)
    (hslot : left.slot = right.slot) : left = right := by
  apply ResolvedNetworkPort.address_injective
  cases left with
  | mk leftIndex leftPort =>
      cases right with
      | mk rightIndex rightPort =>
          cases leftPort <;> cases rightPort <;>
            simp_all [ResolvedNetworkPort.address,
              resolvedNetworkPortHalfEdge, ResolvedNetworkPort.leg,
              ResolvedNetworkPort.slot, TrivalentStrandPort.leg,
              TrivalentStrandPort.slot, Fin.ext_iff]

/-! ## 2. Same-slot continuation on a fixed internal edge -/

/-- Typed strand ports lying over a selected graph-edge identifier. -/
abbrev CanonicalInternalStrandPort
    {degree : Nat} (edge : Nat) (external auxiliary : EdgeLabelling)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true) :=
  { occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) //
    occurrence.edgeId = edge }

/-- Forget the slot of an internal strand while retaining membership in its
two-point half-edge fiber. -/
def canonicalInternalStrandHalfEdge
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (occurrence :
      CanonicalInternalStrandPort edge external auxiliary hallowed) :
    CanonicalInternalHalfEdge edge external auxiliary hallowed :=
  ⟨resolvedNetworkPortHalfEdge occurrence.1,
    (mem_halfEdgesOnEdge_iff _ _).mpr
      ((resolvedNetworkPortHalfEdge_edgeId occurrence.1).trans occurrence.2)⟩

/-- Exchange the two internal half-edge endpoints and carry the strand slot
unchanged. -/
def canonicalInternalStrandContinue
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree) :
    CanonicalInternalStrandPort edge external auxiliary hallowed ->
      CanonicalInternalStrandPort edge external auxiliary hallowed := by
  intro occurrence
  let target := canonicalInternalHalfEdgeSwap hdegree hallowed hedge
    (canonicalInternalStrandHalfEdge occurrence)
  have htarget : target.1.edgeId = edge :=
    canonicalInternalHalfEdgeSwap_edgeId hdegree hallowed hedge
      (canonicalInternalStrandHalfEdge occurrence)
  have hslot : occurrence.1.slot <
      canonicalLinkLabelling degree external auxiliary target.1.edgeId := by
    rw [htarget]
    exact Eq.mp
      (congrArg
        (fun identifier => occurrence.1.slot <
          canonicalLinkLabelling degree external auxiliary identifier)
        occurrence.2)
      occurrence.1.slot_lt_edgeLabel
  refine ⟨resolvedNetworkHalfEdgePortAt target.1 occurrence.1.slot hslot, ?_⟩
  exact (resolvedNetworkHalfEdgePortAt_edgeId
    target.1 occurrence.1.slot hslot).trans htarget

/-- Same-slot continuation realizes exactly the half-edge transposition. -/
theorem canonicalInternalStrandContinue_halfEdge
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence :
      CanonicalInternalStrandPort edge external auxiliary hallowed) :
    canonicalInternalStrandHalfEdge
        (canonicalInternalStrandContinue hdegree hallowed hedge occurrence) =
      canonicalInternalHalfEdgeSwap hdegree hallowed hedge
        (canonicalInternalStrandHalfEdge occurrence) := by
  apply Subtype.ext
  simp [canonicalInternalStrandContinue,
    canonicalInternalStrandHalfEdge]

/-- Same-slot continuation really preserves the strand-copy number. -/
theorem canonicalInternalStrandContinue_slot
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence :
      CanonicalInternalStrandPort edge external auxiliary hallowed) :
    (canonicalInternalStrandContinue
      hdegree hallowed hedge occurrence).1.slot = occurrence.1.slot := by
  simp [canonicalInternalStrandContinue]

/-- The typed internal strand continuation has no fixed occurrence. -/
theorem canonicalInternalStrandContinue_ne_self
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence :
      CanonicalInternalStrandPort edge external auxiliary hallowed) :
    canonicalInternalStrandContinue hdegree hallowed hedge occurrence ≠
      occurrence := by
  intro heq
  apply canonicalInternalHalfEdgeSwap_ne_self hdegree hallowed hedge
    (canonicalInternalStrandHalfEdge occurrence)
  calc
    canonicalInternalHalfEdgeSwap hdegree hallowed hedge
        (canonicalInternalStrandHalfEdge occurrence) =
        canonicalInternalStrandHalfEdge
          (canonicalInternalStrandContinue
            hdegree hallowed hedge occurrence) :=
      (canonicalInternalStrandContinue_halfEdge
        hdegree hallowed hedge occurrence).symm
    _ = canonicalInternalStrandHalfEdge occurrence :=
      congrArg canonicalInternalStrandHalfEdge heq

/-- The typed same-slot continuation is an involution. -/
theorem canonicalInternalStrandContinue_involutive
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence :
      CanonicalInternalStrandPort edge external auxiliary hallowed) :
    canonicalInternalStrandContinue hdegree hallowed hedge
        (canonicalInternalStrandContinue hdegree hallowed hedge occurrence) =
      occurrence := by
  apply Subtype.ext
  apply resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq
  · have hmember :
        canonicalInternalStrandHalfEdge
            (canonicalInternalStrandContinue hdegree hallowed hedge
              (canonicalInternalStrandContinue
                hdegree hallowed hedge occurrence)) =
          canonicalInternalStrandHalfEdge occurrence := by
      calc
        canonicalInternalStrandHalfEdge
            (canonicalInternalStrandContinue hdegree hallowed hedge
              (canonicalInternalStrandContinue
                hdegree hallowed hedge occurrence)) =
            canonicalInternalHalfEdgeSwap hdegree hallowed hedge
              (canonicalInternalStrandHalfEdge
                (canonicalInternalStrandContinue
                  hdegree hallowed hedge occurrence)) :=
          canonicalInternalStrandContinue_halfEdge hdegree hallowed hedge _
        _ = canonicalInternalHalfEdgeSwap hdegree hallowed hedge
              (canonicalInternalHalfEdgeSwap hdegree hallowed hedge
                (canonicalInternalStrandHalfEdge occurrence)) := by
          rw [canonicalInternalStrandContinue_halfEdge]
        _ = canonicalInternalStrandHalfEdge occurrence :=
          canonicalInternalHalfEdgeSwap_involutive hdegree hallowed hedge _
    exact congrArg Subtype.val hmember
  · calc
      (canonicalInternalStrandContinue hdegree hallowed hedge
          (canonicalInternalStrandContinue
            hdegree hallowed hedge occurrence)).1.slot =
          (canonicalInternalStrandContinue
            hdegree hallowed hedge occurrence).1.slot :=
        canonicalInternalStrandContinue_slot hdegree hallowed hedge _
      _ = occurrence.1.slot :=
        canonicalInternalStrandContinue_slot hdegree hallowed hedge occurrence

#print axioms resolvedNetworkPortHalfEdge
#print axioms resolvedNetworkPortHalfEdge_edgeId
#print axioms resolvedNetworkHalfEdgePortAt
#print axioms resolvedNetworkHalfEdgePortAt_halfEdge
#print axioms resolvedNetworkHalfEdgePortAt_slot
#print axioms resolvedNetworkHalfEdgePortAt_edgeId
#print axioms resolvedNetworkPortSlot_lt_halfEdgeLabel
#print axioms resolvedNetworkPortAt_halfEdge_slot
#print axioms resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq
#print axioms CanonicalInternalStrandPort
#print axioms canonicalInternalStrandHalfEdge
#print axioms canonicalInternalStrandContinue
#print axioms canonicalInternalStrandContinue_halfEdge
#print axioms canonicalInternalStrandContinue_slot
#print axioms canonicalInternalStrandContinue_ne_self
#print axioms canonicalInternalStrandContinue_involutive

end YMGap.Continuum.CanonicalLinkInternalStrandContinuation
