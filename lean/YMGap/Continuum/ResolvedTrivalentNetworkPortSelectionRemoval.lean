/-
# Descend occurrence-closed port selections to coherent strand removal

A physical strand selection is naturally evaluated on literal port
occurrences, while the conservation compiler uses one Boolean value for each
graph-edge strand copy.  The only mathematical seam between them is finite
descent: if two occurrences with the same `(edgeId, slot)` have the same
Boolean value, the exhaustive port list supplies a proof-independent value for
that edge copy.  Missing edge copies receive `false` and are never observed by
a resolved vertex.

Local-mate invariance then descends verbatim, so the existing three Kirchhoff
identities compile the occurrence selection to one coherent removal plan.
The representative search is confined to this generic finite descent; no
canonical-link geometry or physical terminal classification enters it.

Honest scope: this module consumes same-copy invariance.  Proving that the
physical terminal pullback has this invariance on the canonical link network
is the next geometric orbit lemma.

Constructive contract: exhaustive finite search with decidable equality and
structural conservation only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval

namespace YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPortPairing

/-! ## 1. Occurrence-level closed selections -/

/-- A Boolean selection on literal resolved-network port occurrences.

`local_closed` is the vertexwise conservation law.  `same_copy_closed` says
that the value belongs to the graph-edge strand copy rather than to a chosen
half-edge occurrence. -/
structure ResolvedNetworkPortClosedSelection
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) : Type where
  selected : ResolvedNetworkPort network -> Bool
  local_closed : forall port, selected port.localMate = selected port
  same_copy_closed : forall left right,
    left.edgeId = right.edgeId -> left.slot = right.slot ->
      selected left = selected right

/-- Decidable characteristic function of one graph-edge strand-copy fiber. -/
def portHasEdgeSlot
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (edge slot : Nat) (port : ResolvedNetworkPort network) : Bool :=
  decide (port.edgeId = edge) && decide (port.slot = slot)

/-- Select the first literal occurrence of an edge-copy, if it exists, and
evaluate the occurrence selection there.  The value is `false` only for an
edge-copy absent from the resolved network. -/
def ResolvedNetworkPortClosedSelection.edgeSlotValue
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (selection : ResolvedNetworkPortClosedSelection network)
    (edge slot : Nat) : Bool :=
  match (allResolvedNetworkPorts network).find?
      (portHasEdgeSlot edge slot) with
  | some port => selection.selected port
  | none => false

/-- Finite descent is exact on every actual port occurrence. -/
theorem ResolvedNetworkPortClosedSelection.edgeSlotValue_at_port
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (selection : ResolvedNetworkPortClosedSelection network)
    (port : ResolvedNetworkPort network) :
    selection.edgeSlotValue port.edgeId port.slot =
      selection.selected port := by
  unfold ResolvedNetworkPortClosedSelection.edgeSlotValue
  cases hfind : (allResolvedNetworkPorts network).find?
      (portHasEdgeSlot port.edgeId port.slot) with
  | none =>
      have hfalse := (List.find?_eq_none.mp hfind)
        port port.mem_all
      have htrue : portHasEdgeSlot port.edgeId port.slot port = true := by
        simp [portHasEdgeSlot]
      rw [htrue] at hfalse
      exact False.elim (hfalse rfl)
  | some representative =>
      have hfiber := List.find?_some hfind
      have hparts := (Bool.and_eq_true _ _).mp hfiber
      exact selection.same_copy_closed representative port
        (of_decide_eq_true hparts.1) (of_decide_eq_true hparts.2)

/-! ## 2. Descent into the existing Kirchhoff compiler -/

/-- The occurrence-level selection descends to one Boolean per graph-edge
strand copy, with local mate closure inherited exactly. -/
def ResolvedNetworkPortClosedSelection.toMateClosedSelection
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (selection : ResolvedNetworkPortClosedSelection network) :
    ResolvedNetworkMateClosedSelection network.resolved where
  selected := selection.edgeSlotValue
  mate_closed := by
    intro vertex hvertex port
    obtain ⟨index, hindex, hget⟩ := List.getElem_of_mem hvertex
    subst vertex
    let occurrence : ResolvedNetworkPort network :=
      ⟨⟨index, hindex⟩, port⟩
    calc
      selection.edgeSlotValue
          ((network.resolved[index]).vertex |> fun vertex =>
            vertexEdgeId vertex (strandMate
              (network.resolved[index]).strands port).leg)
          (strandMate (network.resolved[index]).strands port).slot =
          selection.selected occurrence.localMate := by
        simpa [occurrence, ResolvedNetworkPort.localMate,
          ResolvedNetworkPort.edgeId, ResolvedNetworkPort.vertex,
          ResolvedNetworkPort.leg, ResolvedNetworkPort.slot,
          resolvedVertexAt] using
            selection.edgeSlotValue_at_port occurrence.localMate
      _ = selection.selected occurrence :=
        selection.local_closed occurrence
      _ = selection.edgeSlotValue
          (vertexEdgeId (network.resolved[index]).vertex port.leg)
          port.slot := by
        simpa [occurrence, ResolvedNetworkPort.edgeId,
          ResolvedNetworkPort.vertex, ResolvedNetworkPort.leg,
          ResolvedNetworkPort.slot, resolvedVertexAt] using
            (selection.edgeSlotValue_at_port occurrence).symm

/-- The descended selection's common drop is exactly the finite count of the
proof-independent edge-slot values.  This generic transparency lemma lets
physical specializations reason about the count without unfolding their
entire dependent network. -/
theorem ResolvedNetworkPortClosedSelection.toMateClosedSelection_drop
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (selection : ResolvedNetworkPortClosedSelection network) :
    (selection.toMateClosedSelection network).drop =
      fun edge => boolCountFrom (selection.edgeSlotValue edge)
        0 (label edge) := rfl

/-- **Occurrence-to-removal compiler.**  Same-copy descent followed by the
three local Kirchhoff identities constructs one coherent network removal. -/
def ResolvedNetworkPortClosedSelection.toCoherentRemoval
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (selection : ResolvedNetworkPortClosedSelection network) :
    CoherentResolvedTrivalentRemoval network :=
  (selection.toMateClosedSelection network).toCoherentRemoval network

#print axioms ResolvedNetworkPortClosedSelection
#print axioms portHasEdgeSlot
#print axioms ResolvedNetworkPortClosedSelection.edgeSlotValue
#print axioms ResolvedNetworkPortClosedSelection.edgeSlotValue_at_port
#print axioms ResolvedNetworkPortClosedSelection.toMateClosedSelection
#print axioms ResolvedNetworkPortClosedSelection.toMateClosedSelection_drop
#print axioms ResolvedNetworkPortClosedSelection.toCoherentRemoval

end YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval
