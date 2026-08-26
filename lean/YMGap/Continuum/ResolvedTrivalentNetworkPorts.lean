/-
# Literal strand-port occurrences in a resolved trivalent network

`CompactDualSlabLinkStrandResolution` produces an ordered list of resolved
trivalent vertices.  `SU2TrivalentStrandPortPairing` produces the individual
bounded strand copies and their exact mate at one such vertex.  This module
forms their dependent sum.

A `ResolvedNetworkPort` remembers the vertex occurrence, the leg, the strand
copy, and therefore the actual graph-edge identifier on which that copy lies.
The local mate remains at the same vertex, changes legs, has no fixed point,
and is involutive.  An explicit finite list enumerates every network port.

This is the common typed carrier needed by the next incidence compiler:
copies on the same auxiliary graph edge can now be continued between its two
vertex occurrences, while copies on physical external edges can be attached
to the corresponding lattice plaquette occurrence.  This module does not yet
construct either continuation.

Constructive contract: dependent finite sums and explicit `List.finRange`
enumeration only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabLinkStrandResolution
import YMGap.Continuum.SU2TrivalentStrandPortPairing

namespace YMGap.Continuum.ResolvedTrivalentNetworkPorts

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPortPairing

/-! ## 1. Ports at one resolved vertex -/

/-- The graph-edge identifier selected by one trivalent leg. -/
def vertexEdgeId (vertex : TrivalentVertex) : TrivalentLeg -> Nat
  | .a => vertex.1
  | .b => vertex.2.1
  | .c => vertex.2.2

/-- Enumerate every bounded strand copy at one resolved vertex. -/
def portsAtResolvedVertex {label : EdgeLabelling}
    (resolved : ResolvedTrivalentVertex label) :
    List (TrivalentStrandPort
      (label resolved.vertex.1)
      (label resolved.vertex.2.1)
      (label resolved.vertex.2.2)) :=
  (List.finRange (label resolved.vertex.1)).map
      TrivalentStrandPort.onA ++
    (List.finRange (label resolved.vertex.2.1)).map
      TrivalentStrandPort.onB ++
    (List.finRange (label resolved.vertex.2.2)).map
      TrivalentStrandPort.onC

/-- The one-vertex enumeration contains every typed port. -/
theorem mem_portsAtResolvedVertex {label : EdgeLabelling}
    (resolved : ResolvedTrivalentVertex label)
    (port : TrivalentStrandPort
      (label resolved.vertex.1)
      (label resolved.vertex.2.1)
      (label resolved.vertex.2.2)) :
    port ∈ portsAtResolvedVertex resolved := by
  cases port <;> simp [portsAtResolvedVertex]

/-- The enumeration cardinality is the total twice-spin at the vertex. -/
theorem portsAtResolvedVertex_length {label : EdgeLabelling}
    (resolved : ResolvedTrivalentVertex label) :
    (portsAtResolvedVertex resolved).length =
      label resolved.vertex.1 +
        label resolved.vertex.2.1 +
          label resolved.vertex.2.2 := by
  simp [portsAtResolvedVertex]
  omega

/-! ## 2. The dependent sum over an ordered resolved network -/

/-- Retrieve the resolved vertex at a bounded position in the ordered
network. -/
def resolvedVertexAt
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (index : Fin network.resolved.length) :
    ResolvedTrivalentVertex label :=
  network.resolved.get index

/-- One literal bounded strand-copy occurrence in an ordered resolved
network. -/
structure ResolvedNetworkPort
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) : Type where
  vertexIndex : Fin network.resolved.length
  port : TrivalentStrandPort
    (label (resolvedVertexAt network vertexIndex).vertex.1)
    (label (resolvedVertexAt network vertexIndex).vertex.2.1)
    (label (resolvedVertexAt network vertexIndex).vertex.2.2)

/-- The selected resolved vertex. -/
def ResolvedNetworkPort.vertex
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) : TrivalentVertex :=
  (resolvedVertexAt network occurrence.vertexIndex).vertex

/-- The selected trivalent leg. -/
def ResolvedNetworkPort.leg
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) : TrivalentLeg :=
  occurrence.port.leg

/-- The actual graph-edge identifier carrying this strand copy. -/
def ResolvedNetworkPort.edgeId
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) : Nat :=
  vertexEdgeId occurrence.vertex occurrence.leg

/-- The zero-based strand-copy number on the selected graph edge. -/
def ResolvedNetworkPort.slot
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) : Nat :=
  occurrence.port.slot

/-- A proof-independent address for deciding equality of dependent network
ports. -/
structure ResolvedNetworkPortAddress : Type where
  vertexIndex : Nat
  leg : TrivalentLeg
  slot : Nat
  deriving DecidableEq

/-- Forget only the bound proofs and retain the complete occurrence address. -/
def ResolvedNetworkPort.address
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    ResolvedNetworkPortAddress where
  vertexIndex := occurrence.vertexIndex.val
  leg := occurrence.leg
  slot := occurrence.slot

/-- The address loses no data: bounds are propositions and hence proof
irrelevance reconstructs the original dependent occurrence. -/
theorem ResolvedNetworkPort.address_injective
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    {left right : ResolvedNetworkPort network}
    (heq : left.address = right.address) :
    left = right := by
  cases left with
  | mk leftIndex leftPort =>
      cases right with
      | mk rightIndex rightPort =>
          have hindexValue := congrArg
            ResolvedNetworkPortAddress.vertexIndex heq
          have hindex : leftIndex = rightIndex := Fin.ext hindexValue
          subst rightIndex
          have hleg := congrArg ResolvedNetworkPortAddress.leg heq
          have hslot := congrArg ResolvedNetworkPortAddress.slot heq
          congr 1
          cases leftPort <;> cases rightPort <;>
            simp_all [ResolvedNetworkPort.address,
              ResolvedNetworkPort.leg, ResolvedNetworkPort.slot,
              TrivalentStrandPort.leg, TrivalentStrandPort.slot,
              Fin.ext_iff]

/-- Decidable equality is computed from the natural-number occurrence
address, with no classical choice. -/
def resolvedNetworkPortDecidableEq
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label} :
    DecidableEq (ResolvedNetworkPort network) :=
  fun left right =>
    match decEq left.address right.address with
    | isTrue heq => isTrue (ResolvedNetworkPort.address_injective heq)
    | isFalse hne => isFalse fun heq =>
        hne (congrArg ResolvedNetworkPort.address heq)

instance instDecidableEqResolvedNetworkPort
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label} :
    DecidableEq (ResolvedNetworkPort network) :=
  resolvedNetworkPortDecidableEq

/-- The occurrence's copy number is bounded by the actual label assigned to
its graph edge. -/
theorem ResolvedNetworkPort.slot_lt_edgeLabel
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    occurrence.slot < label occurrence.edgeId := by
  cases occurrence with
  | mk index port =>
      cases port <;> exact Fin.isLt _

/-! ## 3. The inherited local incidence involution -/

/-- Apply the exact trivalent mate without changing the vertex occurrence. -/
def ResolvedNetworkPort.localMate
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    ResolvedNetworkPort network where
  vertexIndex := occurrence.vertexIndex
  port := strandMate
    (resolvedVertexAt network occurrence.vertexIndex).strands
    occurrence.port

@[simp] theorem ResolvedNetworkPort.localMate_vertexIndex
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    occurrence.localMate.vertexIndex = occurrence.vertexIndex :=
  rfl

/-- Local pairing always changes the trivalent leg. -/
theorem ResolvedNetworkPort.localMate_leg_ne
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    occurrence.localMate.leg ≠ occurrence.leg :=
  strandMate_leg_ne
    (resolvedVertexAt network occurrence.vertexIndex).strands
    occurrence.port

/-- Local pairing twice returns the identical typed network occurrence. -/
theorem ResolvedNetworkPort.localMate_involutive
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    occurrence.localMate.localMate = occurrence := by
  cases occurrence with
  | mk index port =>
      change ResolvedNetworkPort.mk index
          (strandMate (resolvedVertexAt network index).strands
            (strandMate (resolvedVertexAt network index).strands port)) =
        ResolvedNetworkPort.mk index port
      rw [strandMate_involutive]

/-- Hence the local incidence pairing has no fixed occurrence. -/
theorem ResolvedNetworkPort.localMate_ne_self
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    occurrence.localMate ≠ occurrence := by
  intro heq
  have hleg := congrArg ResolvedNetworkPort.leg heq
  exact occurrence.localMate_leg_ne hleg

/-! ## 4. Explicit finite support -/

/-- Enumerate every dependent port occurrence in the ordered network. -/
def allResolvedNetworkPorts
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) :
    List (ResolvedNetworkPort network) :=
  (List.finRange network.resolved.length).flatMap fun index =>
    (portsAtResolvedVertex (resolvedVertexAt network index)).map fun port =>
      { vertexIndex := index, port := port }

/-- The finite support is exhaustive. -/
theorem ResolvedNetworkPort.mem_all
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (occurrence : ResolvedNetworkPort network) :
    occurrence ∈ allResolvedNetworkPorts network := by
  cases occurrence with
  | mk index port =>
      apply List.mem_flatMap.mpr
      refine ⟨index, List.mem_finRange index, ?_⟩
      apply List.mem_map.mpr
      exact ⟨port,
        mem_portsAtResolvedVertex (resolvedVertexAt network index) port,
        rfl⟩

/-! ## 5. Production slab-link specialization -/

/-- Literal port occurrences in the resolved production witness at one
corrected-slab link. -/
abbrev SlabLinkResolvedPort
    (K extent : Nat)
    (physical :
      YMGap.Continuum.CompactDualSlabFineIntertwinerWitness.SlabLabelling)
    (link :
      YMGap.Continuum.CompactDualSlabFineIntertwinerWitness.SlabLink)
    (auxiliary :
      YMGap.Continuum.CompactDualSlabFineIntertwinerWitness.SlabLabelling)
    (hmem : auxiliary ∈
      YMGap.Continuum.CompactDualSlabFineIntertwinerWitness.slabLinkFusionWitnesses
        K extent physical link) :=
  ResolvedNetworkPort
    (slabLinkResolvedStrandNetwork
      K extent physical link auxiliary hmem)

#print axioms vertexEdgeId
#print axioms portsAtResolvedVertex
#print axioms mem_portsAtResolvedVertex
#print axioms portsAtResolvedVertex_length
#print axioms resolvedVertexAt
#print axioms ResolvedNetworkPort
#print axioms ResolvedNetworkPort.vertex
#print axioms ResolvedNetworkPort.leg
#print axioms ResolvedNetworkPort.edgeId
#print axioms ResolvedNetworkPort.slot
#print axioms ResolvedNetworkPortAddress
#print axioms ResolvedNetworkPort.address
#print axioms ResolvedNetworkPort.address_injective
#print axioms resolvedNetworkPortDecidableEq
#print axioms instDecidableEqResolvedNetworkPort
#print axioms ResolvedNetworkPort.slot_lt_edgeLabel
#print axioms ResolvedNetworkPort.localMate
#print axioms ResolvedNetworkPort.localMate_leg_ne
#print axioms ResolvedNetworkPort.localMate_involutive
#print axioms ResolvedNetworkPort.localMate_ne_self
#print axioms allResolvedNetworkPorts
#print axioms ResolvedNetworkPort.mem_all
#print axioms SlabLinkResolvedPort

end YMGap.Continuum.ResolvedTrivalentNetworkPorts
