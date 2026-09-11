/-
# Global strand edges for heterogeneous certified link presentations

A fusion-tree basis is local to a lattice link.  A global physical strand
graph therefore need not force every link into the production ordering: it is
enough to retain, at each displayed link, a certified face order and an
auxiliary witness accepted in that order.  All local endpoints forget to the
same literal `(faceId, slot)` carrier.

This file packages that observation as a constructive compiler.  It
enumerates every physical terminal in one ordered resolved network, maps the
terminal pairing to global edges, and concatenates those edge lists over a
dependent field of presented link witnesses.  Every local edge has a literal
membership theorem in the resulting global list.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or trusted external computation is used.
-/

import YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge

namespace YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Enumerate the physical terminals and edges in one presentation -/

def orderedSlabLinkPhysicalStrandTerminals
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order) :
    List (OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :=
  let hallowed := orderedSlabLinkFusionWitness_mem_allowed
    K physical order auxiliary hmem
  (allResolvedNetworkPorts
      (canonicalLinkResolvedStrandNetwork
        order.faceIds.length
        (orderedSlabLinkExternalSpins physical order)
        auxiliary hallowed)).filterMap fun occurrence =>
    if hphysical : occurrence.edgeId < order.faceIds.length then
      some ⟨occurrence, hphysical⟩
    else none

/-- The ordered terminal enumeration contains every typed physical terminal. -/
theorem OrderedSlabLinkPhysicalStrandTerminal.mem_all
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    terminal ∈ orderedSlabLinkPhysicalStrandTerminals
      K physical order auxiliary hmem := by
  unfold orderedSlabLinkPhysicalStrandTerminals
  apply List.mem_filterMap.mpr
  refine ⟨terminal.1, terminal.1.mem_all, ?_⟩
  simp only [terminal.2, dite_true]

def orderedSlabLinkFaceStrandEdges
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order) :
    List (SlabFaceStrandEdge physical) :=
  (orderedSlabLinkPhysicalStrandTerminals
    K physical order auxiliary hmem).map
      (orderedSlabLinkFaceStrandEdgeOfTerminal
        K physical order auxiliary hmem)

/-- Every displayed ordered terminal-pair edge occurs in its local edge list. -/
theorem orderedSlabLinkFaceStrandEdgeOfTerminal_mem
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    orderedSlabLinkFaceStrandEdgeOfTerminal
        K physical order auxiliary hmem terminal ∈
      orderedSlabLinkFaceStrandEdges
        K physical order auxiliary hmem := by
  unfold orderedSlabLinkFaceStrandEdges
  exact List.mem_map.mpr
    ⟨terminal,
      OrderedSlabLinkPhysicalStrandTerminal.mem_all
        K physical order auxiliary hmem terminal,
      rfl⟩

/-! ## 2. A dependent presented-link assignment -/

/-- One local fusion witness together with the literal face order in which it
is accepted. -/
structure PresentedSlabLinkFusionWitness
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink) : Type where
  order : SlabLinkFaceOrder extent link
  auxiliary : SlabLabelling
  auxiliary_mem : auxiliary ∈
    orderedSlabLinkFusionWitnesses K physical order

/-- One certified presented witness for every member of a displayed link
list.  The dependency on the attached link prevents mismatched local data. -/
abbrev PresentedSlabFusionWitnessAssignment
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink) :=
  (linked : {link // link ∈ links}) →
    PresentedSlabLinkFusionWitness K extent physical linked.1

/-- Replace one attached link presentation while retaining the supplied
presentations at every other attached link. -/
def presentedSlabFusionWitnessAssignmentReplace
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links)
    (selected : {link // link ∈ links})
    (witness : PresentedSlabLinkFusionWitness
      K extent physical selected.1) :
    PresentedSlabFusionWitnessAssignment K extent physical links :=
  fun linked =>
    if hlink : linked.1 = selected.1 then
      cast (congrArg
        (PresentedSlabLinkFusionWitness K extent physical) hlink.symm)
        witness
    else assignment linked

@[simp] theorem presentedSlabFusionWitnessAssignmentReplace_at
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links)
    (selected : {link // link ∈ links})
    (witness : PresentedSlabLinkFusionWitness
      K extent physical selected.1) :
    presentedSlabFusionWitnessAssignmentReplace
      assignment selected witness selected = witness := by
  simp [presentedSlabFusionWitnessAssignmentReplace]

/-! ## 3. Concatenate the heterogeneous edge lists -/

def presentedSlabFusionWitnessAssignmentFaceStrandEdgesAt
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links)
    (linked : {link // link ∈ links}) :
    List (SlabFaceStrandEdge physical) :=
  let witness := assignment linked
  orderedSlabLinkFaceStrandEdges K physical witness.order
    witness.auxiliary witness.auxiliary_mem

/-- The global physical strand graph of a heterogeneous field of certified
local fusion presentations. -/
def presentedSlabFusionWitnessAssignmentFaceStrandEdges
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links) :
    List (SlabFaceStrandEdge physical) :=
  links.attach.flatMap
    (presentedSlabFusionWitnessAssignmentFaceStrandEdgesAt
      K extent physical links assignment)

/-- Every terminal-pair edge at every attached presented link is literally a
member of the heterogeneous global edge list. -/
theorem presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links)
    (linked : {link // link ∈ links}) :
    let witness := assignment linked
    ∀ terminal : OrderedSlabLinkPhysicalStrandTerminal
        K physical witness.order witness.auxiliary witness.auxiliary_mem,
      orderedSlabLinkFaceStrandEdgeOfTerminal K physical witness.order
          witness.auxiliary witness.auxiliary_mem terminal ∈
        presentedSlabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment := by
  dsimp
  intro terminal
  unfold presentedSlabFusionWitnessAssignmentFaceStrandEdges
  apply List.mem_flatMap.mpr
  refine ⟨linked, List.mem_attach links linked, ?_⟩
  exact orderedSlabLinkFaceStrandEdgeOfTerminal_mem K physical
    (assignment linked).order (assignment linked).auxiliary
    (assignment linked).auxiliary_mem terminal

/-- A separately named local witness can be used after proving that it is the
assignment value at the attached link.  This small transport boundary avoids
unfolding a large proof-indexed assignment in downstream specializations. -/
theorem presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem_of_eq
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links)
    (linked : {link // link ∈ links})
    (witness : PresentedSlabLinkFusionWitness
      K extent physical linked.1)
    (hwitness : assignment linked = witness)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical witness.order witness.auxiliary witness.auxiliary_mem) :
    orderedSlabLinkFaceStrandEdgeOfTerminal K physical witness.order
        witness.auxiliary witness.auxiliary_mem terminal ∈
      presentedSlabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment := by
  cases hwitness
  exact presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
    K extent physical links assignment linked terminal

end YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges.orderedSlabLinkPhysicalStrandTerminals
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges.OrderedSlabLinkPhysicalStrandTerminal.mem_all
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges.orderedSlabLinkFaceStrandEdges
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges.PresentedSlabLinkFusionWitness
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges.PresentedSlabFusionWitnessAssignment
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges.presentedSlabFusionWitnessAssignmentReplace_at
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges.presentedSlabFusionWitnessAssignmentFaceStrandEdges
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges.presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges.presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem_of_eq
