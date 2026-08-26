/-
# Global physical face-strand edges of one corrected-slab fusion assignment

The preceding local theorem pairs literal physical face copies at one
accepted link.  A complete corrected-slab fusion witness is an explicit list
of one accepted auxiliary labelling for every physical link.  This module
turns that global witness into the finite edge list needed by component
extraction.

The construction has three mathematical layers:

1. computably look up the auxiliary labelling carried by the assignment at a
   selected link and prove that it is accepted there;
2. enumerate every physical terminal of that accepted canonical link network;
3. map each terminal and its partner to a directed edge between two distinct
   actual `(faceId, strand-copy)` vertices, then concatenate over all links.

The directed list contains both orientations of a local pair.  This harmless
redundancy makes symmetry manifest and will be removed, if useful, only after
the connected-component theorem.  No analytic estimate is asserted here.

Constructive contract: recursion on the literal assignment and finite port
lists only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing

namespace YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. A computable accepted local lookup in a global assignment -/

/-- Total lookup of a link's auxiliary labelling in a global assignment.
Membership in the Cartesian assignment list below proves that the default
branch is never semantically used at a requested listed link. -/
def slabFusionWitnessAssignmentAt (link : SlabLink) :
    SlabFusionWitnessAssignment → SlabLabelling
  | [] => zeroEdgeLabelling
  | entry :: rest =>
      if entry.1 = link then entry.2
      else slabFusionWitnessAssignmentAt link rest

/-- A member of the Cartesian global-assignment list returns an accepted
local auxiliary labelling at every requested link.  The returned data are
computed by `slabFusionWitnessAssignmentAt`; the membership proof is used only
to certify acceptance. -/
theorem slabFusionWitnessAssignmentAt_mem_local
    (K extent : Nat) (physical : SlabLabelling) :
    ∀ (links : List SlabLink) (assignment : SlabFusionWitnessAssignment),
      assignment ∈
          slabFusionWitnessAssignmentsOn K extent physical links →
      ∀ link, link ∈ links →
        slabFusionWitnessAssignmentAt link assignment ∈
          slabLinkFusionWitnesses K extent physical link
  | [], _, _, link, hlink => False.elim (List.not_mem_nil hlink)
  | head :: rest, assignment, hassignment, link, hlink => by
      obtain ⟨selected, hselected, hselectedBlock⟩ :=
        List.mem_flatMap.mp hassignment
      obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hselectedBlock
      by_cases hsame : head = link
      · subst link
        simpa [slabFusionWitnessAssignmentAt] using hselected
      · have hrest : link ∈ rest := by
          rcases List.mem_cons.mp hlink with hhead | hrest
          · exact False.elim (hsame hhead.symm)
          · exact hrest
        simp only [slabFusionWitnessAssignmentAt, hsame, if_false]
        exact slabFusionWitnessAssignmentAt_mem_local
          K extent physical rest tail htail link hrest

/-! ## 2. Enumerate every physical terminal at one accepted link -/

/-- Every physical terminal in one accepted slab-link network, obtained by
filtering the already-complete resolved-port enumeration. -/
def slabLinkPhysicalStrandTerminals
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    List (SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :=
  let hallowed := slabLinkFusionWitness_mem_allowed
    K extent physical link auxiliary hmem
  (allResolvedNetworkPorts
      (canonicalLinkResolvedStrandNetwork
        (slabIncidentPlaqIds extent link).length
        (slabLinkExternalSpins extent physical link)
        auxiliary hallowed)).filterMap fun occurrence =>
    if hphysical : occurrence.edgeId <
        (slabIncidentPlaqIds extent link).length then
      some ⟨occurrence, hphysical⟩
    else none

/-- The terminal enumeration is exhaustive. -/
theorem SlabLinkPhysicalStrandTerminal.mem_all
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    terminal ∈ slabLinkPhysicalStrandTerminals
      K extent physical link auxiliary hmem := by
  unfold slabLinkPhysicalStrandTerminals
  apply List.mem_filterMap.mpr
  refine ⟨terminal.1, terminal.1.mem_all, ?_⟩
  simp only [terminal.2, dite_true]

/-! ## 3. Literal global face-copy vertices and local edges -/

/-- A physical face identifier together with one copy below its actual
twice-spin label.  Physical-carrier membership is proved for edge endpoints;
keeping it out of the structure avoids irrelevant proof transports in graph
equality. -/
structure SlabFaceStrandCopy (physical : SlabLabelling) : Type where
  faceId : Nat
  slot : Fin (physical faceId)
  deriving DecidableEq

/-- Forget the incident-link position while retaining the actual face copy. -/
def slabLinkFaceStrandOccurrenceToCopy
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (occurrence : SlabLinkFaceStrandOccurrence extent physical link) :
    SlabFaceStrandCopy physical where
  faceId := occurrence.faceId
  slot := occurrence.slot

/-- The copy obtained from a terminal at an accepted link. -/
def slabLinkPhysicalTerminalFaceStrandCopy
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    SlabFaceStrandCopy physical :=
  slabLinkFaceStrandOccurrenceToCopy
    (slabLinkPhysicalTerminalOccurrence
      K extent physical link auxiliary hmem terminal)

/-- A directed physical strand edge records the lattice link that performs
the pairing and two endpoints on different plaquette faces. -/
structure SlabFaceStrandEdge (physical : SlabLabelling) : Type where
  link : SlabLink
  source : SlabFaceStrandCopy physical
  target : SlabFaceStrandCopy physical
  faceId_ne : source.faceId ≠ target.faceId

/-- One terminal and its partner give one directed global face-strand edge. -/
def slabLinkFaceStrandEdgeOfTerminal
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    SlabFaceStrandEdge physical where
  link := link
  source := slabLinkPhysicalTerminalFaceStrandCopy
    K extent physical link auxiliary hmem terminal
  target := slabLinkPhysicalTerminalFaceStrandCopy
    K extent physical link auxiliary hmem
      (slabLinkPhysicalStrandPartner
        K extent physical link auxiliary hmem terminal)
  faceId_ne := (slabLinkPhysicalStrandPartner_faceId_ne
    K extent physical link auxiliary hmem terminal).symm

/-- All directed physical strand edges contributed by one accepted link. -/
def slabLinkFaceStrandEdges
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    List (SlabFaceStrandEdge physical) :=
  (slabLinkPhysicalStrandTerminals
    K extent physical link auxiliary hmem).map
      (slabLinkFaceStrandEdgeOfTerminal
        K extent physical link auxiliary hmem)

/-- Every displayed terminal-pair edge occurs in the literal local edge
list. -/
theorem slabLinkFaceStrandEdgeOfTerminal_mem
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    slabLinkFaceStrandEdgeOfTerminal
        K extent physical link auxiliary hmem terminal ∈
      slabLinkFaceStrandEdges
        K extent physical link auxiliary hmem := by
  unfold slabLinkFaceStrandEdges
  exact List.mem_map.mpr
    ⟨terminal,
      SlabLinkPhysicalStrandTerminal.mem_all
        K extent physical link auxiliary hmem terminal,
      rfl⟩

/-! ## 4. Concatenate the edge lists over a complete assignment -/

/-- The physical face-strand edges contributed by one link of a complete
assignment.  Factoring this dependent lookup away from the outer list
concatenation keeps the construction transparent: first certify one local
pairing, then assemble the finite family. -/
def slabFusionWitnessAssignmentFaceStrandEdgesAt
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (linked : {link // link ∈ links}) :
    List (SlabFaceStrandEdge physical) :=
  let auxiliary := slabFusionWitnessAssignmentAt linked.1 assignment
  let hmem := slabFusionWitnessAssignmentAt_mem_local
    K extent physical links assignment hassignment linked.1 linked.2
  slabLinkFaceStrandEdges
    K extent physical linked.1 auxiliary hmem

/-- The complete directed physical face-strand edge list over any displayed
link list and any member of its Cartesian fusion-witness assignment list. -/
def slabFusionWitnessAssignmentFaceStrandEdges
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links) :
    List (SlabFaceStrandEdge physical) :=
  links.attach.flatMap
    (slabFusionWitnessAssignmentFaceStrandEdgesAt
      K extent physical links assignment hassignment)

/-- Every terminal-pair edge of every displayed link is literally present in
the concatenated global assignment edge list. -/
theorem slabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (linked : {link // link ∈ links}) :
    let auxiliary := slabFusionWitnessAssignmentAt linked.1 assignment
    let hmem := slabFusionWitnessAssignmentAt_mem_local
      K extent physical links assignment hassignment linked.1 linked.2
    ∀ terminal : SlabLinkPhysicalStrandTerminal
        K extent physical linked.1 auxiliary hmem,
      slabLinkFaceStrandEdgeOfTerminal
          K extent physical linked.1 auxiliary hmem terminal ∈
        slabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment hassignment := by
  dsimp
  intro terminal
  unfold slabFusionWitnessAssignmentFaceStrandEdges
  apply List.mem_flatMap.mpr
  refine ⟨linked, List.mem_attach links linked, ?_⟩
  exact slabLinkFaceStrandEdgeOfTerminal_mem
    K extent physical linked.1
      (slabFusionWitnessAssignmentAt linked.1 assignment)
      (slabFusionWitnessAssignmentAt_mem_local
        K extent physical links assignment hassignment linked.1 linked.2)
      terminal

/-- Specialization to one literal member of the production corrected-slab
global fusion-witness list. -/
def slabFineFusionWitnessFaceStrandEdges
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical) :
    List (SlabFaceStrandEdge physical) :=
  slabFusionWitnessAssignmentFaceStrandEdges
    D.cutoff D.extent physical (boundaryCompleteSlabLinks D.extent)
    assignment hassignment

#print axioms slabFusionWitnessAssignmentAt
#print axioms slabFusionWitnessAssignmentAt_mem_local
#print axioms slabLinkPhysicalStrandTerminals
#print axioms SlabLinkPhysicalStrandTerminal.mem_all
#print axioms SlabFaceStrandCopy
#print axioms slabLinkFaceStrandOccurrenceToCopy
#print axioms slabLinkPhysicalTerminalFaceStrandCopy
#print axioms SlabFaceStrandEdge
#print axioms slabLinkFaceStrandEdgeOfTerminal
#print axioms slabLinkFaceStrandEdges
#print axioms slabLinkFaceStrandEdgeOfTerminal_mem
#print axioms slabFusionWitnessAssignmentFaceStrandEdgesAt
#print axioms slabFusionWitnessAssignmentFaceStrandEdges
#print axioms slabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
#print axioms slabFineFusionWitnessFaceStrandEdges

end YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
