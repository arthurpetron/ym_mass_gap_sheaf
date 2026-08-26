/-
# Physical face-strand pairing at one accepted corrected-slab link

The canonical fusion tree uses local physical identifiers `0, ..., degree-1`.
For the corrected slab those identifiers are precisely positions in the
literal list of plaquette faces incident on one lattice link.  This module
performs that final reindexing.

A `SlabLinkFaceStrandOccurrence` is the mathematical object needed by global
component extraction: an incident physical face together with one copy below
its actual twice-spin label.  Every canonical physical terminal maps to such
an occurrence.  The terminal partner is then proved to land on a different
literal face, so a local peel removes paired strands from two genuinely
different incident plaquettes.

Constructive contract: bounded list lookup, the explicit accepted link
witness, and the proved canonical terminal pairing only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkPhysicalTerminalPairing

namespace YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkPhysicalTerminalPairing
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Literal face-copy occurrences at one slab link -/

/-- One copy of one actual physical face at a specified incident link. -/
structure SlabLinkFaceStrandOccurrence
    (extent : Nat) (physical : SlabLabelling) (link : SlabLink) : Type where
  position : Fin (slabIncidentPlaqIds extent link).length
  slot : Fin (physical ((slabIncidentPlaqIds extent link).get position))
  deriving DecidableEq

/-- The literal numerical plaquette identifier carried by an occurrence. -/
def SlabLinkFaceStrandOccurrence.faceId
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (occurrence : SlabLinkFaceStrandOccurrence extent physical link) : Nat :=
  (slabIncidentPlaqIds extent link).get occurrence.position

/-- Every displayed face-copy occurrence really is incident on its link. -/
theorem SlabLinkFaceStrandOccurrence.faceId_mem_incident
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (occurrence : SlabLinkFaceStrandOccurrence extent physical link) :
    occurrence.faceId ∈ slabIncidentPlaqIds extent link :=
  List.get_mem _ occurrence.position

/-- Hence every displayed incident face is in the slab physical carrier. -/
theorem SlabLinkFaceStrandOccurrence.faceId_physical
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (occurrence : SlabLinkFaceStrandOccurrence extent physical link) :
    occurrence.faceId ∈ slabPhysicalFaceEdges extent :=
  slabIncidentPlaqId_physical occurrence.faceId_mem_incident

/-! ## 2. Reindex accepted canonical terminals by literal faces -/

/-- Totalized external-spin lookup agrees with bounded list lookup. -/
theorem externalSpinsOfList_map_get
    (ids : List Nat) (physical : EdgeLabelling)
    (position : Fin ids.length) :
    externalSpinsOfList (ids.map physical) position.val =
      physical (ids.get position) := by
  unfold externalSpinsOfList
  rw [List.getD_eq_getElem?_getD]
  have hposition : position.val < (ids.map physical).length := by
    rw [List.length_map]
    exact position.isLt
  rw [List.getElem?_eq_getElem hposition]
  simp

/-- The canonical physical terminal type specialized to one literal accepted
corrected-slab link witness. -/
abbrev SlabLinkPhysicalStrandTerminal
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :=
  CanonicalPhysicalStrandPort
    (slabLinkExternalSpins extent physical link) auxiliary
    (slabLinkFusionWitness_mem_allowed
      K extent physical link auxiliary hmem)

/-- Forget the fusion-tree address of a terminal and retain its literal
incident face and strand-copy number. -/
def slabLinkPhysicalTerminalOccurrence
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    SlabLinkFaceStrandOccurrence extent physical link where
  position := ⟨terminal.1.edgeId, terminal.2⟩
  slot := ⟨terminal.1.slot, by
    have hslot := terminal.1.slot_lt_edgeLabel
    have hoverlay :
        overlayOn (List.range (slabIncidentPlaqIds extent link).length)
            (slabLinkExternalSpins extent physical link) auxiliary
            terminal.1.edgeId =
          slabLinkExternalSpins extent physical link terminal.1.edgeId :=
      overlayOn_apply_of_mem (List.mem_range.mpr terminal.2)
    have hlabel :
        canonicalLinkLabelling
            (slabIncidentPlaqIds extent link).length
            (slabLinkExternalSpins extent physical link) auxiliary
            terminal.1.edgeId =
          physical ((slabIncidentPlaqIds extent link).get
            ⟨terminal.1.edgeId, terminal.2⟩) := by
      unfold canonicalLinkLabelling
      exact hoverlay.trans
        (externalSpinsOfList_map_get
          (slabIncidentPlaqIds extent link) physical
          ⟨terminal.1.edgeId, terminal.2⟩)
    exact Eq.mp
      (congrArg (fun upper => terminal.1.slot < upper) hlabel)
      hslot⟩

/-! ## 3. The accepted link pairing joins different literal faces -/

/-- Bounded lookup in a duplicate-free list is injective.  The witness is
proved directly by structural induction so no finite choice is hidden in the
reindexing from local terminal positions to physical face identifiers. -/
private theorem nodup_get_injective {A : Type} [DecidableEq A] :
    ∀ {entries : List A}, entries.Nodup →
      ∀ left right : Fin entries.length,
        entries.get left = entries.get right → left = right
  | [], _, left, _, _ => Fin.elim0 left
  | head :: tail, hnodup, left, right, hget => by
      have hparts := List.nodup_cons.mp hnodup
      cases left using Fin.cases with
      | zero =>
        cases right using Fin.cases with
        | zero => rfl
        | succ rightTail =>
          change head = tail.get rightTail at hget
          have hmem := List.get_mem tail rightTail
          rw [← hget] at hmem
          exact False.elim (hparts.1 hmem)
      | succ leftTail =>
        cases right using Fin.cases with
        | zero =>
          change tail.get leftTail = head at hget
          have hmem := List.get_mem tail leftTail
          rw [hget] at hmem
          exact False.elim (hparts.1 hmem)
        | succ rightTail =>
          change tail.get leftTail = tail.get rightTail at hget
          exact congrArg Fin.succ
            (nodup_get_injective hparts.2 leftTail rightTail hget)

/-- The actual accepted-link terminal operation. -/
def slabLinkPhysicalStrandPartner
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    SlabLinkPhysicalStrandTerminal K extent physical link auxiliary hmem →
      SlabLinkPhysicalStrandTerminal K extent physical link auxiliary hmem :=
  canonicalPhysicalStrandPartner
    (slabIncidentPlaqIds_length_le_six extent link)
    (slabLinkFusionWitness_mem_allowed
      K extent physical link auxiliary hmem)

/-- The accepted-link partner remains involutive. -/
theorem slabLinkPhysicalStrandPartner_involutive
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    slabLinkPhysicalStrandPartner K extent physical link auxiliary hmem
        (slabLinkPhysicalStrandPartner
          K extent physical link auxiliary hmem terminal) = terminal :=
  canonicalPhysicalStrandPartner_involutive
    (slabIncidentPlaqIds_length_le_six extent link)
    (slabLinkFusionWitness_mem_allowed
      K extent physical link auxiliary hmem)
    terminal

/-- The accepted-link partner has a different local incident-list position. -/
theorem slabLinkPhysicalStrandPartner_position_ne
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    (slabLinkPhysicalTerminalOccurrence K extent physical link auxiliary hmem
        (slabLinkPhysicalStrandPartner
          K extent physical link auxiliary hmem terminal)).position ≠
      (slabLinkPhysicalTerminalOccurrence
        K extent physical link auxiliary hmem terminal).position := by
  intro hposition
  have hedge := congrArg Fin.val hposition
  exact canonicalPhysicalStrandPartner_edgeId_ne
    (slabIncidentPlaqIds_length_le_six extent link)
    (slabLinkFusionWitness_mem_allowed
      K extent physical link auxiliary hmem)
    terminal hedge

/-- The local pairing therefore joins two different literal plaquette faces.
This is the exact global-gluing invariant: a selected strand crosses a link
from one incident physical face to another. -/
theorem slabLinkPhysicalStrandPartner_faceId_ne
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    (slabLinkPhysicalTerminalOccurrence K extent physical link auxiliary hmem
        (slabLinkPhysicalStrandPartner
          K extent physical link auxiliary hmem terminal)).faceId ≠
      (slabLinkPhysicalTerminalOccurrence
        K extent physical link auxiliary hmem terminal).faceId := by
  intro hface
  apply slabLinkPhysicalStrandPartner_position_ne
    K extent physical link auxiliary hmem terminal
  exact nodup_get_injective
    (slabIncidentPlaqIds_nodup extent link) _ _ hface

#print axioms SlabLinkFaceStrandOccurrence
#print axioms SlabLinkFaceStrandOccurrence.faceId_mem_incident
#print axioms SlabLinkFaceStrandOccurrence.faceId_physical
#print axioms externalSpinsOfList_map_get
#print axioms SlabLinkPhysicalStrandTerminal
#print axioms slabLinkPhysicalTerminalOccurrence
#print axioms slabLinkPhysicalStrandPartner
#print axioms slabLinkPhysicalStrandPartner_involutive
#print axioms slabLinkPhysicalStrandPartner_position_ne
#print axioms slabLinkPhysicalStrandPartner_faceId_ne

end YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
