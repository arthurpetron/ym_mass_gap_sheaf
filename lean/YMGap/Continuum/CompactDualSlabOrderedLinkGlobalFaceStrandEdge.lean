/-
# Global face-strand edges from an arbitrary certified link presentation

The production global strand graph uses only literal physical face-copy
vertices.  Those vertices do not depend on the local ordering chosen to
resolve a link.  This file therefore forgets an ordered terminal's fusion-tree
address while retaining its actual `(faceId, slot)` copy, then packages a
terminal and its canonical partner as the same global edge type already used
by component extraction.

This does not identify a reordered auxiliary witness with a production-order
witness.  It supplies the presentation-independent geometric edge needed for
the later heterogeneous global assignment compiler.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or trusted external computation is used.
-/

import YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
import YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing

namespace YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPairing
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff

/-! ## 1. Forget an ordered local address to a global face copy -/

/-- Face identifier and natural slot value determine a dependent global
face-copy record. -/
theorem slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
    {physical : SlabLabelling} (left right : SlabFaceStrandCopy physical)
    (hface : left.faceId = right.faceId)
    (hslot : left.slot.val = right.slot.val) :
    left = right := by
  cases left with
  | mk leftFace leftSlot =>
      cases right with
      | mk rightFace rightSlot =>
          dsimp only [SlabFaceStrandCopy.faceId,
            SlabFaceStrandCopy.slot] at hface hslot
          subst rightFace
          congr
          exact Fin.ext hslot

/-- The global copy directly named by a certified face position and bounded
physical strand slot. -/
def orderedSlabLinkPhysicalCopyAt
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link)
    (position : Fin order.faceIds.length)
    (slot : Fin (physical (order.faceIds.get position))) :
    SlabFaceStrandCopy physical where
  faceId := order.faceIds.get position
  slot := slot

def orderedSlabLinkFaceStrandOccurrenceToCopy
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {order : SlabLinkFaceOrder extent link}
    (occurrence : OrderedSlabLinkFaceStrandOccurrence physical order) :
    SlabFaceStrandCopy physical where
  faceId := occurrence.faceId
  slot := occurrence.slot

def orderedSlabLinkPhysicalTerminalFaceStrandCopy
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    SlabFaceStrandCopy physical :=
  orderedSlabLinkFaceStrandOccurrenceToCopy
    (orderedSlabLinkPhysicalTerminalOccurrence
      K physical order auxiliary hmem terminal)

/-- Constructing a terminal at a specified ordered face copy and then
forgetting its fusion-tree address recovers that exact global copy. -/
theorem orderedSlabLinkPhysicalTerminalAtFaceStrandCopy
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (position : Fin order.faceIds.length)
    (slot : Fin (physical (order.faceIds.get position))) :
    orderedSlabLinkPhysicalTerminalFaceStrandCopy
        K physical order auxiliary hmem
          (orderedSlabLinkPhysicalTerminalAt
            K physical order auxiliary hmem position slot) =
      orderedSlabLinkPhysicalCopyAt order position slot := by
  apply slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
  · exact orderedSlabLinkPhysicalTerminalAt_occurrence_faceId
      K physical order auxiliary hmem position slot
  · exact orderedSlabLinkPhysicalTerminalAt_occurrence_slot
      K physical order auxiliary hmem position slot

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

/-- Forgetting an ordered physical terminal to its literal global face copy
is injective.  Duplicate-freeness recovers the physical edge position, and
the singleton physical half-edge fiber plus the slot recovers the port. -/
theorem orderedSlabLinkPhysicalTerminalFaceStrandCopy_injective
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (left right : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem)
    (hcopy :
      orderedSlabLinkPhysicalTerminalFaceStrandCopy
          K physical order auxiliary hmem left =
        orderedSlabLinkPhysicalTerminalFaceStrandCopy
          K physical order auxiliary hmem right) :
    left = right := by
  have hface := congrArg SlabFaceStrandCopy.faceId hcopy
  change order.faceIds.get ⟨left.1.edgeId, left.2⟩ =
    order.faceIds.get ⟨right.1.edgeId, right.2⟩ at hface
  have hposition := nodup_get_injective order.nodup _ _ hface
  have hedge : left.1.edgeId = right.1.edgeId := congrArg Fin.val hposition
  have hslot := congrArg (fun copy => copy.slot.val) hcopy
  change left.1.slot = right.1.slot at hslot
  apply Subtype.ext
  apply resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq
  · exact canonicalPhysicalTerminals_halfEdge_eq_of_edgeId_eq
      (by simpa [linkIncidenceBound] using order.length_le_six)
      (orderedSlabLinkFusionWitness_mem_allowed
        K physical order auxiliary hmem)
      left right hedge
  · exact hslot

@[simp] theorem orderedSlabLinkPhysicalTerminalFaceStrandCopy_faceId
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    (orderedSlabLinkPhysicalTerminalFaceStrandCopy
      K physical order auxiliary hmem terminal).faceId =
        order.faceIds.get ⟨terminal.1.edgeId, terminal.2⟩ :=
  rfl

@[simp] theorem orderedSlabLinkPhysicalTerminalFaceStrandCopy_slot_val
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    (orderedSlabLinkPhysicalTerminalFaceStrandCopy
      K physical order auxiliary hmem terminal).slot.val =
        terminal.1.slot :=
  rfl

/-! ## 2. Package the ordered partner as a global edge -/

/-- A terminal and its partner in any certified face presentation define a
directed edge on the common global physical-copy carrier. -/
def orderedSlabLinkFaceStrandEdgeOfTerminal
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    SlabFaceStrandEdge physical where
  link := link
  source := orderedSlabLinkPhysicalTerminalFaceStrandCopy
    K physical order auxiliary hmem terminal
  target := orderedSlabLinkPhysicalTerminalFaceStrandCopy
    K physical order auxiliary hmem
      (orderedSlabLinkPhysicalStrandPartner
        K physical order auxiliary hmem terminal)
  faceId_ne := (orderedSlabLinkPhysicalStrandPartner_faceId_ne
    K physical order auxiliary hmem terminal).symm

@[simp] theorem orderedSlabLinkFaceStrandEdgeOfTerminal_link
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    (orderedSlabLinkFaceStrandEdgeOfTerminal
      K physical order auxiliary hmem terminal).link = link :=
  rfl

@[simp] theorem orderedSlabLinkFaceStrandEdgeOfTerminal_source
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    (orderedSlabLinkFaceStrandEdgeOfTerminal
      K physical order auxiliary hmem terminal).source =
        orderedSlabLinkPhysicalTerminalFaceStrandCopy
          K physical order auxiliary hmem terminal :=
  rfl

@[simp] theorem orderedSlabLinkFaceStrandEdgeOfTerminal_target
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    (orderedSlabLinkFaceStrandEdgeOfTerminal
      K physical order auxiliary hmem terminal).target =
        orderedSlabLinkPhysicalTerminalFaceStrandCopy
          K physical order auxiliary hmem
            (orderedSlabLinkPhysicalStrandPartner
              K physical order auxiliary hmem terminal) :=
  rfl

end YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge.slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge.orderedSlabLinkFaceStrandOccurrenceToCopy
#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge.orderedSlabLinkPhysicalTerminalFaceStrandCopy
#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge.orderedSlabLinkPhysicalTerminalAtFaceStrandCopy
#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge.orderedSlabLinkPhysicalTerminalFaceStrandCopy_injective
#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge.orderedSlabLinkFaceStrandEdgeOfTerminal
