/-
# Pull physical face-strand selections back through canonical link paths

The global component carrier is physical: a literal face identifier and a
bounded strand slot.  The fusion-preserving compiler, however, consumes a
selection on every strand copy of each resolved link network.  The bridge is
terminal extraction.  A resolved port is selected exactly when the physical
terminal reached by its deterministic canonical path is selected.

The mathematical point is that terminal extraction respects reversal.  For
every resolved port `p`, the terminal reached from `p.localMate` is the
physical partner of the terminal reached from `p`.  The proof reverses the
retained path from `p`, appends terminal extraction from `p.localMate`, and
uses uniqueness of deterministic physical endpoints.  Consequently any
physical selection closed under the partner involution pulls back to a
selection invariant under both local mates and same-slot internal crossings.

Honest scope: this module now proves the local pullback laws, finite
same-copy descent, and coherent fusion removal at one accepted link.  The
seed-generated global component, its exact physical external-label equation,
and the assembly over every slab link remain open.

Constructive contract: retained path reversal, exact endpoint uniqueness,
one- and two-point half-edge fibers, and exhaustive finite descent only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
import YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval

namespace YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalHalfEdgeSwap
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPairing
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Terminal extraction commutes with strand reversal -/

/-- Advancing once along an internal strand does not change its eventual
physical terminal. -/
theorem canonicalLinkStrandTerminal_advance
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (source : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree) :
    canonicalLinkStrandTerminal hdegree hallowed
        (canonicalInternalAdvancePort
          hdegree hallowed source hinternal) =
      canonicalLinkStrandTerminal hdegree hallowed source := by
  let tail := canonicalLinkStrandTerminalWitness hdegree hallowed
    (canonicalInternalAdvancePort hdegree hallowed source hinternal)
  let whole : CanonicalStrandPathToPhysical hdegree hallowed source tail.1 :=
    .advance source hinternal tail.1 tail.2
  exact canonicalStrandPath_terminal_unique whole
    (canonicalLinkStrandTerminalWitness hdegree hallowed source).2

/-- **Terminal reversal identity.**  Starting from the local mate of any
resolved port reaches the partner of the original port's physical terminal.
This is the precise commuting square behind physical-selection pullback. -/
theorem canonicalLinkStrandTerminal_localMate
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (source : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    canonicalLinkStrandTerminal hdegree hallowed source.localMate =
      canonicalPhysicalStrandPartner hdegree hallowed
        (canonicalLinkStrandTerminal hdegree hallowed source) := by
  let sourceWitness :=
    canonicalLinkStrandTerminalWitness hdegree hallowed source
  let mateWitness :=
    canonicalLinkStrandTerminalWitness hdegree hallowed source.localMate
  let reversed : CanonicalInternalAdvancePath hdegree hallowed
      sourceWitness.1.1.localMate source.localMate :=
    canonicalStrandPathReverseToMatePath sourceWitness.2
  let combined : CanonicalInternalAdvancePath hdegree hallowed
      sourceWitness.1.1.localMate mateWitness.1.1 :=
    reversed.append (canonicalStrandPathToAdvancePath mateWitness.2)
  exact canonicalStrandPath_terminal_unique
    (canonicalAdvancePathToPhysical combined mateWitness.1.2)
    (canonicalPhysicalStrandPartner_path
      hdegree hallowed sourceWitness.1)

/-- Raw same-slot crossing of an internal edge reverses the physical
orientation: its terminal is the partner of the source terminal. -/
theorem canonicalLinkStrandTerminal_cross
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (source : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree) :
    canonicalLinkStrandTerminal hdegree hallowed
        (canonicalInternalCrossPort hdegree hallowed source hinternal) =
      canonicalPhysicalStrandPartner hdegree hallowed
        (canonicalLinkStrandTerminal hdegree hallowed source) := by
  let crossed := canonicalInternalCrossPort
    hdegree hallowed source hinternal
  let advanced := canonicalInternalAdvancePort
    hdegree hallowed source hinternal
  have hadvanced : crossed.localMate = advanced := by
    have hmate := canonicalInternalAdvancePort_localMate_eq_cross
      hdegree hallowed source hinternal
    calc
      crossed.localMate = advanced.localMate.localMate :=
        congrArg ResolvedNetworkPort.localMate hmate.symm
      _ = advanced := ResolvedNetworkPort.localMate_involutive advanced
  have hpartnerCross :
      canonicalPhysicalStrandPartner hdegree hallowed
          (canonicalLinkStrandTerminal hdegree hallowed crossed) =
        canonicalLinkStrandTerminal hdegree hallowed source := by
    calc
      canonicalPhysicalStrandPartner hdegree hallowed
          (canonicalLinkStrandTerminal hdegree hallowed crossed) =
          canonicalLinkStrandTerminal hdegree hallowed crossed.localMate :=
        (canonicalLinkStrandTerminal_localMate
          hdegree hallowed crossed).symm
      _ = canonicalLinkStrandTerminal hdegree hallowed advanced := by
        rw [hadvanced]
      _ = canonicalLinkStrandTerminal hdegree hallowed source :=
        canonicalLinkStrandTerminal_advance
          hdegree hallowed source hinternal
  calc
    canonicalLinkStrandTerminal hdegree hallowed crossed =
        canonicalPhysicalStrandPartner hdegree hallowed
          (canonicalPhysicalStrandPartner hdegree hallowed
            (canonicalLinkStrandTerminal hdegree hallowed crossed)) :=
      (canonicalPhysicalStrandPartner_involutive hdegree hallowed _).symm
    _ = canonicalPhysicalStrandPartner hdegree hallowed
          (canonicalLinkStrandTerminal hdegree hallowed source) :=
      congrArg (canonicalPhysicalStrandPartner hdegree hallowed)
        hpartnerCross

/-! ## 2. Pull back any partner-closed physical selection -/

/-- A Boolean choice of physical terminals closed under their exact partner
involution. -/
structure CanonicalPhysicalPartnerClosedSelection
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    Type where
  selected : CanonicalPhysicalStrandPort external auxiliary hallowed -> Bool
  partner_closed : forall terminal,
    selected (canonicalPhysicalStrandPartner
        hdegree hallowed terminal) = selected terminal

/-- Pull physical selection back to an arbitrary resolved port by following
its deterministic strand to the boundary. -/
def CanonicalPhysicalPartnerClosedSelection.atPort
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true}
    (selection :
      CanonicalPhysicalPartnerClosedSelection hdegree hallowed)
    (port : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) : Bool :=
  selection.selected (canonicalLinkStrandTerminal hdegree hallowed port)

/-- The pulled selection is invariant under every local trivalent mate. -/
theorem CanonicalPhysicalPartnerClosedSelection.atPort_localMate
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true}
    (selection :
      CanonicalPhysicalPartnerClosedSelection hdegree hallowed)
    (port : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    selection.atPort port.localMate = selection.atPort port := by
  unfold CanonicalPhysicalPartnerClosedSelection.atPort
  rw [canonicalLinkStrandTerminal_localMate]
  exact selection.partner_closed _

/-- The pulled selection is constant under a full internal advance. -/
theorem CanonicalPhysicalPartnerClosedSelection.atPort_advance
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true}
    (selection :
      CanonicalPhysicalPartnerClosedSelection hdegree hallowed)
    (port : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : port.edgeId ∈ canonicalInternalFusionEdges degree) :
    selection.atPort
        (canonicalInternalAdvancePort hdegree hallowed port hinternal) =
      selection.atPort port := by
  unfold CanonicalPhysicalPartnerClosedSelection.atPort
  rw [canonicalLinkStrandTerminal_advance]

/-- The pulled selection is also invariant under the raw same-slot crossing
of an internal edge.  Thus it depends only on `(edgeId,slot)`, not on which of
the two internal half-edge occurrences is displayed. -/
theorem CanonicalPhysicalPartnerClosedSelection.atPort_cross
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true}
    (selection :
      CanonicalPhysicalPartnerClosedSelection hdegree hallowed)
    (port : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : port.edgeId ∈ canonicalInternalFusionEdges degree) :
    selection.atPort
        (canonicalInternalCrossPort hdegree hallowed port hinternal) =
      selection.atPort port := by
  unfold CanonicalPhysicalPartnerClosedSelection.atPort
  rw [canonicalLinkStrandTerminal_cross]
  exact selection.partner_closed _

/-! ## 3. Same-copy orbit descent and coherent removal -/

/-- **Canonical same-copy orbit lemma.**  Two resolved ports carrying the same
graph-edge strand copy have equal pulled physical selections.

On a physical edge the half-edge fiber has one point.  On an internal edge it
has two points, so the second port is either the first port or its exact
same-slot crossing.  These are precisely the two cases already controlled by
terminal pullback. -/
theorem CanonicalPhysicalPartnerClosedSelection.atPort_eq_of_same_copy
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true}
    (selection :
      CanonicalPhysicalPartnerClosedSelection hdegree hallowed)
    (left right : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hedge : left.edgeId = right.edgeId)
    (hslot : left.slot = right.slot) :
    selection.atPort left = selection.atPort right := by
  match hclass : canonicalResolvedPortClassify
      hdegree hallowed left with
  | .physical hphysical =>
      have hrightPhysical : right.edgeId < degree := by
        rw [← hedge]
        exact hphysical
      have hhalfEdge :=
        canonicalPhysicalTerminals_halfEdge_eq_of_edgeId_eq
          hdegree hallowed
          (⟨left, hphysical⟩ : CanonicalPhysicalStrandPort
            external auxiliary hallowed)
          (⟨right, hrightPhysical⟩ : CanonicalPhysicalStrandPort
            external auxiliary hallowed)
          hedge
      have heq : left = right :=
        resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq hhalfEdge hslot
      rw [heq]
  | .internal hinternal =>
      let network := canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed
      let fiber := canonicalInternalHalfEdgeFiber
        hdegree hallowed hinternal
      have hleftMem : resolvedNetworkPortHalfEdge left ∈
          halfEdgesOnEdge network left.edgeId :=
        (mem_halfEdgesOnEdge_iff _ _).mpr rfl
      have hrightMem : resolvedNetworkPortHalfEdge right ∈
          halfEdgesOnEdge network left.edgeId :=
        (mem_halfEdgesOnEdge_iff _ _).mpr
          ((resolvedNetworkPortHalfEdge_edgeId right).trans hedge.symm)
      rcases fiber.eq_or_eq_swap hleftMem hrightMem with
        hsame | hcross
      · have heq : left = right :=
          resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq
            hsame.symm hslot
        rw [heq]
      · let typed : CanonicalInternalStrandPort
            left.edgeId external auxiliary hallowed := ⟨left, rfl⟩
        let crossed := canonicalInternalStrandContinue
          hdegree hallowed hinternal typed
        have hcrossHalfEdge :
            resolvedNetworkPortHalfEdge crossed.1 =
              fiber.swap (resolvedNetworkPortHalfEdge left) := by
          have hcontinue := congrArg Subtype.val
            (canonicalInternalStrandContinue_halfEdge
              hdegree hallowed hinternal typed)
          simpa [crossed, typed, fiber,
            canonicalInternalStrandHalfEdge,
            canonicalInternalHalfEdgeSwap,
            TwoPointFiber.swapMember] using hcontinue
        have hcrossSlot : crossed.1.slot = left.slot :=
          canonicalInternalStrandContinue_slot
            hdegree hallowed hinternal typed
        have hrightCross : right = crossed.1 :=
          resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq
            (hcross.trans hcrossHalfEdge.symm)
            (hslot.symm.trans hcrossSlot.symm)
        rw [hrightCross]
        exact (selection.atPort_cross left hinternal).symm

/-- The pulled physical selection is therefore a literal occurrence-level
closed selection on the canonical resolved link network. -/
def CanonicalPhysicalPartnerClosedSelection.toPortClosedSelection
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true}
    (selection :
      CanonicalPhysicalPartnerClosedSelection hdegree hallowed) :
    ResolvedNetworkPortClosedSelection
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) where
  selected := selection.atPort
  local_closed := selection.atPort_localMate
  same_copy_closed := selection.atPort_eq_of_same_copy

/-- Partner-closed physical terminal data now compiles all the way to a
coherent simultaneous strand removal on the accepted canonical link. -/
def CanonicalPhysicalPartnerClosedSelection.toCoherentRemoval
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true}
    (selection :
      CanonicalPhysicalPartnerClosedSelection hdegree hallowed) :
    CoherentResolvedTrivalentRemoval
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) :=
  selection.toPortClosedSelection.toCoherentRemoval
    (canonicalLinkResolvedStrandNetwork
      degree external auxiliary hallowed)

/-! ## 4. Literal corrected-slab face-copy selection -/

/-- A global physical face-strand characteristic function whose values agree
on the two endpoints paired by one accepted slab link. -/
structure SlabLinkPartnerClosedFaceSelection
    (cutoff extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link) : Type where
  selected : SlabFaceStrandCopy physical -> Bool
  partner_closed : forall terminal : SlabLinkPhysicalStrandTerminal
      cutoff extent physical link auxiliary hmem,
    selected (slabLinkPhysicalTerminalFaceStrandCopy
        cutoff extent physical link auxiliary hmem
        (slabLinkPhysicalStrandPartner
          cutoff extent physical link auxiliary hmem terminal)) =
      selected (slabLinkPhysicalTerminalFaceStrandCopy
        cutoff extent physical link auxiliary hmem terminal)

/-- Reindex a literal face-copy selection as the canonical terminal selection
used by the generic pullback theorem. -/
def SlabLinkPartnerClosedFaceSelection.toCanonical
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    CanonicalPhysicalPartnerClosedSelection
      (slabIncidentPlaqIds_length_le_six extent link)
      (slabLinkFusionWitness_mem_allowed
        cutoff extent physical link auxiliary hmem) where
  selected := fun terminal =>
    selection.selected (slabLinkPhysicalTerminalFaceStrandCopy
      cutoff extent physical link auxiliary hmem terminal)
  partner_closed := selection.partner_closed

/-- The literal face-copy pullback is invariant under every local mate of the
accepted resolved slab-link network. -/
theorem SlabLinkPartnerClosedFaceSelection.atPort_localMate
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (port : SlabLinkResolvedPort
      cutoff extent physical link auxiliary hmem) :
    selection.toCanonical.atPort port.localMate =
      selection.toCanonical.atPort port :=
  selection.toCanonical.atPort_localMate port

/-- The same literal pullback is invariant under same-slot crossing of every
internal fusion edge. -/
theorem SlabLinkPartnerClosedFaceSelection.atPort_cross
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (port : SlabLinkResolvedPort
      cutoff extent physical link auxiliary hmem)
    (hinternal : port.edgeId ∈ canonicalInternalFusionEdges
      (slabIncidentPlaqIds extent link).length) :
    selection.toCanonical.atPort
        (canonicalInternalCrossPort
          (slabIncidentPlaqIds_length_le_six extent link)
          (slabLinkFusionWitness_mem_allowed
            cutoff extent physical link auxiliary hmem)
          port hinternal) =
      selection.toCanonical.atPort port :=
  selection.toCanonical.atPort_cross port hinternal

/-- The literal slab face-copy pullback compiles to the existing mate-closed
edge-copy selection consumed by fusion preservation. -/
def SlabLinkPartnerClosedFaceSelection.toMateClosedSelection
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    SlabLinkMateClosedSelection hmem :=
  selection.toCanonical.toPortClosedSelection.toMateClosedSelection
    (slabLinkResolvedStrandNetwork
      cutoff extent physical link auxiliary hmem)

/-- **Physical-selection fusion preservation.**  If the target external
labels realize the edge drops extracted from a partner-closed physical
face-copy selection, the lowered auxiliary labelling is an actual accepted
target witness. -/
theorem SlabLinkPartnerClosedFaceSelection.lower_auxiliary_mem
    {cutoff extent : Nat}
    {sourcePhysical targetPhysical : SlabLabelling} {link : SlabLink}
    {sourceAuxiliary : SlabLabelling}
    {hmem : sourceAuxiliary ∈
      slabLinkFusionWitnesses cutoff extent sourcePhysical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent sourcePhysical link sourceAuxiliary hmem)
    (hexternal :
      slabLinkExternalSpins extent targetPhysical link =
        lowerEdgeLabellingBy
          (slabLinkExternalSpins extent sourcePhysical link)
          selection.toMateClosedSelection.drop) :
    lowerEdgeLabellingBy sourceAuxiliary
        selection.toMateClosedSelection.drop ∈
      slabLinkFusionWitnesses cutoff extent targetPhysical link :=
  selection.toMateClosedSelection.lower_auxiliary_mem hexternal

#print axioms canonicalLinkStrandTerminal_advance
#print axioms canonicalLinkStrandTerminal_localMate
#print axioms canonicalLinkStrandTerminal_cross
#print axioms CanonicalPhysicalPartnerClosedSelection
#print axioms CanonicalPhysicalPartnerClosedSelection.atPort
#print axioms CanonicalPhysicalPartnerClosedSelection.atPort_localMate
#print axioms CanonicalPhysicalPartnerClosedSelection.atPort_advance
#print axioms CanonicalPhysicalPartnerClosedSelection.atPort_cross
#print axioms CanonicalPhysicalPartnerClosedSelection.atPort_eq_of_same_copy
#print axioms CanonicalPhysicalPartnerClosedSelection.toPortClosedSelection
#print axioms CanonicalPhysicalPartnerClosedSelection.toCoherentRemoval
#print axioms SlabLinkPartnerClosedFaceSelection
#print axioms SlabLinkPartnerClosedFaceSelection.toCanonical
#print axioms SlabLinkPartnerClosedFaceSelection.atPort_localMate
#print axioms SlabLinkPartnerClosedFaceSelection.atPort_cross
#print axioms SlabLinkPartnerClosedFaceSelection.toMateClosedSelection
#print axioms SlabLinkPartnerClosedFaceSelection.lower_auxiliary_mem

end YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
