/-
# Physical strand pairing in an arbitrary certified face order

The canonical SU(2) strand machine depends on an ordered external spin word,
whereas a lattice link supplies an unordered incidence set represented by one
production list.  A `SlabLinkFaceOrder` retains any alternative presentation
as literal face identifiers together with a permutation certificate from the
production list.

An auxiliary accepted on the reordered physical spin word therefore drives
the existing canonical terminal and partner compilers unchanged.  Reindexing
those terminals through the certified face order produces literal incident
face copies, and duplicate-freeness proves that every local partner crosses to
a different plaquette.  No recoupling of a distinguished basis witness is
asserted or required.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber

namespace YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkPhysicalTerminalPairing
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Certified presentations of one physical link -/

structure SlabLinkFaceOrder (extent : Nat) (link : SlabLink) : Type where
  faceIds : List Nat
  production_perm :
    (slabIncidentPlaqIds extent link).Perm faceIds

theorem SlabLinkFaceOrder.length_eq
    {extent : Nat} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link) :
    order.faceIds.length = (slabIncidentPlaqIds extent link).length :=
  order.production_perm.length_eq.symm

theorem SlabLinkFaceOrder.length_le_six
    {extent : Nat} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link) :
    order.faceIds.length ≤ 6 := by
  rw [order.length_eq]
  exact slabIncidentPlaqIds_length_le_six extent link

theorem SlabLinkFaceOrder.nodup
    {extent : Nat} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link) :
    order.faceIds.Nodup :=
  order.production_perm.nodup (slabIncidentPlaqIds_nodup extent link)

def orderedSlabLinkExternalSpins
    {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link) :
    SlabLabelling :=
  externalSpinsOfList (order.faceIds.map physical)

def orderedSlabLinkFusionWitnesses
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link) :
    List SlabLabelling :=
  fusionWitnessesForSpins (linkAuxiliaryCutoff K)
    (order.faceIds.map physical)

theorem orderedSlabLinkFusionWitness_mem_allowed
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      orderedSlabLinkFusionWitnesses K physical order) :
    canonicalLinkConditionalAllowedB order.faceIds.length
      (orderedSlabLinkExternalSpins physical order) auxiliary = true := by
  unfold orderedSlabLinkFusionWitnesses fusionWitnessesForSpins at hmem
  simpa only [List.length_map, orderedSlabLinkExternalSpins] using
    (List.mem_filter.mp hmem).2

/-! ## 2. Reordered canonical terminals remain literal face occurrences -/

abbrev OrderedSlabLinkPhysicalStrandTerminal
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      orderedSlabLinkFusionWitnesses K physical order) :=
  CanonicalPhysicalStrandPort
    (orderedSlabLinkExternalSpins physical order) auxiliary
    (orderedSlabLinkFusionWitness_mem_allowed
      K physical order auxiliary hmem)

structure OrderedSlabLinkFaceStrandOccurrence
    {extent : Nat} (physical : SlabLabelling) {link : SlabLink}
    (order : SlabLinkFaceOrder extent link) : Type where
  position : Fin order.faceIds.length
  slot : Fin (physical (order.faceIds.get position))

def OrderedSlabLinkFaceStrandOccurrence.faceId
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {order : SlabLinkFaceOrder extent link}
    (occurrence : OrderedSlabLinkFaceStrandOccurrence physical order) : Nat :=
  order.faceIds.get occurrence.position

theorem OrderedSlabLinkFaceStrandOccurrence.faceId_mem_incident
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {order : SlabLinkFaceOrder extent link}
    (occurrence : OrderedSlabLinkFaceStrandOccurrence physical order) :
    occurrence.faceId ∈ slabIncidentPlaqIds extent link := by
  exact order.production_perm.mem_iff.mpr
    (List.get_mem order.faceIds occurrence.position)

theorem OrderedSlabLinkFaceStrandOccurrence.faceId_physical
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {order : SlabLinkFaceOrder extent link}
    (occurrence : OrderedSlabLinkFaceStrandOccurrence physical order) :
    occurrence.faceId ∈ slabPhysicalFaceEdges extent :=
  slabIncidentPlaqId_physical occurrence.faceId_mem_incident

def orderedSlabLinkPhysicalTerminalOccurrence
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    OrderedSlabLinkFaceStrandOccurrence physical order where
  position := ⟨terminal.1.edgeId, terminal.2⟩
  slot := ⟨terminal.1.slot, by
    have hslot := terminal.1.slot_lt_edgeLabel
    have hoverlay :
        overlayOn (List.range order.faceIds.length)
            (orderedSlabLinkExternalSpins physical order) auxiliary
            terminal.1.edgeId =
          orderedSlabLinkExternalSpins physical order terminal.1.edgeId :=
      overlayOn_apply_of_mem (List.mem_range.mpr terminal.2)
    have hlabel :
        canonicalLinkLabelling order.faceIds.length
            (orderedSlabLinkExternalSpins physical order) auxiliary
            terminal.1.edgeId =
          physical (order.faceIds.get
            ⟨terminal.1.edgeId, terminal.2⟩) := by
      unfold canonicalLinkLabelling
      exact hoverlay.trans
        (externalSpinsOfList_map_get order.faceIds physical
          ⟨terminal.1.edgeId, terminal.2⟩)
    exact Eq.mp (congrArg (fun upper => terminal.1.slot < upper) hlabel)
      hslot⟩

/-! ## 3. The local mate is independent of the chosen face presentation -/

def orderedSlabLinkPhysicalStrandPartner
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      orderedSlabLinkFusionWitnesses K physical order) :
    OrderedSlabLinkPhysicalStrandTerminal K physical order auxiliary hmem →
      OrderedSlabLinkPhysicalStrandTerminal
        K physical order auxiliary hmem :=
  canonicalPhysicalStrandPartner
    (by simpa [linkIncidenceBound] using order.length_le_six)
    (orderedSlabLinkFusionWitness_mem_allowed
      K physical order auxiliary hmem)

theorem orderedSlabLinkPhysicalStrandPartner_involutive
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    orderedSlabLinkPhysicalStrandPartner K physical order auxiliary hmem
        (orderedSlabLinkPhysicalStrandPartner
          K physical order auxiliary hmem terminal) = terminal :=
  canonicalPhysicalStrandPartner_involutive
    (by simpa [linkIncidenceBound] using order.length_le_six)
    (orderedSlabLinkFusionWitness_mem_allowed
      K physical order auxiliary hmem) terminal

theorem orderedSlabLinkPhysicalStrandPartner_position_ne
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    (orderedSlabLinkPhysicalTerminalOccurrence K physical order auxiliary hmem
        (orderedSlabLinkPhysicalStrandPartner
          K physical order auxiliary hmem terminal)).position ≠
      (orderedSlabLinkPhysicalTerminalOccurrence
        K physical order auxiliary hmem terminal).position := by
  intro hposition
  have hedge := congrArg Fin.val hposition
  exact canonicalPhysicalStrandPartner_edgeId_ne
    (by simpa [linkIncidenceBound] using order.length_le_six)
    (orderedSlabLinkFusionWitness_mem_allowed
      K physical order auxiliary hmem) terminal hedge

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

theorem orderedSlabLinkPhysicalStrandPartner_faceId_ne
    (K : Nat) {extent : Nat} {link : SlabLink}
    (physical : SlabLabelling) (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    (orderedSlabLinkPhysicalTerminalOccurrence K physical order auxiliary hmem
        (orderedSlabLinkPhysicalStrandPartner
          K physical order auxiliary hmem terminal)).faceId ≠
      (orderedSlabLinkPhysicalTerminalOccurrence
        K physical order auxiliary hmem terminal).faceId := by
  intro hface
  apply orderedSlabLinkPhysicalStrandPartner_position_ne
    K physical order auxiliary hmem terminal
  exact nodup_get_injective order.nodup _ _ hface

end YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing.SlabLinkFaceOrder.length_le_six
#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing.OrderedSlabLinkFaceStrandOccurrence.faceId_mem_incident
#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing.orderedSlabLinkPhysicalTerminalOccurrence
#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing.orderedSlabLinkPhysicalStrandPartner_involutive
#print axioms
  YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing.orderedSlabLinkPhysicalStrandPartner_faceId_ne
