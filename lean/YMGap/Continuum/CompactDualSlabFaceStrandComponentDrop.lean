/-
# A rooted face-strand component gives the exact physical link drop

For a Boolean selection of literal physical face-strand copies, define the
drop of a face to be the number of its selected slots.  The preceding
component theorem supplies such a selection and the Kirchhoff compiler counts
the same Boolean values on canonical-link edge copies.

This module proves the commuting equality between those two counts.  The
proof observes each physical edge through its unique half-edge and rebuilds
the typed port at the requested bounded slot.  Exactness of finite descent
then identifies the compiler value with the original face-copy value.  There
is no new graph search or representation-level hypothesis.

The resulting target physical labelling makes the external-label equation
definitionally correct at every link.  Consequently every rooted global
component constructs an actually accepted lowered auxiliary witness at every
displayed link.

Constructive contract: finite Boolean counting, the explicit one-half-edge
physical fiber, and bounded ports only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkInternalHalfEdgeSwap
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. The global observable: selected copies on one physical face -/

/-- Totalize a face-copy selection outside the actual bounded slot range. -/
def slabFaceStrandSelectionAt
    {physical : SlabLabelling}
    (selected : SlabFaceStrandCopy physical -> Bool)
    (faceId slot : Nat) : Bool :=
  if hslot : slot < physical faceId then
    selected { faceId := faceId, slot := ⟨slot, hslot⟩ }
  else false

/-- On an actual bounded face copy, totalization returns the original
selection value. -/
@[simp] theorem slabFaceStrandSelectionAt_fin
    {physical : SlabLabelling}
    (selected : SlabFaceStrandCopy physical -> Bool)
    (faceId : Nat) (slot : Fin (physical faceId)) :
    slabFaceStrandSelectionAt selected faceId slot.val =
      selected { faceId := faceId, slot := slot } := by
  simp [slabFaceStrandSelectionAt, slot.isLt]

/-- The exact number of selected strand copies carried by one physical face. -/
def slabFaceStrandSelectionCount
    {physical : SlabLabelling}
    (selected : SlabFaceStrandCopy physical -> Bool)
    (faceId : Nat) : Nat :=
  boolCountFrom (slabFaceStrandSelectionAt selected faceId)
    0 (physical faceId)

/-- A face loses no more copies than it carries. -/
theorem slabFaceStrandSelectionCount_le
    {physical : SlabLabelling}
    (selected : SlabFaceStrandCopy physical -> Bool)
    (faceId : Nat) :
    slabFaceStrandSelectionCount selected faceId <= physical faceId :=
  boolCountFrom_le _ _ _

/-- Lower every physical face by its exact selected-copy count. -/
def lowerSlabPhysicalByFaceStrandSelection
    {physical : SlabLabelling}
    (selected : SlabFaceStrandCopy physical -> Bool) : SlabLabelling :=
  lowerEdgeLabellingBy physical (slabFaceStrandSelectionCount selected)

/-! ## 2. Observe a physical canonical edge at an arbitrary bounded slot -/

/-- The unique displayed half-edge over one physical canonical identifier.
This witness is private: it exists only to compare the two finite counts. -/
private def canonicalPhysicalHalfEdgeAt
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree <= linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (edge : Fin degree) :
    ResolvedNetworkHalfEdge
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) := by
  let network := canonicalLinkResolvedStrandNetwork
    degree external auxiliary hallowed
  let fiber := halfEdgesOnEdge network edge.val
  have hlength : fiber.length = 1 :=
    canonicalLinkResolved_halfEdgesOnEdge_length_physical
      hdegree hallowed edge.isLt
  exact fiber.get ⟨0, by rw [hlength]; omega⟩

private theorem canonicalPhysicalHalfEdgeAt_edgeId
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree <= linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (edge : Fin degree) :
    (canonicalPhysicalHalfEdgeAt hdegree hallowed edge).edgeId = edge.val := by
  apply (mem_halfEdgesOnEdge_iff _ _).mp
  exact List.get_mem _ _

/-- A typed observation of one bounded slot on a physical canonical edge. -/
private structure CanonicalPhysicalSlotObservation
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true}
    (edge : Fin degree)
    (slot : Fin (canonicalLinkLabelling
      degree external auxiliary edge.val)) : Type where
  terminal : CanonicalPhysicalStrandPort external auxiliary hallowed
  edgeId_eq : terminal.1.edgeId = edge.val
  slot_eq : terminal.1.slot = slot.val

/-- Construct the observation from the exact one-half-edge physical fiber. -/
private def canonicalPhysicalSlotObservation
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree <= linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (edge : Fin degree)
    (slot : Fin (canonicalLinkLabelling
      degree external auxiliary edge.val)) :
    CanonicalPhysicalSlotObservation (hallowed := hallowed) edge slot := by
  let halfEdge := canonicalPhysicalHalfEdgeAt hdegree hallowed edge
  have hedge : halfEdge.edgeId = edge.val :=
    canonicalPhysicalHalfEdgeAt_edgeId hdegree hallowed edge
  have hslot : slot.val < canonicalLinkLabelling
      degree external auxiliary halfEdge.edgeId := by
    rw [hedge]
    exact slot.isLt
  let port := resolvedNetworkHalfEdgePortAt halfEdge slot.val hslot
  have hportEdge : port.edgeId = edge.val := by
    rw [resolvedNetworkHalfEdgePortAt_edgeId, hedge]
  have hportSlot : port.slot = slot.val :=
    resolvedNetworkHalfEdgePortAt_slot halfEdge slot.val hslot
  have hphysical : port.edgeId < degree := by
    rw [hportEdge]
    exact edge.isLt
  exact
    { terminal := ⟨port, hphysical⟩
      edgeId_eq := hportEdge
      slot_eq := hportSlot }

/-! ## 3. The same physical slot is seen by the global and local carriers -/

/-- The canonical link labelling at a bounded physical position is the
literal spin of the incident face at that position. -/
theorem slabLinkCanonicalLabel_at_position
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    (position : Fin (slabIncidentPlaqIds extent link).length) :
    canonicalLinkLabelling
        (slabIncidentPlaqIds extent link).length
        (slabLinkExternalSpins extent physical link) auxiliary position.val =
      physical ((slabIncidentPlaqIds extent link).get position) := by
  unfold canonicalLinkLabelling
  rw [overlayOn_apply_of_mem (List.mem_range.mpr position.isLt)]
  exact externalSpinsOfList_map_get
    (slabIncidentPlaqIds extent link) physical position

/-- Reindex one literal physical-face slot as a bounded canonical-link slot. -/
private def slabLinkCanonicalSlotAt
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    (position : Fin (slabIncidentPlaqIds extent link).length)
    (slot : Fin (physical
      ((slabIncidentPlaqIds extent link).get position))) :
    Fin (canonicalLinkLabelling
      (slabIncidentPlaqIds extent link).length
      (slabLinkExternalSpins extent physical link) auxiliary position.val) :=
  ⟨slot.val, by
    rw [slabLinkCanonicalLabel_at_position position]
    exact slot.isLt⟩

private theorem slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
    {physical : SlabLabelling}
    {left right : SlabFaceStrandCopy physical}
    (hface : left.faceId = right.faceId)
    (hslot : left.slot.val = right.slot.val) :
    left = right := by
  cases left with
  | mk leftFace leftSlot =>
      cases right with
      | mk rightFace rightSlot =>
          dsimp at hface hslot
          subst rightFace
          congr 1
          exact Fin.ext hslot

private theorem slabLinkPhysicalSlotObservation_copy
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (position : Fin (slabIncidentPlaqIds extent link).length)
    (slot : Fin (physical
      ((slabIncidentPlaqIds extent link).get position)))
    (observation : CanonicalPhysicalSlotObservation
      (hallowed := slabLinkFusionWitness_mem_allowed
        cutoff extent physical link auxiliary hmem)
      position (slabLinkCanonicalSlotAt
        (auxiliary := auxiliary) position slot)) :
    slabLinkPhysicalTerminalFaceStrandCopy
        cutoff extent physical link auxiliary hmem
        observation.terminal =
      { faceId := (slabIncidentPlaqIds extent link).get position
        slot := slot } := by
  have hposition :
      (⟨observation.terminal.1.edgeId, observation.terminal.2⟩ :
        Fin (slabIncidentPlaqIds extent link).length) = position := by
    apply Fin.ext
    exact observation.edgeId_eq
  apply slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
  · rw [slabLinkPhysicalTerminalFaceStrandCopy_faceId]
    exact congrArg (List.get (slabIncidentPlaqIds extent link)) hposition
  · rw [slabLinkPhysicalTerminalFaceStrandCopy_slot_val]
    simpa [slabLinkCanonicalSlotAt] using observation.slot_eq

/-- At a physical port, terminal pullback observes exactly the corresponding
literal global face copy. -/
private theorem SlabLinkPartnerClosedFaceSelection.atPort_physical
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (position : Fin (slabIncidentPlaqIds extent link).length)
    (slot : Fin (physical
      ((slabIncidentPlaqIds extent link).get position)))
    (observation : CanonicalPhysicalSlotObservation
      (hallowed := slabLinkFusionWitness_mem_allowed
        cutoff extent physical link auxiliary hmem)
      position (slabLinkCanonicalSlotAt
        (auxiliary := auxiliary) position slot)) :
    selection.toCanonical.atPort
        observation.terminal.1 =
      selection.selected
        { faceId := (slabIncidentPlaqIds extent link).get position
          slot := slot } := by
  have hterminal :
      canonicalLinkStrandTerminal
          (slabIncidentPlaqIds_length_le_six extent link)
          (slabLinkFusionWitness_mem_allowed
            cutoff extent physical link auxiliary hmem)
          observation.terminal.1 = observation.terminal :=
    canonicalStrandPath_terminal_unique
      (canonicalLinkStrandTerminalWitness
        (slabIncidentPlaqIds_length_le_six extent link)
        (slabLinkFusionWitness_mem_allowed
          cutoff extent physical link auxiliary hmem)
        observation.terminal.1).2
      (CanonicalStrandPathToPhysical.stop observation.terminal)
  unfold CanonicalPhysicalPartnerClosedSelection.atPort
  rw [hterminal]
  change selection.selected
      (slabLinkPhysicalTerminalFaceStrandCopy
        cutoff extent physical link auxiliary hmem
        observation.terminal) = _
  rw [slabLinkPhysicalSlotObservation_copy
    (position := position) (slot := slot) observation]

/-! ## 4. The commuting count and accepted lower witness -/

/-- **Pointwise physical observation.**  Finite edge-copy descent at one
bounded physical slot returns the original literal face-copy selection. -/
theorem SlabLinkPartnerClosedFaceSelection.edgeSlotValue_at_position_slot
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (position : Fin (slabIncidentPlaqIds extent link).length)
    (slot : Fin (physical
      ((slabIncidentPlaqIds extent link).get position))) :
    selection.toCanonical.toPortClosedSelection.edgeSlotValue
        position.val slot.val =
      selection.selected
        { faceId := (slabIncidentPlaqIds extent link).get position
          slot := slot } := by
  let canonicalSlot := slabLinkCanonicalSlotAt
    (auxiliary := auxiliary) position slot
  let observation := canonicalPhysicalSlotObservation
    (slabIncidentPlaqIds_length_le_six extent link)
    (slabLinkFusionWitness_mem_allowed
      cutoff extent physical link auxiliary hmem)
    position canonicalSlot
  have hexact :=
    selection.toCanonical.toPortClosedSelection.edgeSlotValue_at_port
      observation.terminal.1
  have hvalue := SlabLinkPartnerClosedFaceSelection.atPort_physical
    (cutoff := cutoff) (extent := extent) (physical := physical)
    (link := link) (auxiliary := auxiliary) (hmem := hmem)
    selection position slot observation
  calc
    selection.toCanonical.toPortClosedSelection.edgeSlotValue
        position.val slot.val =
        selection.toCanonical.toPortClosedSelection.edgeSlotValue
          observation.terminal.1.edgeId
          observation.terminal.1.slot := by
      rw [observation.edgeId_eq, observation.slot_eq]
      simp [canonicalSlot, slabLinkCanonicalSlotAt]
    _ = selection.toCanonical.atPort observation.terminal.1 := hexact
    _ = selection.selected
        { faceId := (slabIncidentPlaqIds extent link).get position
          slot := slot } := hvalue

/-- **External-drop commuting equality.**  On every literal incident-face
position, the Kirchhoff compiler's edge drop equals the number of selected
copies on that physical face. -/
theorem SlabLinkPartnerClosedFaceSelection.drop_at_position
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (position : Fin (slabIncidentPlaqIds extent link).length) :
    selection.drop position.val =
      slabFaceStrandSelectionCount selection.selected
        ((slabIncidentPlaqIds extent link).get position) := by
  unfold SlabLinkPartnerClosedFaceSelection.drop
    slabFaceStrandSelectionCount
  rw [slabLinkCanonicalLabel_at_position position]
  apply boolCountFrom_congr
  intro offset hoffset
  simp only [Nat.zero_add]
  let slot : Fin (physical
      ((slabIncidentPlaqIds extent link).get position)) :=
    ⟨offset, hoffset⟩
  change selection.toCanonical.toPortClosedSelection.edgeSlotValue
      position.val offset =
    slabFaceStrandSelectionAt selection.selected
      ((slabIncidentPlaqIds extent link).get position) offset
  calc
    selection.toCanonical.toPortClosedSelection.edgeSlotValue
        position.val offset = selection.selected
        { faceId := (slabIncidentPlaqIds extent link).get position
          slot := slot } :=
      SlabLinkPartnerClosedFaceSelection.edgeSlotValue_at_position_slot
        selection position slot
    _ = slabFaceStrandSelectionAt selection.selected
        ((slabIncidentPlaqIds extent link).get position) offset := by
      symm
      exact slabFaceStrandSelectionAt_fin _ _ slot

private theorem externalSpinsOfList_eq_zero_of_length_le
    (spins : List Nat) (position : Nat) (hlength : spins.length <= position) :
    externalSpinsOfList spins position = 0 := by
  unfold externalSpinsOfList
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none hlength]
  rfl

/-- Lowering physical faces by the selected-copy count realizes exactly the
compiled external-edge drop on the whole totalized canonical link labelling. -/
theorem SlabLinkPartnerClosedFaceSelection.externalSpins_lowerPhysical
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    slabLinkExternalSpins extent
        (lowerSlabPhysicalByFaceStrandSelection selection.selected) link =
      lowerEdgeLabellingBy
        (slabLinkExternalSpins extent physical link)
        selection.drop := by
  funext edge
  by_cases hedge : edge < (slabIncidentPlaqIds extent link).length
  · let position : Fin (slabIncidentPlaqIds extent link).length :=
      ⟨edge, hedge⟩
    unfold slabLinkExternalSpins
    rw [externalSpinsOfList_map_get
      (slabIncidentPlaqIds extent link)
      (lowerSlabPhysicalByFaceStrandSelection selection.selected)
      position]
    change
      lowerSlabPhysicalByFaceStrandSelection selection.selected
          ((slabIncidentPlaqIds extent link).get position) =
        externalSpinsOfList
            ((slabIncidentPlaqIds extent link).map physical) edge -
          selection.drop edge
    rw [externalSpinsOfList_map_get
      (slabIncidentPlaqIds extent link) physical position]
    rw [SlabLinkPartnerClosedFaceSelection.drop_at_position
      selection position]
    rfl
  · have hlength : (slabIncidentPlaqIds extent link).length <= edge := by
      omega
    unfold slabLinkExternalSpins lowerEdgeLabellingBy
    rw [externalSpinsOfList_eq_zero_of_length_le _ edge (by
      simpa using hlength)]
    rw [externalSpinsOfList_eq_zero_of_length_le _ edge (by
      simpa using hlength)]
    exact (Nat.zero_sub _).symm

/-- The global rooted component's canonical target physical labelling. -/
def SlabFusionWitnessFaceStrandSeed.lowerPhysical
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : SlabLabelling :=
  lowerSlabPhysicalByFaceStrandSelection seed.selected

/-- **Local accepted component peel.**  At every displayed link, one rooted
global strand component constructs the literal accepted lowered auxiliary
witness for the single common target physical labelling. -/
theorem SlabFusionWitnessFaceStrandSeed.lower_auxiliary_mem_atLink
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (linked : {link // link ∈ links}) :
    let auxiliary := slabFusionWitnessAssignmentAt linked.1 assignment
    lowerEdgeLabellingBy auxiliary
        (seed.atLinkSelection linked).drop ∈
      slabLinkFusionWitnesses
        K extent (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
          linked.1 := by
  dsimp
  let selection := seed.atLinkSelection linked
  rw [← selection.toMateClosedSelection_drop]
  exact selection.lower_auxiliary_mem (by
    rw [selection.toMateClosedSelection_drop]
    exact SlabLinkPartnerClosedFaceSelection.externalSpins_lowerPhysical
      selection)

#print axioms slabFaceStrandSelectionAt
#print axioms slabFaceStrandSelectionAt_fin
#print axioms slabFaceStrandSelectionCount
#print axioms slabFaceStrandSelectionCount_le
#print axioms lowerSlabPhysicalByFaceStrandSelection
#print axioms slabLinkCanonicalLabel_at_position
#print axioms SlabLinkPartnerClosedFaceSelection.edgeSlotValue_at_position_slot
#print axioms SlabLinkPartnerClosedFaceSelection.drop_at_position
#print axioms SlabLinkPartnerClosedFaceSelection.externalSpins_lowerPhysical
#print axioms SlabFusionWitnessFaceStrandSeed.lowerPhysical
#print axioms SlabFusionWitnessFaceStrandSeed.lower_auxiliary_mem_atLink

end YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
