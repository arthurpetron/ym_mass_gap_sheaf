/-
# A fixed observable face supplies a canonical rooted strand component

The component entropy theorem is useful for a volume-uniform estimate only
when its root is fixed by the observable.  A source-dependent search over all
nonzero faces would introduce a slab-volume factor.  This module instead fixes
one literal physical face and, whenever that face carries a positive strand,
constructs the slot-zero copy as an actual vertex of the global strand graph.

The construction is completely explicit.  It chooses the first boundary link
of the face plaquette, finds the face's numerical position in that link's
incident-face list, constructs the unique physical half-edge at slot zero, and
uses the corresponding displayed global strand edge to certify vertex
membership.  The resulting seed has the requested face identifier and slot
definitionally; no root enumeration or choice is used.

Constructive contract: finite list indexing and the already explicit physical
half-edge observation only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop

namespace YMGap.Continuum.CompactDualSlabObservableRootSeed

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Deterministic incidence data for one physical face -/

/-- The first genuine boundary link of the selected slab plaquette. -/
def slabObservableRootLink (extent faceId : Nat) : SlabLink :=
  ((slabPlaquetteAt extent faceId).1,
    (dirsOf (slabPlaquetteAt extent faceId).2).1)

/-- The selected link is literally one of the four plaquette boundary links. -/
theorem slabObservableRootLink_mem_edgesOf (extent faceId : Nat) :
    slabObservableRootLink extent faceId ∈
      edgesOf (slabPlaquetteAt extent faceId) := by
  simp [slabObservableRootLink, edgesOf]

/-- A physical slab face's selected link belongs to the complete slab link
carrier. -/
theorem slabObservableRootLink_mem_complete
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    slabObservableRootLink extent faceId ∈
      boundaryCompleteSlabLinks extent := by
  apply (mem_boundaryCompleteSlabLinks_iff extent _).mpr
  exact ⟨slabPlaquetteAt extent faceId,
    slabPlaquetteAt_mem hface,
    slabObservableRootLink_mem_edgesOf extent faceId⟩

/-- The selected face identifier occurs in the incident-face list of its
selected boundary link. -/
theorem slabObservableRootFace_mem_incident
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    faceId ∈ slabIncidentPlaqIds extent
      (slabObservableRootLink extent faceId) := by
  apply mem_slabIncidentPlaqIds.mpr
  exact ⟨slabPlaquetteAt extent faceId,
    slabPlaquetteAt_mem_enumerate hface,
    slabObservableRootLink_mem_edgesOf extent faceId⟩

/-- The computable first position of the selected face in its chosen link's
incident-face list. -/
def slabObservableRootPosition
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    Fin (slabIncidentPlaqIds extent
      (slabObservableRootLink extent faceId)).length :=
  ⟨listIndexOf faceId
      (slabIncidentPlaqIds extent
        (slabObservableRootLink extent faceId)),
    listIndexOf_lt_of_mem faceId _
      (slabObservableRootFace_mem_incident hface)⟩

/-- Looking up the computable incident position returns exactly the selected
face identifier. -/
theorem slabObservableRootPosition_get
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    (slabIncidentPlaqIds extent
      (slabObservableRootLink extent faceId)).get
        (slabObservableRootPosition hface) = faceId := by
  let ids := slabIncidentPlaqIds extent
    (slabObservableRootLink extent faceId)
  let index := listIndexOf faceId ids
  have hmem : faceId ∈ ids := slabObservableRootFace_mem_incident hface
  have hlt : index < ids.length := listIndexOf_lt_of_mem faceId ids hmem
  have hgetD : ids.getD index faceId = faceId :=
    getD_listIndexOf_of_mem faceId faceId ids hmem
  change ids[index] = faceId
  rw [List.getElem_eq_getD (l := ids) (i := index) (h := hlt) faceId]
  exact hgetD

/-! ## 2. The fixed slot-zero global root -/

/-- Slot zero on one positive physical face. -/
def slabObservableRootCopy
    {physical : SlabLabelling} (faceId : Nat)
    (hpositive : 0 < physical faceId) : SlabFaceStrandCopy physical where
  faceId := faceId
  slot := ⟨0, hpositive⟩

/-- The fixed slot-zero observable copy is a displayed vertex of every
accepted complete global fusion assignment. -/
theorem slabObservableRootCopy_mem_vertices
    (cutoff extent faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (physical : SlabLabelling)
    (hpositive : 0 < physical faceId)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent)) :
    slabObservableRootCopy faceId hpositive ∈
      slabFaceStrandVertices
        (slabFusionWitnessAssignmentFaceStrandEdges
          cutoff extent physical (boundaryCompleteSlabLinks extent)
          assignment hassignment) := by
  let link := slabObservableRootLink extent faceId
  have hlink : link ∈ boundaryCompleteSlabLinks extent :=
    slabObservableRootLink_mem_complete hface
  let linked : {candidate // candidate ∈ boundaryCompleteSlabLinks extent} :=
    ⟨link, hlink⟩
  let auxiliary := slabFusionWitnessAssignmentAt link assignment
  have hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link :=
    slabFusionWitnessAssignmentAt_mem_local
      cutoff extent physical (boundaryCompleteSlabLinks extent)
      assignment hassignment link hlink
  let position := slabObservableRootPosition hface
  let slot : Fin (physical
      ((slabIncidentPlaqIds extent link).get position)) :=
    ⟨0, by
      rw [slabObservableRootPosition_get hface]
      exact hpositive⟩
  let canonicalSlot := slabLinkCanonicalSlotAt
    (auxiliary := auxiliary) position slot
  let observation := canonicalPhysicalSlotObservation
    (slabIncidentPlaqIds_length_le_six extent link)
    (slabLinkFusionWitness_mem_allowed
      cutoff extent physical link auxiliary hmem)
    position canonicalSlot
  let edge := slabLinkFaceStrandEdgeOfTerminal
    cutoff extent physical link auxiliary hmem observation.terminal
  have hedge : edge ∈
      slabFusionWitnessAssignmentFaceStrandEdges
        cutoff extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment := by
    exact slabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
      cutoff extent physical (boundaryCompleteSlabLinks extent)
      assignment hassignment linked observation.terminal
  have hsource : edge.source ∈
      slabFaceStrandVertices
        (slabFusionWitnessAssignmentFaceStrandEdges
          cutoff extent physical (boundaryCompleteSlabLinks extent)
          assignment hassignment) :=
    slabFaceStrandEdge_source_mem_vertices hedge
  have hcopy : edge.source =
      { faceId := (slabIncidentPlaqIds extent link).get position
        slot := slot } := by
    exact slabLinkPhysicalSlotObservation_copy
      (cutoff := cutoff) (extent := extent) (physical := physical)
      (link := link) (auxiliary := auxiliary) (hmem := hmem)
      position slot observation
  have hroot : edge.source = slabObservableRootCopy faceId hpositive := by
    apply slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
    · rw [hcopy]
      exact slabObservableRootPosition_get hface
    · rw [hcopy]
      rfl
  rw [← hroot]
  exact hsource

/-- Every positive value at the fixed observable face therefore gives a
canonical rooted component with no sum over possible roots. -/
def slabObservableRootSeed
    (cutoff extent faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (physical : SlabLabelling)
    (hpositive : 0 < physical faceId)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent)) :
    SlabFusionWitnessFaceStrandSeed cutoff extent physical
      (boundaryCompleteSlabLinks extent) assignment hassignment where
  root := slabObservableRootCopy faceId hpositive
  root_mem := slabObservableRootCopy_mem_vertices
    cutoff extent faceId hface physical hpositive assignment hassignment

@[simp] theorem slabObservableRootSeed_faceId
    (cutoff extent faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (physical : SlabLabelling)
    (hpositive : 0 < physical faceId)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent)) :
    (slabObservableRootSeed cutoff extent faceId hface physical hpositive
      assignment hassignment).root.faceId = faceId := rfl

@[simp] theorem slabObservableRootSeed_slot
    (cutoff extent faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (physical : SlabLabelling)
    (hpositive : 0 < physical faceId)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent)) :
    (slabObservableRootSeed cutoff extent faceId hface physical hpositive
      assignment hassignment).root.slot.val = 0 := rfl

#print axioms slabObservableRootLink
#print axioms slabObservableRootLink_mem_edgesOf
#print axioms slabObservableRootLink_mem_complete
#print axioms slabObservableRootFace_mem_incident
#print axioms slabObservableRootPosition
#print axioms slabObservableRootPosition_get
#print axioms slabObservableRootCopy
#print axioms slabObservableRootCopy_mem_vertices
#print axioms slabObservableRootSeed
#print axioms slabObservableRootSeed_faceId
#print axioms slabObservableRootSeed_slot

end YMGap.Continuum.CompactDualSlabObservableRootSeed
