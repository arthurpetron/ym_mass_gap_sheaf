/-
# Charge sparse presented auxiliary rows to physical peel mass

Every nonzero internal-drop row contains a positive dropped coordinate.  The
canonical strand path from that coordinate reaches a selected physical
terminal on the same link.  Charge the row to that literal physical copy and
link.  A plaquette has four boundary links, while the complete filtered list
of selected physical copies has length exactly equal to the serialized peel
word.  Hence the number of sparse rows is at most four times peel size.

This argument applies directly to a supported selection, including a union of
two components that may coincide or remain disconnected.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
import YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentSparseDropCode

namespace YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. A positive ordered drop reaches a selected physical terminal -/

abbrev OrderedSlabLinkSelectedPhysicalTerminal
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :=
  {terminal : OrderedSlabLinkPhysicalStrandTerminal K physical
      witness.order witness.auxiliary witness.auxiliary_mem //
    selection.selected
      (orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
        witness.order witness.auxiliary witness.auxiliary_mem terminal) = true}

/-- Any positive internal drop computes a selected physical terminal on the
same ordered link. -/
def orderedSlabLinkSelectedPhysicalTerminalOfDropPos
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness)
    (edge : Nat) (hpositive : 0 < selection.drop edge) :
    OrderedSlabLinkSelectedPhysicalTerminal selection := by
  rw [OrderedSlabLinkPartnerClosedFaceSelection.drop_apply selection]
    at hpositive
  let portSelection := selection.toCanonical.toPortClosedSelection
  let label := canonicalLinkLabelling witness.order.faceIds.length
    (orderedSlabLinkExternalSpins physical witness.order) witness.auxiliary
  have hcount : 0 < boolCountFrom
      (portSelection.edgeSlotValue edge) 0 (label edge) := hpositive
  let witnessCount := boolCountFromPositiveWitness
    (portSelection.edgeSlotValue edge) 0 (label edge) hcount
  have hvalue :
      portSelection.edgeSlotValue edge witnessCount.1.val = true := by
    simpa only [Nat.zero_add] using witnessCount.property
  let portWitness :=
    ResolvedNetworkPortClosedSelection.portOfEdgeSlotTrue
      portSelection edge witnessCount.1.val hvalue
  let terminal := canonicalLinkStrandTerminal
    witness.order.length_le_six
    (orderedSlabLinkFusionWitness_mem_allowed K physical witness.order
      witness.auxiliary witness.auxiliary_mem)
    portWitness.1
  refine ⟨terminal, ?_⟩
  change selection.toCanonical.toPortClosedSelection.selected
    portWitness.1 = true
  exact portWitness.property.2.2

/-! ## 2. Compute a selected physical copy from every sparse row -/

structure PresentedSparseAuxiliaryRowPhysicalWitness
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (entry : SlabLink × List Nat) : Type where
  link_mem : entry.1 ∈ links
  selectedTerminal : OrderedSlabLinkSelectedPhysicalTerminal
    (selection.closed.atLink ⟨entry.1, link_mem⟩)

/-- A nonzero sparse row constructively yields a selected physical terminal
on its source link. -/
def presentedSparseAuxiliaryRowPhysicalWitness
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (entry : SlabLink × List Nat)
    (hentry : entry ∈
      (presentedSlabSupportedSelectionSparseDropCode
        selection).auxiliaryWords) :
    PresentedSparseAuxiliaryRowPhysicalWitness selection entry := by
  have hentryRaw : entry ∈ slabSparseAuxiliaryDropWordsFrom links
      (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection) := hentry
  let source := sparseAuxiliaryDropRowSource
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)
    links entry hentryRaw
  let hlink : entry.1 ∈ links := source.link_mem
  let localSelection := selection.closed.atLink ⟨entry.1, hlink⟩
  let coordinates := canonicalUsedAuxiliaryCoordinates
    (assignment ⟨entry.1, hlink⟩).order.faceIds.length
  have hword : entry.2 = coordinates.map localSelection.drop :=
    source.word_eq.trans
      (presentedSlabSupportedSelectionAuxiliaryDropWordAt_of_mem
        selection entry.1 hlink)
  have hnonzero : finiteWordAllZeroB entry.2 = false :=
    presentedSlabSupportedSelectionSparseDropCode_row_nonzero
      selection entry hentry
  have hencodedNonzero :
      finiteWordAllZeroB (coordinates.map localSelection.drop) = false := by
    rw [← hword]
    exact hnonzero
  let indexWitness := finiteWordNonzeroIndexWitness
    (coordinates.map localSelection.drop) hencodedNonzero
  let coordinateIndex : Fin coordinates.length :=
    ⟨indexWitness.1.val, by
      simpa only [List.length_map] using indexWitness.1.isLt⟩
  let edge := coordinates.get coordinateIndex
  have hdropNe : localSelection.drop edge ≠ 0 := by
    simpa [edge, coordinateIndex] using indexWitness.property
  have hdropPos : 0 < localSelection.drop edge := by omega
  exact ⟨hlink,
    orderedSlabLinkSelectedPhysicalTerminalOfDropPos
      localSelection edge hdropPos⟩

def PresentedSparseAuxiliaryRowPhysicalWitness.physicalCopy
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    {selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment}
    {entry : SlabLink × List Nat}
    (witness : PresentedSparseAuxiliaryRowPhysicalWitness selection entry) :
    SlabFaceStrandCopy physical :=
  orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
    (assignment ⟨entry.1, witness.link_mem⟩).order
    (assignment ⟨entry.1, witness.link_mem⟩).auxiliary
    (assignment ⟨entry.1, witness.link_mem⟩).auxiliary_mem
    witness.selectedTerminal.1

theorem PresentedSparseAuxiliaryRowPhysicalWitness.physicalCopy_selected
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    {selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment}
    {entry : SlabLink × List Nat}
    (witness : PresentedSparseAuxiliaryRowPhysicalWitness selection entry) :
    selection.closed.selected witness.physicalCopy = true :=
  witness.selectedTerminal.property

theorem PresentedSparseAuxiliaryRowPhysicalWitness.physicalCopy_faceId_mem_incident
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    {selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment}
    {entry : SlabLink × List Nat}
    (witness : PresentedSparseAuxiliaryRowPhysicalWitness selection entry) :
    witness.physicalCopy.faceId ∈ slabIncidentPlaqIds extent entry.1 := by
  let occurrence := orderedSlabLinkPhysicalTerminalOccurrence K physical
    (assignment ⟨entry.1, witness.link_mem⟩).order
    (assignment ⟨entry.1, witness.link_mem⟩).auxiliary
    (assignment ⟨entry.1, witness.link_mem⟩).auxiliary_mem
    witness.selectedTerminal.1
  exact occurrence.faceId_mem_incident

/-! ## 3. The selected-copy carrier has exactly peel-word length -/

def presentedSelectedPhysicalFaceStrandCopies
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    List (SlabFaceStrandCopy physical) :=
  (slabPhysicalFaceStrandCopies extent physical).filter
    selection.closed.selected

theorem presentedSelectedPhysicalFaceStrandCopies_length_eq_peelFaces
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    (presentedSelectedPhysicalFaceStrandCopies selection).length =
      selection.peelFaces.length := by
  unfold presentedSelectedPhysicalFaceStrandCopies
    slabPhysicalFaceStrandCopies
    PresentedSlabSupportedPartnerClosedFaceSelection.peelFaces
    slabFaceDropList
  exact selectedFaceStrandCopiesFrom_length_eq_dropListFrom
    selection.closed.selected (slabPhysicalFaceEdges extent)

theorem PresentedSparseAuxiliaryRowPhysicalWitness.physicalCopy_mem_selected
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    {selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment}
    {entry : SlabLink × List Nat}
    (witness : PresentedSparseAuxiliaryRowPhysicalWitness selection entry) :
    witness.physicalCopy ∈
      presentedSelectedPhysicalFaceStrandCopies selection := by
  apply List.mem_filter.mpr
  constructor
  · unfold slabPhysicalFaceStrandCopies
    apply List.mem_flatMap.mpr
    refine ⟨witness.physicalCopy.faceId,
      selection.selected_faceId_physical witness.physicalCopy
        witness.physicalCopy_selected, ?_⟩
    unfold faceStrandCopiesAt
    apply List.mem_map.mpr
    exact ⟨witness.physicalCopy.slot,
      List.mem_finRange witness.physicalCopy.slot, by
        cases witness.physicalCopy
        rfl⟩
  · exact witness.physicalCopy_selected

/-! ## 4. Injective row charging and the volume-free bound -/

def presentedSparseDropCodeAttachedRowCharge
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (entry : {row // row ∈
      (presentedSlabSupportedSelectionSparseDropCode
        selection).auxiliaryWords}) :
    SlabFaceStrandCopy physical × SlabLink :=
  ((presentedSparseAuxiliaryRowPhysicalWitness
      selection entry.1 entry.2).physicalCopy,
    entry.1.1)

theorem presentedSparseDropCodeAttachedRowCharge_mem
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (entry : {row // row ∈
      (presentedSlabSupportedSelectionSparseDropCode
        selection).auxiliaryWords}) :
    presentedSparseDropCodeAttachedRowCharge selection entry ∈
      faceStrandCopyBoundaryLinkCarrier extent
        (presentedSelectedPhysicalFaceStrandCopies selection) := by
  let witness := presentedSparseAuxiliaryRowPhysicalWitness
    selection entry.1 entry.2
  apply (mem_faceStrandCopyBoundaryLinkCarrier_iff extent
    (presentedSelectedPhysicalFaceStrandCopies selection)
    (presentedSparseDropCodeAttachedRowCharge selection entry)).mpr
  constructor
  · exact witness.physicalCopy_mem_selected
  · exact link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
      witness.physicalCopy_faceId_mem_incident

theorem presentedSparseDropCodeAttachedRowCharge_injective
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (left right : {row // row ∈
      (presentedSlabSupportedSelectionSparseDropCode
        selection).auxiliaryWords})
    (heq : presentedSparseDropCodeAttachedRowCharge selection left =
      presentedSparseDropCodeAttachedRowCharge selection right) :
    left = right := by
  apply Subtype.ext
  have hkey : left.1.1 = right.1.1 := congrArg Prod.snd heq
  apply Prod.ext hkey
  have hleftWord := sparseAuxiliaryDropRow_word_eq
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)
    links left.1 left.2
  have hrightWord := sparseAuxiliaryDropRow_word_eq
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)
    links right.1 right.2
  rw [hleftWord, hrightWord, hkey]

def presentedSparseDropCodeRowCharges
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    List (SlabFaceStrandCopy physical × SlabLink) :=
  (presentedSlabSupportedSelectionSparseDropCode
    selection).auxiliaryWords.attach.map
      (presentedSparseDropCodeAttachedRowCharge selection)

theorem presentedSparseDropCodeRowCharges_nodup
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (hnodup : links.Nodup) :
    (presentedSparseDropCodeRowCharges selection).Nodup := by
  apply nodup_map_of_injOn
    (presentedSparseDropCodeAttachedRowCharge selection)
  · apply attach_nodup_of_nodup
    unfold presentedSlabSupportedSelectionSparseDropCode
    exact slabSparseAuxiliaryDropWordsFrom_nodup
      (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)
      links hnodup
  · intro left hleft right hright heq
    exact presentedSparseDropCodeAttachedRowCharge_injective
      selection left right heq

/-- **Volume-independent presented sparse-row bound.**  Every retained row is
charged injectively to one of four boundary links of one selected physical
copy. -/
theorem presentedSlabSupportedSelectionSparseDropCode_auxiliaryWords_length_le_four_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (hnodup : links.Nodup) :
    (presentedSlabSupportedSelectionSparseDropCode
        selection).auxiliaryWords.length <=
      4 * selection.peelFaces.length := by
  have hbound := nodup_subset_length_le
    (presentedSparseDropCodeRowCharges selection)
    (faceStrandCopyBoundaryLinkCarrier extent
      (presentedSelectedPhysicalFaceStrandCopies selection))
    (presentedSparseDropCodeRowCharges_nodup selection hnodup)
    (fun charge hcharge => by
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hcharge
      exact presentedSparseDropCodeAttachedRowCharge_mem selection entry)
  rw [presentedSparseDropCodeRowCharges, List.length_map,
    List.length_attach,
    faceStrandCopyBoundaryLinkCarrier_length extent
      (presentedSelectedPhysicalFaceStrandCopies selection),
    presentedSelectedPhysicalFaceStrandCopies_length_eq_peelFaces selection]
    at hbound
  exact hbound

end YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.orderedSlabLinkSelectedPhysicalTerminalOfDropPos
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.presentedSparseAuxiliaryRowPhysicalWitness
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.presentedSelectedPhysicalFaceStrandCopies_length_eq_peelFaces
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.presentedSparseDropCodeRowCharges_nodup
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.presentedSlabSupportedSelectionSparseDropCode_auxiliaryWords_length_le_four_mul_peelFaces
