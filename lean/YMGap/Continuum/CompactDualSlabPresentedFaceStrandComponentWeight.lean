/-
# Serialize and pay a supported presented strand selection

A heterogeneous presented assignment uses an independently certified face
order at each lattice link.  Its global strand graph still lives on literal
physical face copies.  This file proves that every such graph endpoint is a
displayed physical face, packages a globally partner-closed selection with an
explicit support certificate, and serializes its exact face-copy multiplicity
as a legal repeated face peel.

The resulting path has a physical left inverse and receives the existing
cutoff-independent anchor heat payment.  The auxiliary coordinates and face
orders are retained in the presented source and lowered target; serializing
their internal drops into the finite inverse code remains downstream.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
import YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
import YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction

namespace YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Every presented graph endpoint is a physical face copy -/

theorem orderedSlabLinkFaceStrandEdgeOfTerminal_endpoints_physical
    (K : Nat) {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ orderedSlabLinkFusionWitnesses K physical order)
    (terminal : OrderedSlabLinkPhysicalStrandTerminal
      K physical order auxiliary hmem) :
    let edge := orderedSlabLinkFaceStrandEdgeOfTerminal
      K physical order auxiliary hmem terminal
    edge.source.faceId ∈ slabPhysicalFaceEdges extent ∧
      edge.target.faceId ∈ slabPhysicalFaceEdges extent := by
  dsimp only
  constructor
  · change (orderedSlabLinkPhysicalTerminalOccurrence
      K physical order auxiliary hmem terminal).faceId ∈
        slabPhysicalFaceEdges extent
    exact OrderedSlabLinkFaceStrandOccurrence.faceId_physical _
  · change (orderedSlabLinkPhysicalTerminalOccurrence
      K physical order auxiliary hmem
        (orderedSlabLinkPhysicalStrandPartner
          K physical order auxiliary hmem terminal)).faceId ∈
        slabPhysicalFaceEdges extent
    exact OrderedSlabLinkFaceStrandOccurrence.faceId_physical _

/-- Both endpoints of every edge in a heterogeneous presented graph lie on
displayed physical faces. -/
theorem presentedSlabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links)
    {edge : SlabFaceStrandEdge physical}
    (hedge : edge ∈
      presentedSlabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment) :
    edge.source.faceId ∈ slabPhysicalFaceEdges extent ∧
      edge.target.faceId ∈ slabPhysicalFaceEdges extent := by
  unfold presentedSlabFusionWitnessAssignmentFaceStrandEdges at hedge
  obtain ⟨linked, _, hedge⟩ := List.mem_flatMap.mp hedge
  unfold presentedSlabFusionWitnessAssignmentFaceStrandEdgesAt at hedge
  unfold orderedSlabLinkFaceStrandEdges at hedge
  obtain ⟨terminal, _, hedgeEq⟩ := List.mem_map.mp hedge
  rw [← hedgeEq]
  exact orderedSlabLinkFaceStrandEdgeOfTerminal_endpoints_physical
    K (assignment linked).order (assignment linked).auxiliary
    (assignment linked).auxiliary_mem terminal

/-- Every copy in a constructive component of a presented global graph is
supported on a displayed physical face. -/
theorem PresentedSlabFusionWitnessFaceStrandSeed.component_faceId_physical
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (copy : SlabFaceStrandCopy physical) (hcopy : copy ∈ seed.component) :
    copy.faceId ∈ slabPhysicalFaceEdges extent := by
  have hvertex : copy ∈ slabFaceStrandVertices
      (presentedSlabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment) :=
    rootComponent_subset
      (slabFaceStrandAdjacentB
        (presentedSlabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment))
      seed.root_mem hcopy
  obtain ⟨edge, hedge, hendpoint⟩ := List.mem_flatMap.mp hvertex
  have hphysical :=
    presentedSlabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
      K extent physical links assignment hedge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hendpoint
  rcases hendpoint with hsource | htarget
  · rw [hsource]
    exact hphysical.1
  · rw [htarget]
    exact hphysical.2

/-! ## 2. A supported common partner-closed selection -/

/-- A common presented selection together with the proof that every selected
copy belongs to the displayed physical face carrier. -/
structure PresentedSlabSupportedPartnerClosedFaceSelection
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links) : Type where
  closed : PresentedSlabPartnerClosedFaceSelection
    K extent physical links assignment
  selected_faceId_physical :
    ∀ copy : SlabFaceStrandCopy physical,
      closed.selected copy = true →
        copy.faceId ∈ slabPhysicalFaceEdges extent

/-- The union of two rooted presented components is both partner closed and
physically supported. -/
def PresentedSlabSupportedPartnerClosedFaceSelection.ofSeedUnion
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (left right : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment) :
    PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment where
  closed := PresentedSlabPartnerClosedFaceSelection.ofSeedUnion left right
  selected_faceId_physical := by
    intro copy hselected
    unfold PresentedSlabPartnerClosedFaceSelection.ofSeedUnion at hselected
    dsimp only at hselected
    rcases (Bool.or_eq_true _ _).mp hselected with hleft | hright
    · apply PresentedSlabFusionWitnessFaceStrandSeed.component_faceId_physical
        left copy
      unfold SlabFaceStrandSeed.selected at hleft
      exact of_decide_eq_true hleft
    · apply PresentedSlabFusionWitnessFaceStrandSeed.component_faceId_physical
        right copy
      unfold SlabFaceStrandSeed.selected at hright
      exact of_decide_eq_true hright

private theorem boolCountFrom_false (start : Nat) : ∀ length : Nat,
    boolCountFrom (fun _ => false) start length = 0
  | 0 => rfl
  | length + 1 => by
      rw [boolCountFrom]
      simp only [boolIndicator, Nat.zero_add]
      exact boolCountFrom_false (start + 1) length

/-- Physical support forces zero selected-copy count away from the displayed
face carrier. -/
theorem PresentedSlabSupportedPartnerClosedFaceSelection.selectionCount_eq_zero_of_not_physical
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (faceId : Nat) (hface : faceId ∉ slabPhysicalFaceEdges extent) :
    slabFaceStrandSelectionCount selection.closed.selected faceId = 0 := by
  unfold slabFaceStrandSelectionCount
  have hcount := boolCountFrom_congr
    (slabFaceStrandSelectionAt selection.closed.selected faceId)
    (fun _ => false) 0 0 (physical faceId) (by
      intro offset hoffset
      let copy : SlabFaceStrandCopy physical :=
        { faceId := faceId, slot := ⟨offset, hoffset⟩ }
      have hfalse : selection.closed.selected copy = false := by
        cases hvalue : selection.closed.selected copy with
        | false => rfl
        | true =>
            exact False.elim
              (hface (selection.selected_faceId_physical copy hvalue))
      simp only [Nat.zero_add]
      change slabFaceStrandSelectionAt selection.closed.selected
          faceId offset = false
      simp [slabFaceStrandSelectionAt, hoffset, copy, hfalse])
  exact hcount.trans (boolCountFrom_false 0 (physical faceId))

/-! ## 3. Exact physical serialization, path, and left inverse -/

def PresentedSlabSupportedPartnerClosedFaceSelection.peelFaces
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) : List Nat :=
  slabFaceDropList extent
    (slabFaceStrandSelectionCount selection.closed.selected)

theorem PresentedSlabSupportedPartnerClosedFaceSelection.peelFaces_count
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (faceId : Nat) :
    selection.peelFaces.count faceId =
      slabFaceStrandSelectionCount selection.closed.selected faceId := by
  by_cases hface : faceId ∈ slabPhysicalFaceEdges extent
  · unfold PresentedSlabSupportedPartnerClosedFaceSelection.peelFaces
    exact slabFaceDropList_count_of_mem extent
      (slabFaceStrandSelectionCount selection.closed.selected) hface
  · unfold PresentedSlabSupportedPartnerClosedFaceSelection.peelFaces
    rw [slabFaceDropList_count_of_not_mem extent
      (slabFaceStrandSelectionCount selection.closed.selected) hface]
    exact (selection.selectionCount_eq_zero_of_not_physical
      faceId hface).symm

private theorem two_le_length_of_two_distinct_members
    {A : Type} [DecidableEq A] (items : List A) (left right : A)
    (hleft : left ∈ items) (hright : right ∈ items) (hne : left ≠ right) :
    2 <= items.length := by
  cases items with
  | nil => cases hleft
  | cons head tail =>
      cases tail with
      | nil =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hleft hright
          exact False.elim (hne (hleft.trans hright.symm))
      | cons next rest =>
          simp only [List.length_cons]
          omega

/-- Two selected copies on distinct physical faces force at least two letters
in the exact serialized peel word. -/
theorem PresentedSlabSupportedPartnerClosedFaceSelection.two_le_peelFaces_length_of_selected_faceId_ne
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (left right : SlabFaceStrandCopy physical)
    (hleft : selection.closed.selected left = true)
    (hright : selection.closed.selected right = true)
    (hne : left.faceId ≠ right.faceId) :
    2 <= selection.peelFaces.length := by
  have hleftPos := slabFaceStrandSelectionCount_pos_of_selected
    selection.closed.selected left hleft
  have hrightPos := slabFaceStrandSelectionCount_pos_of_selected
    selection.closed.selected right hright
  have hleftMem : left.faceId ∈ selection.peelFaces := by
    by_cases hmem : left.faceId ∈ selection.peelFaces
    · exact hmem
    · have hzero := List.count_eq_zero.mpr hmem
      rw [selection.peelFaces_count left.faceId] at hzero
      omega
  have hrightMem : right.faceId ∈ selection.peelFaces := by
    by_cases hmem : right.faceId ∈ selection.peelFaces
    · exact hmem
    · have hzero := List.count_eq_zero.mpr hmem
      rw [selection.peelFaces_count right.faceId] at hzero
      omega
  exact two_le_length_of_two_distinct_members
    selection.peelFaces left.faceId right.faceId hleftMem hrightMem hne

theorem PresentedSlabSupportedPartnerClosedFaceSelection.lowerSlabFacesByList_peelFaces
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    lowerSlabFacesByList physical selection.peelFaces =
      selection.closed.lowerPhysical := by
  funext faceId
  unfold lowerSlabFacesByList
    PresentedSlabPartnerClosedFaceSelection.lowerPhysical
    lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
  rw [selection.peelFaces_count faceId]

def PresentedSlabSupportedPartnerClosedFaceSelection.peelPath
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    SlabFacePeelPath K extent physical selection.peelFaces
      selection.closed.lowerPhysical := by
  have path := slabFacePeelPath_of_drop K extent physical
    (slabFaceStrandSelectionCount selection.closed.selected)
    (fun faceId _ =>
      slabFaceStrandSelectionCount_le selection.closed.selected faceId)
    hbounded
  change SlabFacePeelPath K extent physical selection.peelFaces
    (lowerSlabFacesByList physical selection.peelFaces) at path
  rw [selection.lowerSlabFacesByList_peelFaces] at path
  exact path

/-- The finite physical word reconstructs the source from the lowered target. -/
theorem PresentedSlabSupportedPartnerClosedFaceSelection.reconstructPhysical
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    raiseEdgeLabellingBy selection.closed.lowerPhysical
        (fun faceId => selection.peelFaces.count faceId) = physical := by
  rw [show (fun faceId => selection.peelFaces.count faceId) =
      slabFaceStrandSelectionCount selection.closed.selected by
    funext faceId
    exact selection.peelFaces_count faceId]
  unfold PresentedSlabPartnerClosedFaceSelection.lowerPhysical
    lowerSlabPhysicalByFaceStrandSelection
  exact raiseEdgeLabellingBy_lowerEdgeLabellingBy _ _
    (slabFaceStrandSelectionCount_le selection.closed.selected)

/-! ## 4. The exact anchor heat payment on presented entries -/

/-- Forget presentation proofs and write the literal auxiliary payloads in
the displayed link order.  No production-order membership is asserted. -/
def presentedSlabFusionWitnessAssignmentRaw
    {K extent : Nat} {physical : SlabLabelling} (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links) : SlabFusionWitnessAssignment :=
  links.attach.map fun linked => (linked.1, (assignment linked).auxiliary)

/-- The expanded-entry weight of a presented assignment is the actual BF4
fiber formula evaluated on its literal auxiliary payload. -/
def presentedSlabFusionWitnessAssignmentFiberWeight
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (assignment : PresentedSlabFusionWitnessAssignment
      D.cutoff D.extent physical (boundaryCompleteSlabLinks D.extent)) : Q' :=
  retainedFineIntertwinerPhysicalFiberWeight D physical
    (presentedSlabFusionWitnessAssignmentRaw
      (boundaryCompleteSlabLinks D.extent) assignment)

theorem presentedSlabFusionWitnessAssignmentFiberWeight_eqv_faceFactor
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (assignment : PresentedSlabFusionWitnessAssignment
      D.cutoff D.extent physical (boundaryCompleteSlabLinks D.extent)) :
    presentedSlabFusionWitnessAssignmentFiberWeight D physical assignment ≈
      slabParametricKPhysicalFaceFactor
        D.coupling D.cutoff D.extent physical :=
  retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
    D physical
    (presentedSlabFusionWitnessAssignmentRaw
      (boundaryCompleteSlabLinks D.extent) assignment)

/-- The serialized supported presented peel receives one exact anchor factor
per removed physical copy. -/
theorem PresentedSlabSupportedPartnerClosedFaceSelection.expandedFiberWeight_le
    (cutoff half : Nat) {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment cutoff
      (centralExtent half) physical
      (boundaryCompleteSlabLinks (centralExtent half))}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection cutoff
      (centralExtent half) physical
      (boundaryCompleteSlabLinks (centralExtent half)) assignment)
    (hbounded : SlabFaceLabellingBounded
      cutoff (centralExtent half) physical) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := cutoff
        half := half }
    presentedSlabFusionWitnessAssignmentFiberWeight D physical assignment <=
      anchorFaceCoefficient ^ selection.peelFaces.length *
        presentedSlabFusionWitnessAssignmentFiberWeight D
          selection.closed.lowerPhysical
          selection.closed.loweredAssignment := by
  dsimp only
  exact retainedFineIntertwinerPhysicalFiberWeight_anchor_peelPath_le
    cutoff half
    (presentedSlabFusionWitnessAssignmentRaw
      (boundaryCompleteSlabLinks (centralExtent half)) assignment)
    (presentedSlabFusionWitnessAssignmentRaw
      (boundaryCompleteSlabLinks (centralExtent half))
      selection.closed.loweredAssignment)
    (selection.peelPath hbounded)

end YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight.presentedSlabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight.PresentedSlabFusionWitnessFaceStrandSeed.component_faceId_physical
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight.PresentedSlabSupportedPartnerClosedFaceSelection.ofSeedUnion
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight.PresentedSlabSupportedPartnerClosedFaceSelection.peelFaces_count
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight.PresentedSlabSupportedPartnerClosedFaceSelection.two_le_peelFaces_length_of_selected_faceId_ne
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight.PresentedSlabSupportedPartnerClosedFaceSelection.peelPath
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight.PresentedSlabSupportedPartnerClosedFaceSelection.reconstructPhysical
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight.PresentedSlabSupportedPartnerClosedFaceSelection.expandedFiberWeight_le
