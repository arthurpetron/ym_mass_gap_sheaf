/-
# Reduce a complete canonical strand family to one finite-core field

The canonical component family is exhaustive on the graph endpoint carrier.
For the complete corrected-slab link list, every literal physical face-strand
copy is an endpoint: choose the first boundary link of its face, observe its
actual slot at that link, and use the displayed terminal-pair edge.  Hence the
sum of all canonical component multiplicities on a physical face is exactly
the face label `p`.

This equality permits a single simultaneous exterior/core split of the
complete family.  Splitting the aggregate drop once, rather than concatenating
componentwise exterior words, preserves the high-spin reserve:

```text
aggregate exterior = min p (p - S),
aggregate core     = p - aggregate exterior <= S.
```

The aggregate exterior word constructs one actual high-spin path from the
source field to a field bounded by `S` on every physical face.  Exact complete
coverage further identifies that target with literal threshold truncation,
independent of the accepted source assignment, and identifies the paid path
length with the total displayed spin excess above `S`.  The retained
fine-intertwiner fiber has unit counting weight, so the existing path
comparison yields a canonical arbitrary-coupling source-to-core estimate with
an arbitrary target witness.

This is a simultaneous canonical finite-core reduction.  It does not yet sum
the source-assignment fiber over one truncated target into a partition
estimate or prove finite-core coercivity.

Constructive contract: deterministic face-link incidence, finite graph
coverage, exact Boolean counting, and the existing high-spin path compiler
only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreResidual
import YMGap.Continuum.CompactDualSlabObservableRootSeed

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCompleteCoreReduction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreFamily
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreResidual
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabObservableRootSeed
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Every physical strand copy occurs in the complete graph -/

/-- Generalization of the fixed slot-zero observable root: every bounded slot
of every physical face is a displayed endpoint of the complete assignment's
global strand graph. -/
theorem slabPhysicalFaceStrandCopy_mem_vertices
    (cutoff extent : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (copy : SlabFaceStrandCopy physical)
    (hface : copy.faceId ∈ slabPhysicalFaceEdges extent) :
    copy ∈ slabFaceStrandVertices
      (slabFusionWitnessAssignmentFaceStrandEdges
        cutoff extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) := by
  let link := slabObservableRootLink extent copy.faceId
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
    ⟨copy.slot.val, by
      rw [slabObservableRootPosition_get hface]
      exact copy.slot.isLt⟩
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
  have hsourceEq : edge.source = copy := by
    apply slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
    · rw [hcopy]
      exact slabObservableRootPosition_get hface
    · rw [hcopy]
  rw [← hsourceEq]
  exact hsource

/-! ## 2. Exact canonical multiplicity on the complete link carrier -/

private theorem listNatWeight_add {A : Type}
    (left right : A -> Nat) : forall items : List A,
    listNatWeight (fun item => left item + right item) items =
      listNatWeight left items + listNatWeight right items
  | [] => rfl
  | _ :: tail => by
      simp only [listNatWeight]
      rw [listNatWeight_add left right tail]
      omega

private theorem term_le_listNatWeight_of_mem {A : Type}
    (weight : A -> Nat) : forall (items : List A) (item : A),
    item ∈ items -> weight item <= listNatWeight weight items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst item
        simp only [listNatWeight]
        omega
      · have hind := term_le_listNatWeight_of_mem weight tail item htail
        simp only [listNatWeight]
        omega

/-- If every position is selected by at least one Boolean row, the interval
length is bounded by the sum of the row counts. -/
private theorem length_le_listNatWeight_boolCountFrom
    {A : Type} (selected : A -> Nat -> Bool) (items : List A) :
    forall (start length : Nat),
      (forall index, start <= index -> index < start + length ->
        1 <= listNatWeight
          (fun item => boolIndicator (selected item index)) items) ->
      length <= listNatWeight
        (fun item => boolCountFrom (selected item) start length) items
  | _, 0, _ => Nat.zero_le _
  | start, Nat.succ length, hpoint => by
      have hnow := hpoint start (by omega) (by omega)
      have htail := length_le_listNatWeight_boolCountFrom selected items
        (start + 1) length
        (fun index hstart hfinish => hpoint index (by omega) (by omega))
      simp only [boolCountFrom]
      rw [listNatWeight_add]
      omega

/-- On the complete link carrier, the exhaustive canonical components count
every physical strand copy exactly once. -/
theorem slabCompleteCanonicalComponentSelectionMassAtFace_eq
    (cutoff extent : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    slabCanonicalComponentSelectionMassAtFace cutoff extent physical
        (boundaryCompleteSlabLinks extent) assignment hassignment faceId =
      physical faceId := by
  let edges := slabFusionWitnessAssignmentFaceStrandEdges
    cutoff extent physical (boundaryCompleteSlabLinks extent)
      assignment hassignment
  let components := slabFaceStrandCanonicalComponents edges
  let rows : List (SlabFaceStrandCanonicalComponent edges) :=
    (slabFaceStrandCanonicalComponents edges).attach
  let selectedAt : SlabFaceStrandCanonicalComponent edges -> Nat -> Bool :=
    fun component slot =>
      slabFaceStrandSelectionAt component.seed.selected faceId slot
  have hlower : physical faceId <= listNatWeight
      (fun component : SlabFaceStrandCanonicalComponent edges =>
        boolCountFrom (selectedAt component) 0 (physical faceId)) rows := by
    apply length_le_listNatWeight_boolCountFrom
    intro index _ hindex
    let copy : SlabFaceStrandCopy physical :=
      { faceId := faceId, slot := ⟨index, by omega⟩ }
    have hvertex : copy ∈ slabFaceStrandDistinctVertices edges := by
      apply List.mem_eraseDups.mpr
      exact slabPhysicalFaceStrandCopy_mem_vertices
        cutoff extent physical assignment hassignment copy hface
    obtain ⟨component, hcomponent, hcopyComponent⟩ :=
      (graphComponents_covers
        (slabFaceStrandAdjacentB edges)
        (slabFaceStrandDistinctVertices edges) copy).1 hvertex
    have hcomponentMap : component ∈ rows.map Subtype.val := by
      change component ∈
        (slabFaceStrandCanonicalComponents edges).attach.map Subtype.val
      rw [List.attach_map_subtype_val]
      exact hcomponent
    obtain ⟨rawEntry, hrawEntry, hentryValue⟩ :=
      List.mem_map.mp hcomponentMap
    let entry : SlabFaceStrandCanonicalComponent edges :=
      ⟨component, hcomponent⟩
    have hrawEntryEq : rawEntry = entry := by
      apply Subtype.ext
      exact hentryValue
    have hentry : entry ∈ rows := by
      rw [← hrawEntryEq]
      exact hrawEntry
    have hcopyEntry : copy ∈ entry.1 := by
      exact hcopyComponent
    have hcopySeed : copy ∈ entry.seed.component :=
      (entry.mem_seed_component_iff copy).2 hcopyEntry
    have hselected : selectedAt entry index = true := by
      unfold selectedAt
      change slabFaceStrandSelectionAt entry.seed.selected faceId
          copy.slot.val = true
      rw [slabFaceStrandSelectionAt_fin]
      have hcopyEq :
          ({ faceId := faceId, slot := copy.slot } :
            SlabFaceStrandCopy physical) = copy := by
        apply slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
        · rfl
        · rfl
      rw [hcopyEq]
      unfold SlabFaceStrandSeed.selected
      simp [hcopySeed]
    have hone : boolIndicator (selectedAt entry index) = 1 := by
      simp [hselected, boolIndicator]
    have hterm := term_le_listNatWeight_of_mem
      (fun component : SlabFaceStrandCanonicalComponent edges =>
        boolIndicator (selectedAt component index)) rows entry hentry
    have hterm' : boolIndicator (selectedAt entry index) <=
        listNatWeight
          (fun component : SlabFaceStrandCanonicalComponent edges =>
            boolIndicator (selectedAt component index)) rows := by
      simpa only using hterm
    rw [hone] at hterm'
    exact hterm'
  have hupper := slabCanonicalComponentSelectionMassAtFace_le
    cutoff extent physical (boundaryCompleteSlabLinks extent)
      assignment hassignment faceId
  change listNatWeight
      (fun component : SlabFaceStrandCanonicalComponent edges =>
        boolCountFrom (selectedAt component) 0 (physical faceId)) rows <=
    physical faceId at hupper
  change listNatWeight
      (fun component : SlabFaceStrandCanonicalComponent edges =>
        boolCountFrom (selectedAt component) 0 (physical faceId)) rows =
    physical faceId
  omega

/-! ## 3. One simultaneous exterior path to a finite-core field -/

/-- The complete canonical family's exact physical drop profile. -/
def slabCompleteCanonicalDropCount
    (cutoff extent : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent)) : Nat -> Nat :=
  slabCanonicalComponentSelectionMassAtFace cutoff extent physical
    (boundaryCompleteSlabLinks extent) assignment hassignment

/-- The single aggregate high-spin exterior word. -/
def slabCompleteCanonicalExteriorFaces
    (cutoff extent : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (threshold : Nat) : List Nat :=
  highSpinExteriorDropFaces extent physical threshold
    (slabCompleteCanonicalDropCount
      cutoff extent physical assignment hassignment)

/-- The physical field after the simultaneous aggregate exterior removal. -/
def slabCompleteCanonicalCorePhysical
    (cutoff extent : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (threshold : Nat) : SlabLabelling :=
  highSpinCorePhysical extent physical threshold
    (slabCompleteCanonicalDropCount
      cutoff extent physical assignment hassignment)

/-- The assignment-independent finite-core field obtained by truncating every
displayed physical face at `threshold` and leaving every other coordinate
unchanged. -/
def slabThresholdCorePhysical
    (extent : Nat) (physical : SlabLabelling)
    (threshold : Nat) : SlabLabelling :=
  fun faceId =>
    if faceId ∈ slabPhysicalFaceEdges extent then
      min (physical faceId) threshold
    else
      physical faceId

/-- The total high-spin excess above `threshold` on the displayed physical
face carrier. -/
def slabThresholdExteriorMass
    (extent : Nat) (physical : SlabLabelling)
    (threshold : Nat) : Nat :=
  listNatWeight
    (fun faceId => physical faceId - threshold)
    (slabPhysicalFaceEdges extent)

/-- The aggregate exterior constructs one actual threshold-respecting path. -/
def slabCompleteCanonicalHighSpinPath
    (threshold cutoff extent : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (hbounded : SlabFaceLabellingBounded cutoff extent physical) :
    SlabHighSpinFacePeelPath threshold cutoff extent physical
      (slabCompleteCanonicalExteriorFaces
        cutoff extent physical assignment hassignment threshold)
      (slabCompleteCanonicalCorePhysical
        cutoff extent physical assignment hassignment threshold) :=
  slabHighSpinCoreSplitPath threshold cutoff extent physical
    (slabCompleteCanonicalDropCount
      cutoff extent physical assignment hassignment) hbounded

/-- The simultaneous target really is finite-core on every displayed physical
face. -/
theorem slabCompleteCanonicalCorePhysical_le_threshold
    (cutoff extent : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (threshold faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    slabCompleteCanonicalCorePhysical
        cutoff extent physical assignment hassignment threshold faceId <=
      threshold := by
  have hdrop := slabCompleteCanonicalComponentSelectionMassAtFace_eq
    cutoff extent physical assignment hassignment faceId hface
  unfold slabCompleteCanonicalCorePhysical highSpinCorePhysical
    highSpinExteriorDropFaces lowerSlabFacesByList
  rw [slabFaceDropList_count_of_mem extent
    (exteriorDropCount physical threshold
      (slabCompleteCanonicalDropCount
        cutoff extent physical assignment hassignment)) hface]
  unfold exteriorDropCount slabCompleteCanonicalDropCount
  rw [hdrop]
  rw [Nat.min_eq_right (Nat.sub_le _ _)]
  omega

/-- The simultaneous complete-component reduction has no hidden dependence
on the accepted fusion assignment: on every displayed face it is literal
truncation at `threshold`, and outside the displayed carrier it is unchanged. -/
theorem slabCompleteCanonicalCorePhysical_eq_thresholdCorePhysical
    (cutoff extent : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (threshold : Nat) :
    slabCompleteCanonicalCorePhysical
        cutoff extent physical assignment hassignment threshold =
      slabThresholdCorePhysical extent physical threshold := by
  funext faceId
  unfold slabCompleteCanonicalCorePhysical highSpinCorePhysical
    highSpinExteriorDropFaces lowerSlabFacesByList
    slabThresholdCorePhysical
  by_cases hface : faceId ∈ slabPhysicalFaceEdges extent
  · rw [if_pos hface]
    rw [slabFaceDropList_count_of_mem extent
      (exteriorDropCount physical threshold
        (slabCompleteCanonicalDropCount
          cutoff extent physical assignment hassignment)) hface]
    have hdrop := slabCompleteCanonicalComponentSelectionMassAtFace_eq
      cutoff extent physical assignment hassignment faceId hface
    unfold exteriorDropCount slabCompleteCanonicalDropCount
    rw [hdrop]
    omega
  · rw [if_neg hface]
    rw [slabFaceDropList_count_of_not_mem extent
      (exteriorDropCount physical threshold
        (slabCompleteCanonicalDropCount
          cutoff extent physical assignment hassignment)) hface]
    omega

/-- Consequently, any two accepted assignments over the same physical field
produce exactly the same simultaneous finite-core target. -/
theorem slabCompleteCanonicalCorePhysical_assignment_independent
    (cutoff extent : Nat) (physical : SlabLabelling)
    (first second : SlabFusionWitnessAssignment)
    (hfirst : first ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (hsecond : second ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (threshold : Nat) :
    slabCompleteCanonicalCorePhysical
        cutoff extent physical first hfirst threshold =
      slabCompleteCanonicalCorePhysical
        cutoff extent physical second hsecond threshold := by
  rw [slabCompleteCanonicalCorePhysical_eq_thresholdCorePhysical,
    slabCompleteCanonicalCorePhysical_eq_thresholdCorePhysical]

private theorem flatMap_replicate_length_eq_listNatWeight
    {A B : Type} (count : A -> Nat) (value : A -> B) :
    forall items : List A,
      (items.flatMap fun item =>
          List.replicate (count item) (value item)).length =
        listNatWeight count items
  | [] => rfl
  | head :: tail => by
      simp only [List.flatMap_cons, List.length_append,
        List.length_replicate, listNatWeight]
      rw [flatMap_replicate_length_eq_listNatWeight count value tail]

private theorem listNatWeight_congr_local
    {A : Type} (left right : A -> Nat) :
    forall items : List A,
      (forall item, item ∈ items -> left item = right item) ->
      listNatWeight left items = listNatWeight right items
  | [], _ => rfl
  | head :: tail, heq => by
      simp only [listNatWeight]
      rw [heq head List.mem_cons_self]
      rw [listNatWeight_congr_local left right tail
        (fun item hitem => heq item (List.mem_cons_of_mem head hitem))]

/-- The paid path length is also assignment-independent: it is exactly the
total displayed face mass above the threshold. -/
theorem slabCompleteCanonicalExteriorFaces_length_eq_thresholdExteriorMass
    (cutoff extent : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff extent physical
        (boundaryCompleteSlabLinks extent))
    (threshold : Nat) :
    (slabCompleteCanonicalExteriorFaces
        cutoff extent physical assignment hassignment threshold).length =
      slabThresholdExteriorMass extent physical threshold := by
  unfold slabCompleteCanonicalExteriorFaces highSpinExteriorDropFaces
    slabFaceDropList slabThresholdExteriorMass
  rw [flatMap_replicate_length_eq_listNatWeight]
  apply listNatWeight_congr_local
  intro faceId hface
  unfold exteriorDropCount slabCompleteCanonicalDropCount
  rw [slabCompleteCanonicalComponentSelectionMassAtFace_eq
    cutoff extent physical assignment hassignment faceId hface]
  rw [Nat.min_eq_right (Nat.sub_le _ _)]

/-! ## 4. Direct arbitrary-coupling source-to-core comparison -/

/-- At the moving anchor threshold, the complete assignment receives one
simultaneous exterior payment down to a genuinely finite-core physical field.
No accepted intermediate assignment is required or claimed. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_completeCore_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half)))
    (targetWitness : SlabFusionWitnessAssignment)
    (hbounded : SlabFaceLabellingBounded
      cutoff (centralExtent half) physical) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := Q'.le_of_lt hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight D physical assignment <=
      anchorFaceCoefficient ^
          (slabCompleteCanonicalExteriorFaces cutoff (centralExtent half)
            physical assignment hassignment
            (anchorPaidExteriorThreshold w)).length *
        retainedFineIntertwinerPhysicalFiberWeight D
          (slabCompleteCanonicalCorePhysical cutoff (centralExtent half)
            physical assignment hassignment
            (anchorPaidExteriorThreshold w))
          targetWitness := by
  exact retainedFineIntertwinerPhysicalFiberWeight_exterior_anchorPaid_le
    hw0 hw1 cutoff half assignment targetWitness
    (slabCompleteCanonicalHighSpinPath
      (anchorPaidExteriorThreshold w) cutoff (centralExtent half)
      physical assignment hassignment hbounded)

/-- **Canonical arbitrary-coupling source-to-core comparison.**  The complete
accepted assignment pays exactly once for every displayed unit of spin above
the moving threshold and lands on the common truncated physical field.  Both
the exponent and the physical target are independent of the source fusion
assignment. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_thresholdCore_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half)))
    (targetWitness : SlabFusionWitnessAssignment)
    (hbounded : SlabFaceLabellingBounded
      cutoff (centralExtent half) physical) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := Q'.le_of_lt hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight D physical assignment <=
      anchorFaceCoefficient ^
          slabThresholdExteriorMass
            (centralExtent half) physical (anchorPaidExteriorThreshold w) *
        retainedFineIntertwinerPhysicalFiberWeight D
          (slabThresholdCorePhysical
            (centralExtent half) physical (anchorPaidExteriorThreshold w))
          targetWitness := by
  have hraw := retainedFineIntertwinerPhysicalFiberWeight_completeCore_le
    hw0 hw1 cutoff half hassignment targetWitness hbounded
  rw [slabCompleteCanonicalExteriorFaces_length_eq_thresholdExteriorMass,
    slabCompleteCanonicalCorePhysical_eq_thresholdCorePhysical] at hraw
  exact hraw

#print axioms slabPhysicalFaceStrandCopy_mem_vertices
#print axioms slabCompleteCanonicalComponentSelectionMassAtFace_eq
#print axioms slabCompleteCanonicalDropCount
#print axioms slabCompleteCanonicalExteriorFaces
#print axioms slabCompleteCanonicalCorePhysical
#print axioms slabThresholdCorePhysical
#print axioms slabThresholdExteriorMass
#print axioms slabCompleteCanonicalHighSpinPath
#print axioms slabCompleteCanonicalCorePhysical_le_threshold
#print axioms slabCompleteCanonicalCorePhysical_eq_thresholdCorePhysical
#print axioms slabCompleteCanonicalCorePhysical_assignment_independent
#print axioms slabCompleteCanonicalExteriorFaces_length_eq_thresholdExteriorMass
#print axioms retainedFineIntertwinerPhysicalFiberWeight_completeCore_le
#print axioms retainedFineIntertwinerPhysicalFiberWeight_thresholdCore_le

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCompleteCoreReduction
