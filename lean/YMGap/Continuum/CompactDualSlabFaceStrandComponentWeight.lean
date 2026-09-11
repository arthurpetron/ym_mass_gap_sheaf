/-
# An accepted rooted component receives its exact anchor weight payment

The preceding module constructs a complete accepted lowered configuration
from one rooted global face-strand component.  This module joins that geometry
to the exact expanded-fiber payment.

The proof is organized around a finite drop profile.  A list containing a
face identifier `d(face)` times realizes simultaneous subtraction by `d`.
Capacity and physical-support hypotheses construct a legal `SlabFacePeelPath`
by structural recursion.  For the component profile, capacity is the finite
Boolean count bound and support follows because every graph vertex is an
endpoint of an incident physical-face strand edge.

Thus the final comparison applies to the actual source assignment and the
explicit accepted target assignment, with exponent equal to the total number
of selected physical strand copies.

Constructive contract: recursion on finite face lists and natural counts,
explicit endpoint witnesses, and exact rational order algebra inherited from
the peel theorem.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
import YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. A multiplicity list constructs a legal simultaneous peel -/

/-- Subtract the occurrence multiplicity of each identifier in a face list. -/
def lowerSlabFacesByList
    (physical : SlabLabelling) (faces : List Nat) : SlabLabelling :=
  fun faceId => physical faceId - faces.count faceId

private theorem count_cons_self (id : Nat) (items : List Nat) :
    (id :: items).count id = items.count id + 1 := by
  rw [List.count_cons]
  rw [if_pos (beq_iff_eq.mpr rfl)]

private theorem count_cons_of_ne {head id : Nat} (hne : head ≠ id)
    (items : List Nat) :
    (head :: items).count id = items.count id := by
  rw [List.count_cons]
  rw [if_neg (fun heq => hne (beq_iff_eq.mp heq))]
  omega

/-- Peeling the head and then the tail is exactly multiplicity subtraction by
the complete list. -/
theorem lowerSlabFacesByList_cons
    (physical : SlabLabelling) (faceId : Nat) (faces : List Nat) :
    lowerSlabFacesByList physical (faceId :: faces) =
      lowerSlabFacesByList (lowerSlabFace physical faceId) faces := by
  funext id
  unfold lowerSlabFacesByList
  by_cases heq : id = faceId
  · subst id
    simp only [count_cons_self, lowerSlabFace_selected]
    omega
  · rw [count_cons_of_ne (fun h => heq h.symm)]
    rw [lowerSlabFace_other physical heq]

/-- A bounded multiplicity list of physical faces is a constructive legal
peel path.  This is the grouped-face version of repeated one-strand peeling. -/
def slabFacePeelPath_of_count_capacity
    (cutoff extent : Nat) (physical : SlabLabelling) :
    forall faces : List Nat,
      (forall faceId, faces.count faceId <= physical faceId) ->
      (forall faceId, faceId ∈ faces ->
        faceId ∈ slabPhysicalFaceEdges extent) ->
      SlabFaceLabellingBounded cutoff extent physical ->
      SlabFacePeelPath cutoff extent physical faces
        (lowerSlabFacesByList physical faces)
  | [], _, _, _ => by
      simpa [lowerSlabFacesByList] using
        (SlabFacePeelPath.nil (cutoff := cutoff) (extent := extent) physical)
  | faceId :: rest, hcapacity, hsupport, hbounded => by
      have hface : faceId ∈ slabPhysicalFaceEdges extent :=
        hsupport faceId List.mem_cons_self
      have hpositive : 0 < physical faceId := by
        have hcap := hcapacity faceId
        rw [count_cons_self] at hcap
        omega
      have hfaceBounded : physical faceId <= cutoff :=
        hbounded faceId hface
      have htailCapacity : forall id,
          rest.count id <= lowerSlabFace physical faceId id := by
        intro id
        by_cases heq : id = faceId
        · subst id
          rw [lowerSlabFace_selected]
          have hcap := hcapacity faceId
          rw [count_cons_self] at hcap
          omega
        · rw [lowerSlabFace_other physical heq]
          have hcap := hcapacity id
          rw [count_cons_of_ne (fun h => heq h.symm)] at hcap
          exact hcap
      have htailSupport : forall id, id ∈ rest ->
          id ∈ slabPhysicalFaceEdges extent := by
        intro id hid
        exact hsupport id (List.mem_cons_of_mem faceId hid)
      have htailBounded : SlabFaceLabellingBounded cutoff extent
          (lowerSlabFace physical faceId) := by
        intro id hid
        by_cases heq : id = faceId
        · subst id
          rw [lowerSlabFace_selected]
          exact Nat.le_trans (Nat.sub_le _ _) hfaceBounded
        · rw [lowerSlabFace_other physical heq]
          exact hbounded id hid
      have tailPath := slabFacePeelPath_of_count_capacity
        cutoff extent (lowerSlabFace physical faceId) rest
        htailCapacity htailSupport htailBounded
      have path := SlabFacePeelPath.cons
        faceId hface hpositive hfaceBounded tailPath
      rw [lowerSlabFacesByList_cons]
      exact path

/-! ## 2. Serialize a finite face-drop profile -/

/-- Repeat each displayed physical face exactly its prescribed drop count. -/
def slabFaceDropList
    (extent : Nat) (drop : Nat -> Nat) : List Nat :=
  (slabPhysicalFaceEdges extent).flatMap fun faceId =>
    List.replicate (drop faceId) faceId

private theorem rangeNodupLocal : forall count : Nat,
    (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨rangeNodupLocal count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

private theorem count_replicate_self (count id : Nat) :
    (List.replicate count id).count id = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, count_cons_self, ih]

private theorem count_replicate_of_ne
    (count : Nat) {head id : Nat} (hne : head ≠ id) :
    (List.replicate count head).count id = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, count_cons_of_ne hne, ih]

private theorem count_flatMap_replicate_of_not_mem
    (drop : Nat -> Nat) (faceId : Nat) : forall ids : List Nat,
    faceId ∉ ids ->
    (ids.flatMap fun id => List.replicate (drop id) id).count faceId = 0
  | [], _ => rfl
  | head :: tail, hnot => by
      have hhead : head ≠ faceId := by
        intro heq
        subst head
        exact hnot List.mem_cons_self
      have htail : faceId ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      simp only [List.flatMap_cons, List.count_append]
      rw [count_replicate_of_ne (drop head) hhead]
      rw [count_flatMap_replicate_of_not_mem drop faceId tail htail]

private theorem count_flatMap_replicate_of_mem
    (drop : Nat -> Nat) (faceId : Nat) : forall ids : List Nat,
    ids.Nodup -> faceId ∈ ids ->
    (ids.flatMap fun id => List.replicate (drop id) id).count faceId =
      drop faceId
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with heq | htail
      · subst head
        simp only [List.flatMap_cons, List.count_append]
        rw [count_replicate_self]
        rw [count_flatMap_replicate_of_not_mem drop faceId tail hparts.1]
        omega
      · have hhead : head ≠ faceId := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [List.flatMap_cons, List.count_append]
        rw [count_replicate_of_ne (drop head) hhead]
        rw [count_flatMap_replicate_of_mem
          drop faceId tail hparts.2 htail]
        omega

/-- Every identifier in a serialized drop profile is a displayed physical
face. -/
theorem mem_slabFaceDropList
    {extent : Nat} {drop : Nat -> Nat} {faceId : Nat}
    (hmem : faceId ∈ slabFaceDropList extent drop) :
    faceId ∈ slabPhysicalFaceEdges extent := by
  unfold slabFaceDropList at hmem
  obtain ⟨source, hsource, hrepeat⟩ := List.mem_flatMap.mp hmem
  have heq : faceId = source := List.eq_of_mem_replicate hrepeat
  simpa [heq] using hsource

/-- A duplicate-free carrier makes serialization exact: the multiplicity of
a displayed face is its prescribed drop. -/
theorem slabFaceDropList_count_of_mem
    (extent : Nat) (drop : Nat -> Nat) {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    (slabFaceDropList extent drop).count faceId = drop faceId := by
  have hnodup : (slabPhysicalFaceEdges extent).Nodup := by
    unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  unfold slabFaceDropList
  exact count_flatMap_replicate_of_mem
    drop faceId (slabPhysicalFaceEdges extent) hnodup hface

/-- Outside the displayed physical carrier, a serialized profile has zero
multiplicity. -/
theorem slabFaceDropList_count_of_not_mem
    (extent : Nat) (drop : Nat -> Nat) {faceId : Nat}
    (hface : faceId ∉ slabPhysicalFaceEdges extent) :
    (slabFaceDropList extent drop).count faceId = 0 := by
  apply List.count_eq_zero.mpr
  intro hmem
  exact hface (mem_slabFaceDropList hmem)

/-- A supported pointwise-bounded drop profile constructs its canonical legal
peel path. -/
def slabFacePeelPath_of_drop
    (cutoff extent : Nat) (physical : SlabLabelling)
    (drop : Nat -> Nat)
    (hdrop : forall faceId, faceId ∈ slabPhysicalFaceEdges extent ->
      drop faceId <= physical faceId)
    (hbounded : SlabFaceLabellingBounded cutoff extent physical) :
    SlabFacePeelPath cutoff extent physical
      (slabFaceDropList extent drop)
      (lowerSlabFacesByList physical (slabFaceDropList extent drop)) := by
  apply slabFacePeelPath_of_count_capacity
  · intro faceId
    by_cases hface : faceId ∈ slabPhysicalFaceEdges extent
    · rw [slabFaceDropList_count_of_mem extent drop hface]
      exact hdrop faceId hface
    · rw [slabFaceDropList_count_of_not_mem extent drop hface]
      exact Nat.zero_le _
  · intro faceId hmem
    exact mem_slabFaceDropList hmem
  · exact hbounded

/-! ## 3. Every rooted component drop is physically supported -/

/-- The source endpoint of a literal link strand edge lies on an actual
corrected-slab physical face. -/
theorem slabLinkFaceStrandEdgeOfTerminal_source_faceId_physical
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    (slabLinkFaceStrandEdgeOfTerminal
      K extent physical link auxiliary hmem terminal).source.faceId ∈
        slabPhysicalFaceEdges extent := by
  change (slabLinkPhysicalTerminalFaceStrandCopy
      K extent physical link auxiliary hmem terminal).faceId ∈
    slabPhysicalFaceEdges extent
  rw [slabLinkPhysicalTerminalFaceStrandCopy_faceId]
  exact slabIncidentPlaqId_physical (List.get_mem _ _)

/-- The target endpoint is the same statement applied to the explicit
physical terminal partner. -/
theorem slabLinkFaceStrandEdgeOfTerminal_target_faceId_physical
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link)
    (terminal : SlabLinkPhysicalStrandTerminal
      K extent physical link auxiliary hmem) :
    (slabLinkFaceStrandEdgeOfTerminal
      K extent physical link auxiliary hmem terminal).target.faceId ∈
        slabPhysicalFaceEdges extent := by
  change (slabLinkPhysicalTerminalFaceStrandCopy
      K extent physical link auxiliary hmem
        (slabLinkPhysicalStrandPartner
          K extent physical link auxiliary hmem terminal)).faceId ∈
    slabPhysicalFaceEdges extent
  rw [slabLinkPhysicalTerminalFaceStrandCopy_faceId]
  exact slabIncidentPlaqId_physical (List.get_mem _ _)

/-- Both endpoints of every edge in a complete assignment strand graph are
physical face copies. -/
theorem slabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    {edge : SlabFaceStrandEdge physical}
    (hedge : edge ∈ slabFusionWitnessAssignmentFaceStrandEdges
      K extent physical links assignment hassignment) :
    edge.source.faceId ∈ slabPhysicalFaceEdges extent ∧
      edge.target.faceId ∈ slabPhysicalFaceEdges extent := by
  unfold slabFusionWitnessAssignmentFaceStrandEdges at hedge
  obtain ⟨linked, _, hedge⟩ := List.mem_flatMap.mp hedge
  unfold slabFusionWitnessAssignmentFaceStrandEdgesAt at hedge
  unfold slabLinkFaceStrandEdges at hedge
  obtain ⟨terminal, _, hedgeEq⟩ := List.mem_map.mp hedge
  rw [← hedgeEq]
  exact ⟨
    slabLinkFaceStrandEdgeOfTerminal_source_faceId_physical
      K extent physical linked.1
        (slabFusionWitnessAssignmentAt linked.1 assignment)
        (slabFusionWitnessAssignmentAt_mem_local
          K extent physical links assignment hassignment
            linked.1 linked.2)
        terminal,
    slabLinkFaceStrandEdgeOfTerminal_target_faceId_physical
      K extent physical linked.1
        (slabFusionWitnessAssignmentAt linked.1 assignment)
        (slabFusionWitnessAssignmentAt_mem_local
          K extent physical links assignment hassignment
            linked.1 linked.2)
        terminal⟩

/-- Every vertex of the constructive rooted component is supported on a
literal physical face of the corrected slab. -/
theorem SlabFusionWitnessFaceStrandSeed.component_faceId_physical
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (copy : SlabFaceStrandCopy physical) (hcopy : copy ∈ seed.component) :
    copy.faceId ∈ slabPhysicalFaceEdges extent := by
  have hvertex : copy ∈ slabFaceStrandVertices
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment) := by
    exact rootComponent_subset
      (slabFaceStrandAdjacentB
        (slabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment hassignment))
      seed.root_mem hcopy
  obtain ⟨edge, hedge, hendpoint⟩ := List.mem_flatMap.mp hvertex
  have hphysical :=
    slabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
      K extent physical links assignment hassignment hedge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hendpoint
  rcases hendpoint with hsource | htarget
  · rw [hsource]
    exact hphysical.1
  · rw [htarget]
    exact hphysical.2

private theorem boolCountFrom_false (start : Nat) : forall length : Nat,
    boolCountFrom (fun _ => false) start length = 0
  | 0 => rfl
  | length + 1 => by
      rw [boolCountFrom]
      simp only [boolIndicator, Nat.zero_add]
      exact boolCountFrom_false (start + 1) length

/-- A true slot makes its enclosing finite Boolean count strictly positive. -/
private theorem boolCountFrom_pos_of_true
    (selected : Nat -> Bool) : forall start length offset : Nat,
    offset < length -> selected (start + offset) = true ->
      0 < boolCountFrom selected start length
  | _, 0, offset, hoffset, _ => by omega
  | start, length + 1, 0, _, htrue => by
      rw [boolCountFrom]
      simp only [Nat.add_zero] at htrue
      rw [htrue]
      simp only [boolIndicator]
      omega
  | start, length + 1, offset + 1, hoffset, htrue => by
      rw [boolCountFrom]
      have htail : 0 < boolCountFrom selected (start + 1) length :=
        boolCountFrom_pos_of_true selected (start + 1) length offset
          (by omega) (by
            have hindex : start + 1 + offset = start + (offset + 1) := by
              omega
            rw [hindex]
            exact htrue)
      omega

/-- A component has zero selected-copy count outside the physical face
carrier. -/
theorem SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_physical
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (faceId : Nat) (hface : faceId ∉ slabPhysicalFaceEdges extent) :
    slabFaceStrandSelectionCount seed.selected faceId = 0 := by
  unfold slabFaceStrandSelectionCount
  have hcount := boolCountFrom_congr
    (slabFaceStrandSelectionAt seed.selected faceId)
    (fun _ => false) 0 0 (physical faceId) (by
      intro offset hoffset
      let copy : SlabFaceStrandCopy physical :=
        { faceId := faceId, slot := ⟨offset, hoffset⟩ }
      have hcopy : copy ∉ seed.component := by
        intro hmem
        exact hface
          (SlabFusionWitnessFaceStrandSeed.component_faceId_physical
            seed copy hmem)
      simp only [Nat.zero_add]
      change slabFaceStrandSelectionAt seed.selected faceId offset = false
      simp [slabFaceStrandSelectionAt, hoffset,
        SlabFaceStrandSeed.selected, copy, hcopy])
  exact hcount.trans (boolCountFrom_false 0 (physical faceId))

/-- The explicitly rooted component selects at least its root copy. -/
theorem SlabFusionWitnessFaceStrandSeed.selectionCount_root_pos
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    0 < slabFaceStrandSelectionCount seed.selected seed.root.faceId := by
  apply boolCountFrom_pos_of_true
    (slabFaceStrandSelectionAt seed.selected seed.root.faceId)
    0 (physical seed.root.faceId) seed.root.slot.val seed.root.slot.isLt
  rw [Nat.zero_add, slabFaceStrandSelectionAt_fin]
  unfold SlabFaceStrandSeed.selected SlabFaceStrandSeed.component
  simp only [decide_eq_true_eq]
  exact root_mem_rootComponent
    (slabFaceStrandAdjacentB
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment))
    seed.root_mem

/-- Every selected component copy contributes a positive multiplicity at its
face identifier. -/
theorem SlabFusionWitnessFaceStrandSeed.selectionCount_pos_of_mem
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (copy : SlabFaceStrandCopy physical) (hcopy : copy ∈ seed.component) :
    0 < slabFaceStrandSelectionCount seed.selected copy.faceId := by
  apply boolCountFrom_pos_of_true
    (slabFaceStrandSelectionAt seed.selected copy.faceId)
    0 (physical copy.faceId) copy.slot.val copy.slot.isLt
  rw [Nat.zero_add, slabFaceStrandSelectionAt_fin]
  unfold SlabFaceStrandSeed.selected
  simp only [decide_eq_true_eq]
  exact hcopy

/-! ## 4. The component's canonical peel path -/

/-- Serialize the exact selected-copy count of the rooted component. -/
def SlabFusionWitnessFaceStrandSeed.peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : List Nat :=
  slabFaceDropList extent
    (slabFaceStrandSelectionCount seed.selected)

/-- The serialized multiplicity at every identifier is exactly the global
component incidence count, including outside the physical carrier. -/
theorem SlabFusionWitnessFaceStrandSeed.peelFaces_count
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (faceId : Nat) :
    (SlabFusionWitnessFaceStrandSeed.peelFaces seed).count faceId =
      slabFaceStrandSelectionCount seed.selected faceId := by
  by_cases hface : faceId ∈ slabPhysicalFaceEdges extent
  · unfold SlabFusionWitnessFaceStrandSeed.peelFaces
    exact slabFaceDropList_count_of_mem extent
      (slabFaceStrandSelectionCount seed.selected) hface
  · unfold SlabFusionWitnessFaceStrandSeed.peelFaces
    rw [slabFaceDropList_count_of_not_mem extent
      (slabFaceStrandSelectionCount seed.selected) hface]
    exact
      (SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_physical
        seed faceId hface).symm

/-- A rooted component peel is nonempty: its serialized multiplicity contains
at least the chosen root copy. -/
theorem SlabFusionWitnessFaceStrandSeed.peelFaces_length_pos
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    0 < (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  have hroot := SlabFusionWitnessFaceStrandSeed.selectionCount_root_pos seed
  have hcount := SlabFusionWitnessFaceStrandSeed.peelFaces_count
    seed seed.root.faceId
  have hle :
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).count
          seed.root.faceId <=
        (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length :=
    List.count_le_length
  omega

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

/-- A rooted physical strand component always peels at least two face copies.
The partner endpoint supplied by the root's displayed edge lies on a distinct
face in the same component, so both distinct face identifiers occur in the
serialized multiplicity list. -/
theorem SlabFusionWitnessFaceStrandSeed.two_le_peelFaces_length
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    2 <= (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  obtain ⟨copy, hcopy, hne⟩ :=
    SlabFaceStrandSeed.exists_component_faceId_ne_root seed
  have hrootPos := SlabFusionWitnessFaceStrandSeed.selectionCount_root_pos seed
  have hcopyPos :=
    SlabFusionWitnessFaceStrandSeed.selectionCount_pos_of_mem seed copy hcopy
  have hrootMem : seed.root.faceId ∈
      SlabFusionWitnessFaceStrandSeed.peelFaces seed := by
    by_cases hmem : seed.root.faceId ∈
        SlabFusionWitnessFaceStrandSeed.peelFaces seed
    · exact hmem
    · have hzero := List.count_eq_zero.mpr hmem
      rw [SlabFusionWitnessFaceStrandSeed.peelFaces_count seed] at hzero
      exact False.elim (by omega)
  have hcopyMem : copy.faceId ∈
      SlabFusionWitnessFaceStrandSeed.peelFaces seed := by
    by_cases hmem : copy.faceId ∈
        SlabFusionWitnessFaceStrandSeed.peelFaces seed
    · exact hmem
    · have hzero := List.count_eq_zero.mpr hmem
      rw [SlabFusionWitnessFaceStrandSeed.peelFaces_count seed] at hzero
      exact False.elim (by omega)
  exact two_le_length_of_two_distinct_members
    (SlabFusionWitnessFaceStrandSeed.peelFaces seed)
    seed.root.faceId copy.faceId hrootMem hcopyMem hne.symm

/-- Multiplicity subtraction along the serialized component list is the
previously defined common lowered physical labelling. -/
theorem SlabFusionWitnessFaceStrandSeed.lowerSlabFacesByList_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    lowerSlabFacesByList physical
        (SlabFusionWitnessFaceStrandSeed.peelFaces seed) =
      SlabFusionWitnessFaceStrandSeed.lowerPhysical seed := by
  funext faceId
  unfold lowerSlabFacesByList
    SlabFusionWitnessFaceStrandSeed.lowerPhysical
    lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
  rw [SlabFusionWitnessFaceStrandSeed.peelFaces_count seed faceId]

/-- The exact selected-copy profile of a bounded physical configuration is a
legal repeated physical-face peel ending at the accepted component target. -/
def SlabFusionWitnessFaceStrandSeed.peelPath
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    SlabFacePeelPath K extent physical
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed)
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) := by
  have path := slabFacePeelPath_of_drop K extent physical
    (slabFaceStrandSelectionCount seed.selected)
    (fun faceId _ => slabFaceStrandSelectionCount_le seed.selected faceId)
    hbounded
  change SlabFacePeelPath K extent physical
    (SlabFusionWitnessFaceStrandSeed.peelFaces seed)
    (lowerSlabFacesByList physical
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed)) at path
  rw [SlabFusionWitnessFaceStrandSeed.lowerSlabFacesByList_peelFaces seed]
    at path
  exact path

/-! ## 5. The accepted expanded-fiber component payment -/

/-- **Accepted expanded component peel.**  At the production anchor, the
actual source fiber entry is bounded by the exact per-selected-copy power
times the explicitly constructed accepted target fiber entry. -/
theorem SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_le
    (cutoff half : Nat) {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))}
    (seed : SlabFusionWitnessFaceStrandSeed
      cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))
        assignment hassignment)
    (hbounded : SlabFaceLabellingBounded
      cutoff (centralExtent half) physical) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight D physical assignment <=
      anchorFaceCoefficient ^
          (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length *
        retainedFineIntertwinerPhysicalFiberWeight D
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
          (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) := by
  exact retainedFineIntertwinerPhysicalFiberWeight_anchor_peelPath_le
    cutoff half assignment
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed)
      (SlabFusionWitnessFaceStrandSeed.peelPath seed hbounded)

#print axioms slabLinkFaceStrandEdgeOfTerminal_source_faceId_physical
#print axioms slabLinkFaceStrandEdgeOfTerminal_target_faceId_physical
#print axioms slabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
#print axioms SlabFusionWitnessFaceStrandSeed.component_faceId_physical
#print axioms SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_physical
#print axioms SlabFusionWitnessFaceStrandSeed.selectionCount_root_pos
#print axioms SlabFusionWitnessFaceStrandSeed.selectionCount_pos_of_mem
#print axioms SlabFusionWitnessFaceStrandSeed.peelFaces
#print axioms SlabFusionWitnessFaceStrandSeed.peelFaces_count
#print axioms SlabFusionWitnessFaceStrandSeed.peelFaces_length_pos
#print axioms SlabFusionWitnessFaceStrandSeed.two_le_peelFaces_length
#print axioms SlabFusionWitnessFaceStrandSeed.lowerSlabFacesByList_peelFaces
#print axioms SlabFusionWitnessFaceStrandSeed.peelPath
#print axioms SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_le

#print axioms lowerSlabFacesByList
#print axioms lowerSlabFacesByList_cons
#print axioms slabFacePeelPath_of_count_capacity
#print axioms slabFaceDropList
#print axioms mem_slabFaceDropList
#print axioms slabFaceDropList_count_of_mem
#print axioms slabFaceDropList_count_of_not_mem
#print axioms slabFacePeelPath_of_drop

end YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
