/-
# Sparse auxiliary rows are bounded by four times component size

The previous retained-row compiler reconstructs a selected physical terminal
on the same lattice link as every nonzero auxiliary row.  This module turns
that geometric witness into the first volume-independent size bound for the
auxiliary part of the component drop code.

Charge a retained row to the pair consisting of its computed selected
physical face-strand copy and its row link.  The row link is one of the four
boundary links of that copy's plaquette.  Equal charges have equal link keys;
since sparse row values are the prescribed word at their key, equal charges
therefore recover equal rows.  The charge image injects into the list obtained
by placing the four plaquette-boundary links over every selected component
copy, proving

```text
number of retained auxiliary rows <= 4 * number of component copies.
```

Constructive contract: finite lists, explicit terminal extraction, and
duplicate-free source links only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Duplicate-free sparse rows -/

/-- Erasing zero rows from a duplicate-free key list leaves a duplicate-free
table.  Rows with a retained key are unique because the value is the fixed
word prescribed at that key. -/
theorem slabSparseAuxiliaryDropWordsFrom_nodup
    (wordAt : SlabLink -> List Nat) : forall links : List SlabLink,
    links.Nodup ->
      (slabSparseAuxiliaryDropWordsFrom links wordAt).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      cases hzero : finiteWordAllZeroB (wordAt head) with
      | false =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            Bool.false_eq_true, ↓reduceIte]
          apply List.nodup_cons.mpr
          refine ⟨?_, slabSparseAuxiliaryDropWordsFrom_nodup wordAt tail hparts.2⟩
          intro hmem
          have hkey : head ∈ tail :=
            sparseAuxiliaryDropRow_link_mem wordAt tail
              (head, wordAt head) hmem
          exact hparts.1 hkey
      | true =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero, ↓reduceIte]
          exact slabSparseAuxiliaryDropWordsFrom_nodup wordAt tail hparts.2

/-! ## 2. The selected physical copy computed by a row witness -/

/-- Forget a retained-row terminal down to its literal physical face-strand
copy. -/
def SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment}
    {entry : SlabLink × List Nat}
    (witness : SlabSparseAuxiliaryRowPhysicalWitness seed entry) :
    SlabFaceStrandCopy physical :=
  slabLinkPhysicalTerminalFaceStrandCopy
    K extent physical entry.1
    (slabFusionWitnessAssignmentAt entry.1 assignment)
    (slabFusionWitnessAssignmentAt_mem_local
      K extent physical links assignment hassignment
      entry.1 witness.link_mem)
    witness.selectedTerminal.1

/-- The computed copy is selected by the rooted component. -/
theorem SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy_selected
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment}
    {entry : SlabLink × List Nat}
    (witness : SlabSparseAuxiliaryRowPhysicalWitness seed entry) :
    seed.selected
      (SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy witness) = true := by
  exact witness.selectedTerminal.property

/-- The computed copy's face identifier is incident on the row link. -/
theorem SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy_faceId_mem_incident
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment}
    {entry : SlabLink × List Nat}
    (witness : SlabSparseAuxiliaryRowPhysicalWitness seed entry) :
    (SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy witness).faceId ∈
      slabIncidentPlaqIds extent entry.1 := by
  let occurrence := slabLinkPhysicalTerminalOccurrence
    K extent physical entry.1
    (slabFusionWitnessAssignmentAt entry.1 assignment)
    (slabFusionWitnessAssignmentAt_mem_local
      K extent physical links assignment hassignment
      entry.1 witness.link_mem)
    witness.selectedTerminal.1
  exact occurrence.faceId_mem_incident

/-- Numerical incidence lookup implies literal membership in the four-edge
boundary of the decoded slab plaquette. -/
theorem link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
    {extent : Nat} {link : SlabLink} {faceId : Nat}
    (hface : faceId ∈ slabIncidentPlaqIds extent link) :
    link ∈ edgesOf (slabPlaquetteAt extent faceId) := by
  obtain ⟨plaquette, hindexed, hedge⟩ :=
    (mem_slabIncidentPlaqIds.mp hface)
  have hlookup : slabPlaquetteAt extent faceId = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  simpa only [hlookup] using hedge

/-! ## 3. A four-link carrier over every selected component copy -/

/-- Place the four literal boundary links of its plaquette over every copy in
a list of physical face-strand copies. -/
def faceStrandCopyBoundaryLinkCarrier
    {physical : SlabLabelling} (extent : Nat)
    (copies : List (SlabFaceStrandCopy physical)) :
    List (SlabFaceStrandCopy physical × SlabLink) :=
  copies.flatMap fun copy =>
    (edgesOf (slabPlaquetteAt extent copy.faceId)).map
      (fun link => (copy, link))

/-- Membership in the boundary-link carrier is exactly copy membership plus
literal plaquette-boundary incidence. -/
theorem mem_faceStrandCopyBoundaryLinkCarrier_iff
    {physical : SlabLabelling} (extent : Nat)
    (copies : List (SlabFaceStrandCopy physical))
    (pair : SlabFaceStrandCopy physical × SlabLink) :
    pair ∈ faceStrandCopyBoundaryLinkCarrier extent copies ↔
      pair.1 ∈ copies ∧
        pair.2 ∈ edgesOf (slabPlaquetteAt extent pair.1.faceId) := by
  constructor
  · intro hpair
    obtain ⟨copy, hcopy, hmap⟩ := List.mem_flatMap.mp hpair
    obtain ⟨link, hlink, heq⟩ := List.mem_map.mp hmap
    have hcopyEq : copy = pair.1 := by
      rw [← heq]
    have hlinkEq : link = pair.2 := by
      rw [← heq]
    exact ⟨hcopyEq ▸ hcopy, by simpa only [hcopyEq, hlinkEq] using hlink⟩
  · intro hparts
    apply List.mem_flatMap.mpr
    refine ⟨pair.1, hparts.1, ?_⟩
    exact List.mem_map.mpr ⟨pair.2, hparts.2, by cases pair; rfl⟩

/-- Every physical copy contributes exactly the four links of its plaquette. -/
theorem faceStrandCopyBoundaryLinkCarrier_length
    {physical : SlabLabelling} (extent : Nat) :
    forall copies : List (SlabFaceStrandCopy physical),
      (faceStrandCopyBoundaryLinkCarrier extent copies).length =
        4 * copies.length
  | [] => rfl
  | copy :: copies => by
      change
        ((edgesOf (slabPlaquetteAt extent copy.faceId)).map
            (fun link => (copy, link)) ++
          faceStrandCopyBoundaryLinkCarrier extent copies).length =
            4 * (copy :: copies).length
      rw [List.length_append, List.length_map,
        faceStrandCopyBoundaryLinkCarrier_length extent copies]
      simp [edgesOf, Nat.mul_add]
      omega

/-! ## 4. Injective row charging and the component-size bound -/

/-- Totalize the physical-copy compiler with the explicit component root.
The fallback branch is never used for a row in the sparse code. -/
def SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalCopy
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (entry : SlabLink × List Nat) : SlabFaceStrandCopy physical :=
  if hentry : entry ∈
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords then
    SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy
      (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalWitness
        seed entry hentry)
  else
    seed.root

/-- The row charge remembers both the computed selected copy and the row key. -/
def SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (entry : SlabLink × List Nat) :
    SlabFaceStrandCopy physical × SlabLink :=
  (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalCopy seed entry,
    entry.1)

/-- A retained row's charge lies in the four-link carrier over the rooted
component. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge_mem
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (entry : SlabLink × List Nat)
    (hentry : entry ∈
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords) :
    SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge seed entry ∈
      faceStrandCopyBoundaryLinkCarrier extent seed.component := by
  let witness :=
    SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalWitness
      seed entry hentry
  have hcopy :
      SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalCopy seed entry =
        SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy witness := by
    simp [SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalCopy,
      hentry, witness]
  apply (mem_faceStrandCopyBoundaryLinkCarrier_iff extent seed.component
    (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge seed entry)).mpr
  constructor
  · change
      SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalCopy seed entry ∈
        seed.component
    rw [hcopy]
    have hselected :=
      SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy_selected witness
    unfold SlabFaceStrandSeed.selected at hselected
    exact of_decide_eq_true hselected
  · change entry.1 ∈ edgesOf
      (slabPlaquetteAt extent
        (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalCopy
          seed entry).faceId)
    rw [hcopy]
    exact link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
      (SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy_faceId_mem_incident
        witness)

/-- Equal charges of retained rows recover equal rows: the charge equality
gives equal link keys, and sparse membership makes both values the prescribed
word at that key. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge_injectiveOn
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (left : SlabLink × List Nat)
    (hleft : left ∈
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords)
    (right : SlabLink × List Nat)
    (hright : right ∈
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords)
    (heq : SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge seed left =
      SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge seed right) :
    left = right := by
  have hkey : left.1 = right.1 := congrArg Prod.snd heq
  apply Prod.ext hkey
  have hleftWord := sparseAuxiliaryDropRow_word_eq
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
    links left hleft
  have hrightWord := sparseAuxiliaryDropRow_word_eq
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
    links right hright
  rw [hleftWord, hrightWord, hkey]

/-- The complete list of charges of retained sparse rows. -/
def SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharges
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    List (SlabFaceStrandCopy physical × SlabLink) :=
  (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords.map
    (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge seed)

/-- Duplicate-free source links make the row-charge list duplicate-free. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharges_nodup
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hnodup : links.Nodup) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharges seed).Nodup := by
  apply nodup_map_of_injOn
    (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge seed)
  · exact slabSparseAuxiliaryDropWordsFrom_nodup
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
      links hnodup
  · intro left hleft right hright heq
    exact SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge_injectiveOn
      seed
      left hleft right hright heq

/-- **Volume-independent sparse-row bound.**  Every retained auxiliary row is
injectively charged to one of the four plaquette-boundary links of one selected
physical component copy. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWords_length_le_four_mul_component
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hnodup : links.Nodup) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords.length <=
      4 * seed.component.length := by
  have hbound := CayleyPruferInjection.nodup_subset_length_le
    (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharges seed)
    (faceStrandCopyBoundaryLinkCarrier extent seed.component)
    (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharges_nodup
      seed hnodup)
    (fun charge hcharge => by
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hcharge
      exact SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge_mem
        seed entry hentry)
  rw [SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharges,
    List.length_map,
    faceStrandCopyBoundaryLinkCarrier_length extent seed.component] at hbound
  exact hbound

#print axioms slabSparseAuxiliaryDropWordsFrom_nodup
#print axioms SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy
#print axioms SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy_selected
#print axioms SlabSparseAuxiliaryRowPhysicalWitness.physicalCopy_faceId_mem_incident
#print axioms link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
#print axioms faceStrandCopyBoundaryLinkCarrier
#print axioms mem_faceStrandCopyBoundaryLinkCarrier_iff
#print axioms faceStrandCopyBoundaryLinkCarrier_length
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalCopy
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge_mem
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge_injectiveOn
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharges
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharges_nodup
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWords_length_le_four_mul_component

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
