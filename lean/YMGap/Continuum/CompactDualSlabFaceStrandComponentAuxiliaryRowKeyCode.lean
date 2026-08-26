/-
# Component-relative binary codes for sparse auxiliary row keys

Every retained nonzero auxiliary row is incident to a selected physical
strand copy.  After the component plaquettes have been decoded, its possible
row keys therefore lie in the deduplicated union of the four boundary links
of those plaquettes.

This module stores one presence bit per such candidate link and pads the word
to `4 * peelSize`.  The resulting carrier has exact size `16 ^ peelSize`,
independently of volume and cutoff.  A witness-independent decoder recovers
membership in the production sparse-row key set, so equal rooted shape and key
codes force equal key supports.

Constructive contract: finite lists, duplicate erasure, exact row charging,
and Boolean membership only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowKeyCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Candidate links decoded from the geometric word -/

/-- Deduplicate the four boundary links of every decoded component
plaquette. -/
def componentPhysicalDropDecodedBoundaryLinks
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1))) : List SlabLink :=
  ((componentPhysicalDropDecodedSupport extent rootFaceId shapeCode).flatMap
    edgesOf).eraseDups

/-- The production specialization of the witness-independent candidate-link
decoder. -/
def componentDecodedBoundaryLinks
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : List SlabLink :=
  componentPhysicalDropDecodedBoundaryLinks extent seed.root.faceId
    (componentPlaquettePaddedTourCode seed)

private theorem filterTrueLocal {A : Type} :
    forall items : List A, items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

private theorem filteredEraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    forall predicate : A -> Bool,
      (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail induction =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr
          ⟨?_, induction (fun item => (!(item == head)) && predicate item)⟩
        intro hmem
        have hmem' : head ∈ tail.filter
            (fun item => (!(item == head)) && predicate item) :=
          List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hmem').2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact induction predicate

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

private theorem eraseDupsLengthLeLocal {A : Type}
    [BEq A] (items : List A) :
    items.eraseDups.length <= items.length := by
  cases items with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have hfilter := List.length_filter_le
        (fun item : A => !item == head) tail
      have ih := eraseDupsLengthLeLocal
        (tail.filter fun item => !item == head)
      omega
termination_by items.length
decreasing_by
  simp only [List.length_cons]
  omega

private theorem flatMap_edgesOf_length : forall plaquettes : List Z4Plaq,
    (plaquettes.flatMap edgesOf).length = 4 * plaquettes.length
  | [] => rfl
  | plaquette :: plaquettes => by
      rw [List.flatMap_cons, List.length_append,
        flatMap_edgesOf_length plaquettes]
      simp [edgesOf]
      omega

/-- The decoded candidate-link list is duplicate-free. -/
theorem componentDecodedBoundaryLinks_nodup
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    (componentDecodedBoundaryLinks seed).Nodup := by
  unfold componentDecodedBoundaryLinks
    componentPhysicalDropDecodedBoundaryLinks
  exact eraseDupsNodupLocal _

/-- There are at most four candidate row keys per physical peel entry. -/
theorem componentDecodedBoundaryLinks_length_le_four_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    (componentDecodedBoundaryLinks seed).length <=
      4 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  have herase := eraseDupsLengthLeLocal
    ((componentDecodedPlaquetteSupport seed).flatMap edgesOf)
  have hsupport := componentDecodedPlaquetteSupport_length_le_peelFaces seed
  change
    ((componentDecodedPlaquetteSupport seed).flatMap edgesOf).eraseDups.length <=
      4 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length
  rw [flatMap_edgesOf_length] at herase
  omega

/-! ## 2. The production sparse-row key support -/

/-- Retain just the link keys of the production sparse auxiliary table. -/
def componentSparseAuxiliaryRowKeys
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : List SlabLink :=
  (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords.map
    Prod.fst

/-- The production sparse row keys contain no duplicates. -/
theorem componentSparseAuxiliaryRowKeys_nodup
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    (componentSparseAuxiliaryRowKeys seed).Nodup := by
  unfold componentSparseAuxiliaryRowKeys
  apply nodup_map_of_injOn Prod.fst
  · exact slabSparseAuxiliaryDropWordsFrom_nodup
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
      (boundaryCompleteSlabLinks extent)
      (boundaryCompleteSlabLinks_nodup extent)
  · intro left hleft right hright hkey
    apply Prod.ext hkey
    have hleftWord := sparseAuxiliaryDropRow_word_eq
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
      (boundaryCompleteSlabLinks extent) left hleft
    have hrightWord := sparseAuxiliaryDropRow_word_eq
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
      (boundaryCompleteSlabLinks extent) right hright
    rw [hleftWord, hrightWord, hkey]

/-- Exact row charging places every retained production key in the decoded
component boundary-link carrier. -/
theorem componentSparseAuxiliaryRowKey_mem_decodedBoundaryLinks
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment)
    (link : SlabLink) (hlink : link ∈ componentSparseAuxiliaryRowKeys seed) :
    link ∈ componentDecodedBoundaryLinks seed := by
  obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hlink
  have hcharge :=
    SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge_mem
      seed entry hentry
  have hparts := (mem_faceStrandCopyBoundaryLinkCarrier_iff
    extent seed.component
      (SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowCharge
        seed entry)).mp hcharge
  let copy :=
    SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalCopy seed entry
  have hcopy : copy ∈ seed.component := by
    exact hparts.1
  have hedge : entry.1 ∈ edgesOf (slabPlaquetteAt extent copy.faceId) := by
    exact hparts.2
  have hplaquette : slabPlaquetteAt extent copy.faceId ∈
      componentDecodedPlaquetteSupport seed := by
    apply (componentDecodedPlaquetteSupport_sameSupport seed).1
    apply (mem_componentPlaquetteSupport_iff seed _).mpr
    exact ⟨copy, hcopy, rfl⟩
  unfold componentDecodedBoundaryLinks
    componentPhysicalDropDecodedBoundaryLinks
    componentPhysicalDropDecodedSupport
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨slabPlaquetteAt extent copy.faceId, hplaquette, ?_⟩
  rw [← hkey]
  exact hedge

/-! ## 3. A fixed `16^n` presence-bit carrier -/

/-- One bit per decoded candidate link records membership in the sparse row
key set. -/
def componentAuxiliaryRowPresenceWord
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : List Nat :=
  (componentDecodedBoundaryLinks seed).map fun link =>
    if link ∈ componentSparseAuxiliaryRowKeys seed then 1 else 0

/-- Pad the presence word with zeros to exactly four bits per peel entry. -/
def componentAuxiliaryRowPresenceCode
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : List Nat :=
  componentAuxiliaryRowPresenceWord seed ++
    List.replicate
      (4 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length -
        (componentAuxiliaryRowPresenceWord seed).length) 0

/-- The padded key word has the fixed advertised length. -/
theorem componentAuxiliaryRowPresenceCode_length
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    (componentAuxiliaryRowPresenceCode seed).length =
      4 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold componentAuxiliaryRowPresenceCode
  rw [List.length_append, List.length_replicate]
  have hbound :=
    componentDecodedBoundaryLinks_length_le_four_mul_peelFaces seed
  unfold componentAuxiliaryRowPresenceWord at ⊢
  rw [List.length_map]
  omega

/-- Every entry of the padded key word is a bit. -/
theorem componentAuxiliaryRowPresenceCode_entry_lt_two
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment)
    (value : Nat) (hvalue : value ∈
      componentAuxiliaryRowPresenceCode seed) : value < 2 := by
  unfold componentAuxiliaryRowPresenceCode at hvalue
  rcases List.mem_append.mp hvalue with hword | hpadding
  · unfold componentAuxiliaryRowPresenceWord at hword
    obtain ⟨link, _, rfl⟩ := List.mem_map.mp hword
    by_cases hlink : link ∈ componentSparseAuxiliaryRowKeys seed <;>
      simp [hlink]
  · have hzero : value = 0 := by
      exact (List.mem_replicate.mp hpadding).2
    omega

/-- Every production key code belongs to the fixed binary carrier. -/
theorem componentAuxiliaryRowPresenceCode_mem_carrier
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    componentAuxiliaryRowPresenceCode seed ∈ allSeqs 2
      (4 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length) := by
  apply mem_allSeqs
  · exact componentAuxiliaryRowPresenceCode_length seed
  · exact componentAuxiliaryRowPresenceCode_entry_lt_two seed

/-- The key carrier has exactly `16^peelSize` words. -/
theorem componentAuxiliaryRowPresenceCarrier_length (peelSize : Nat) :
    (allSeqs 2 (4 * peelSize)).length = 16 ^ peelSize := by
  rw [length_allSeqs, Nat.pow_mul]

/-! ## 4. Exact membership decoding -/

private theorem getD_append_left_of_ltLocal
    {A : Type} (left right : List A) (index : Nat) (fallback : A)
    (hindex : index < left.length) :
    (left ++ right).getD index fallback = left.getD index fallback := by
  induction left generalizing index with
  | nil => simp at hindex
  | cons head tail induction =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hindex
          simpa using induction index hindex

private theorem getD_map_of_ltLocal
    {A B : Type} (map : A -> B) (source : List A) (index : Nat)
    (hindex : index < source.length) (sourceFallback : A)
    (targetFallback : B) :
    (source.map map).getD index targetFallback =
      map (source.getD index sourceFallback) := by
  induction source generalizing index with
  | nil => simp at hindex
  | cons head tail induction =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hindex
          simpa using induction index hindex

/-- At a decoded candidate link, the padded production code returns exactly
its row-presence bit. -/
theorem componentAuxiliaryRowPresenceCode_getD
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment)
    (link : SlabLink) (hlink : link ∈ componentDecodedBoundaryLinks seed) :
    (componentAuxiliaryRowPresenceCode seed).getD
        (listIndexOf link (componentDecodedBoundaryLinks seed)) 0 =
      if link ∈ componentSparseAuxiliaryRowKeys seed then 1 else 0 := by
  have hindex := listIndexOf_lt_of_mem link
    (componentDecodedBoundaryLinks seed) hlink
  unfold componentAuxiliaryRowPresenceCode
  rw [getD_append_left_of_ltLocal _ _ _ _ (by
    unfold componentAuxiliaryRowPresenceWord
    rw [List.length_map]
    exact hindex)]
  unfold componentAuxiliaryRowPresenceWord
  rw [getD_map_of_ltLocal _ _ _ hindex link 0,
    getD_listIndexOf_of_mem link link
      (componentDecodedBoundaryLinks seed) hlink]

/-- Decode whether a requested link belongs to the sparse row-key set. -/
def componentAuxiliaryRowPresenceDecode
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (presenceCode : List Nat) (link : SlabLink) : Bool :=
  let candidates :=
    componentPhysicalDropDecodedBoundaryLinks extent rootFaceId shapeCode
  if link ∈ candidates then
    decide (presenceCode.getD (listIndexOf link candidates) 0 = 1)
  else false

/-- The production presence decoder is exactly sparse-row key membership. -/
theorem componentAuxiliaryRowPresenceDecode_code
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment)
    (link : SlabLink) :
    componentAuxiliaryRowPresenceDecode extent seed.root.faceId
        (componentPlaquettePaddedTourCode seed)
        (componentAuxiliaryRowPresenceCode seed) link =
      decide (link ∈ componentSparseAuxiliaryRowKeys seed) := by
  by_cases hkey : link ∈ componentSparseAuxiliaryRowKeys seed
  · have hcandidates :=
      componentSparseAuxiliaryRowKey_mem_decodedBoundaryLinks
        seed link hkey
    unfold componentAuxiliaryRowPresenceDecode
    change (if link ∈ componentDecodedBoundaryLinks seed then
      decide ((componentAuxiliaryRowPresenceCode seed).getD
        (listIndexOf link (componentDecodedBoundaryLinks seed)) 0 = 1)
      else false) = decide (link ∈ componentSparseAuxiliaryRowKeys seed)
    rw [if_pos hcandidates,
      componentAuxiliaryRowPresenceCode_getD seed link hcandidates]
    simp [hkey]
  · unfold componentAuxiliaryRowPresenceDecode
    change (if link ∈ componentDecodedBoundaryLinks seed then
      decide ((componentAuxiliaryRowPresenceCode seed).getD
        (listIndexOf link (componentDecodedBoundaryLinks seed)) 0 = 1)
      else false) = decide (link ∈ componentSparseAuxiliaryRowKeys seed)
    by_cases hcandidates : link ∈ componentDecodedBoundaryLinks seed
    · rw [if_pos hcandidates,
        componentAuxiliaryRowPresenceCode_getD seed link hcandidates]
      simp [hkey]
    · rw [if_neg hcandidates]
      simp [hkey]

/-- At a common literal root face, equal shape and presence words force the
same sparse auxiliary row-key support. -/
theorem componentProductionCodes_eq_auxiliaryRowKey_mem_iff
    {K extent : Nat} {physical : SlabLabelling}
    {leftAssignment rightAssignment : SlabFusionWitnessAssignment}
    {hleftAssignment : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    {hrightAssignment : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (left : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        leftAssignment hleftAssignment)
    (right : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        rightAssignment hrightAssignment)
    (hroot : left.root.faceId = right.root.faceId)
    (hshape : componentPlaquettePaddedTourCode left =
      componentPlaquettePaddedTourCode right)
    (hpresence : componentAuxiliaryRowPresenceCode left =
      componentAuxiliaryRowPresenceCode right)
    (link : SlabLink) :
    link ∈ componentSparseAuxiliaryRowKeys left ↔
      link ∈ componentSparseAuxiliaryRowKeys right := by
  have hdecode :
      componentAuxiliaryRowPresenceDecode extent left.root.faceId
          (componentPlaquettePaddedTourCode left)
          (componentAuxiliaryRowPresenceCode left) link =
        componentAuxiliaryRowPresenceDecode extent right.root.faceId
          (componentPlaquettePaddedTourCode right)
          (componentAuxiliaryRowPresenceCode right) link := by
    rw [hroot, hshape, hpresence]
  rw [componentAuxiliaryRowPresenceDecode_code left,
    componentAuxiliaryRowPresenceDecode_code right] at hdecode
  constructor
  · intro hleft
    have htrue : decide (link ∈ componentSparseAuxiliaryRowKeys left) = true :=
      decide_eq_true hleft
    rw [hdecode] at htrue
    exact of_decide_eq_true htrue
  · intro hright
    have htrue : decide (link ∈ componentSparseAuxiliaryRowKeys right) = true :=
      decide_eq_true hright
    rw [← hdecode] at htrue
    exact of_decide_eq_true htrue

#print axioms componentPhysicalDropDecodedBoundaryLinks
#print axioms componentDecodedBoundaryLinks
#print axioms componentDecodedBoundaryLinks_nodup
#print axioms componentDecodedBoundaryLinks_length_le_four_mul_peelFaces
#print axioms componentSparseAuxiliaryRowKeys
#print axioms componentSparseAuxiliaryRowKeys_nodup
#print axioms componentSparseAuxiliaryRowKey_mem_decodedBoundaryLinks
#print axioms componentAuxiliaryRowPresenceWord
#print axioms componentAuxiliaryRowPresenceCode
#print axioms componentAuxiliaryRowPresenceCode_length
#print axioms componentAuxiliaryRowPresenceCode_entry_lt_two
#print axioms componentAuxiliaryRowPresenceCode_mem_carrier
#print axioms componentAuxiliaryRowPresenceCarrier_length
#print axioms componentAuxiliaryRowPresenceCode_getD
#print axioms componentAuxiliaryRowPresenceDecode
#print axioms componentAuxiliaryRowPresenceDecode_code
#print axioms componentProductionCodes_eq_auxiliaryRowKey_mem_iff

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowKeyCode
