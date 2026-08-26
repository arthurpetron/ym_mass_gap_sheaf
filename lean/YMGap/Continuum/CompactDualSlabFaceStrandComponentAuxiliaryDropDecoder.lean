/-
# Decode the sparse auxiliary table from component-relative codes

The presence code recovers the sparse row-key set.  Filtering the complete
slab link carrier by that decoded predicate restores the production key order,
because sparse encoding itself is a filter of that carrier.  Each row width is
then determined by its link's canonical auxiliary-coordinate list, so the
decoded flattened value word can be split back into the exact sparse table.

This supplies the missing left inverse for the auxiliary part of the component
code.  Equal rooted shape, key-presence, and auxiliary-value codes force equal
sparse auxiliary tables and hence equal decoded auxiliary drops.

Constructive contract: Boolean filters, list `take`/`drop`, and the existing
weak-composition decoder only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowKeyCode

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryDropDecoder

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowKeyCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Recover the canonical sparse key order -/

/-- Sparse row keys are literally a Boolean filter of the source link list. -/
theorem sparseAuxiliaryDropKeysFrom_eq_filter
    (wordAt : SlabLink -> List Nat) : forall links : List SlabLink,
    (slabSparseAuxiliaryDropWordsFrom links wordAt).map Prod.fst =
      links.filter fun link => !(finiteWordAllZeroB (wordAt link))
  | [] => rfl
  | head :: tail => by
      cases hzero : finiteWordAllZeroB (wordAt head) with
      | false =>
          simp [slabSparseAuxiliaryDropWordsFrom, hzero,
            sparseAuxiliaryDropKeysFrom_eq_filter]
      | true =>
          simp [slabSparseAuxiliaryDropWordsFrom, hzero,
            sparseAuxiliaryDropKeysFrom_eq_filter]

private theorem filterByFilteredMembership {A : Type}
    [BEq A] [LawfulBEq A]
    (items : List A) (predicate : A -> Bool) :
    items.filter (fun item => decide (item ∈ items.filter predicate)) =
      items.filter predicate := by
  apply List.filter_congr
  intro item hitem
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hdecision
    have hmem : item ∈ items.filter predicate :=
      of_decide_eq_true hdecision
    exact (List.mem_filter.mp hmem).2
  · intro hpredicate
    exact decide_eq_true (List.mem_filter.mpr ⟨hitem, hpredicate⟩)

/-- Filtering the original source carrier by membership in its own sparse key
list returns that key list in its original order. -/
theorem filterBySparseAuxiliaryDropKeys_eq_keys
    (links : List SlabLink) (wordAt : SlabLink -> List Nat) :
    links.filter (fun link => decide (link ∈
      (slabSparseAuxiliaryDropWordsFrom links wordAt).map Prod.fst)) =
      (slabSparseAuxiliaryDropWordsFrom links wordAt).map Prod.fst := by
  rw [sparseAuxiliaryDropKeysFrom_eq_filter]
  exact filterByFilteredMembership links
    (fun link => !(finiteWordAllZeroB (wordAt link)))

/-- Decode the production sparse keys in the canonical complete-slab order. -/
def componentAuxiliaryRowKeysDecode
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (presenceCode : List Nat) : List SlabLink :=
  (boundaryCompleteSlabLinks extent).filter fun link =>
    componentAuxiliaryRowPresenceDecode extent rootFaceId
      shapeCode presenceCode link

/-- The witness-independent key decoder returns the literal production key
list, not only a support-equivalent permutation. -/
theorem componentAuxiliaryRowKeysDecode_code
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    componentAuxiliaryRowKeysDecode extent seed.root.faceId
        (componentPlaquettePaddedTourCode seed)
        (componentAuxiliaryRowPresenceCode seed) =
      componentSparseAuxiliaryRowKeys seed := by
  unfold componentAuxiliaryRowKeysDecode
  have hpredicate :
      (fun link => componentAuxiliaryRowPresenceDecode extent seed.root.faceId
        (componentPlaquettePaddedTourCode seed)
        (componentAuxiliaryRowPresenceCode seed) link) =
      (fun link => decide (link ∈ componentSparseAuxiliaryRowKeys seed)) := by
    funext link
    exact componentAuxiliaryRowPresenceDecode_code seed link
  rw [hpredicate]
  unfold componentSparseAuxiliaryRowKeys
    SlabFusionWitnessFaceStrandSeed.sparseDropCode
  exact filterBySparseAuxiliaryDropKeys_eq_keys
    (boundaryCompleteSlabLinks extent)
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)

/-! ## 2. Split the flattened value word at link-determined widths -/

/-- Split a flat value list according to the canonical auxiliary-coordinate
width attached to each ordered link key. -/
def auxiliaryRowsFromKeysAndValues (extent : Nat) :
    List SlabLink -> List Nat -> List (SlabLink × List Nat)
  | [], _ => []
  | link :: links, values =>
      let width := (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length).length
      (link, values.take width) ::
        auxiliaryRowsFromKeysAndValues extent links (values.drop width)

/-- Every retained production row has exactly the link-determined width. -/
theorem sparseDropCode_row_length_eq_canonicalWidth
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment)
    (entry : SlabLink × List Nat)
    (hentry : entry ∈
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords) :
    entry.2.length = (canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent entry.1).length).length := by
  have hlink := sparseAuxiliaryDropRow_link_mem
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
    (boundaryCompleteSlabLinks extent) entry hentry
  have hword := sparseAuxiliaryDropRow_word_eq
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
    (boundaryCompleteSlabLinks extent) entry hentry
  rw [hword,
    SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_of_mem
      seed entry.1 hlink,
    List.length_map]

/-- Splitting the flattened values of a table whose row widths are determined
by their keys returns that table literally. -/
theorem auxiliaryRowsFromKeysAndValues_values (extent : Nat) : forall
    entries : List (SlabLink × List Nat),
    (forall entry, entry ∈ entries ->
      entry.2.length = (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent entry.1).length).length) ->
    auxiliaryRowsFromKeysAndValues extent (entries.map Prod.fst)
      (auxiliaryWordTableValues entries) = entries
  | [], _ => rfl
  | entry :: entries, hwidth => by
      have hhead := hwidth entry List.mem_cons_self
      have htail : forall next, next ∈ entries ->
          next.2.length = (canonicalUsedAuxiliaryCoordinates
            (slabIncidentPlaqIds extent next.1).length).length := by
        intro next hnext
        exact hwidth next (List.mem_cons_of_mem entry hnext)
      simp only [List.map_cons, auxiliaryWordTableValues,
        List.flatMap_cons, auxiliaryRowsFromKeysAndValues]
      rw [← hhead, List.take_append_length, List.drop_append_length]
      change entry :: auxiliaryRowsFromKeysAndValues extent
        (entries.map Prod.fst) (auxiliaryWordTableValues entries) =
          entry :: entries
      rw [auxiliaryRowsFromKeysAndValues_values extent entries htail]

/-! ## 3. Exact production auxiliary-table decoding -/

/-- Decode a sparse auxiliary table from the shape, presence, and flattened
value codes. -/
def componentAuxiliaryRowsDecode
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (presenceCode valueCode : List Nat) :
    List (SlabLink × List Nat) :=
  auxiliaryRowsFromKeysAndValues extent
    (componentAuxiliaryRowKeysDecode extent rootFaceId
      shapeCode presenceCode)
    (weakCompositionBinaryDecode valueCode)

/-- The three production auxiliary code words reconstruct the literal sparse
auxiliary row table. -/
theorem componentAuxiliaryRowsDecode_code
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    componentAuxiliaryRowsDecode extent seed.root.faceId
        (componentPlaquettePaddedTourCode seed)
        (componentAuxiliaryRowPresenceCode seed)
        (SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode seed) =
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords := by
  unfold componentAuxiliaryRowsDecode
  rw [componentAuxiliaryRowKeysDecode_code seed,
    SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryDecode seed]
  unfold componentSparseAuxiliaryRowKeys
    SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord
  apply auxiliaryRowsFromKeysAndValues_values
  exact sparseDropCode_row_length_eq_canonicalWidth seed

/-- Interpret the reconstructed sparse table as the total auxiliary drop at a
requested link. -/
def componentAuxiliaryDropDecode
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (presenceCode valueCode : List Nat) (link : SlabLink) : SlabLabelling :=
  wordToEdgeLabelling
    (canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length)
    (slabAuxiliaryDropWordAt link
      (componentAuxiliaryRowsDecode extent rootFaceId
        shapeCode presenceCode valueCode))

/-- On production words, the code-level auxiliary decoder equals the existing
sparse-drop decoder at every link. -/
theorem componentAuxiliaryDropDecode_code
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment)
    (link : SlabLink) :
    componentAuxiliaryDropDecode extent seed.root.faceId
        (componentPlaquettePaddedTourCode seed)
        (componentAuxiliaryRowPresenceCode seed)
        (SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode seed)
        link =
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).decodeAuxiliaryDrop
        extent link := by
  unfold componentAuxiliaryDropDecode
    SlabFaceStrandComponentDropCode.decodeAuxiliaryDrop
  rw [componentAuxiliaryRowsDecode_code seed]

/-- At a common literal root, equality of shape, key, and value codes forces
equality of the complete sparse auxiliary row tables. -/
theorem componentProductionCodes_eq_auxiliaryWords_eq
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
    (hvalues :
      SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode left =
      SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode right) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode left).auxiliaryWords =
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode right).auxiliaryWords := by
  rw [← componentAuxiliaryRowsDecode_code left,
    ← componentAuxiliaryRowsDecode_code right,
    hroot, hshape, hpresence, hvalues]

#print axioms sparseAuxiliaryDropKeysFrom_eq_filter
#print axioms filterBySparseAuxiliaryDropKeys_eq_keys
#print axioms componentAuxiliaryRowKeysDecode
#print axioms componentAuxiliaryRowKeysDecode_code
#print axioms auxiliaryRowsFromKeysAndValues
#print axioms sparseDropCode_row_length_eq_canonicalWidth
#print axioms auxiliaryRowsFromKeysAndValues_values
#print axioms componentAuxiliaryRowsDecode
#print axioms componentAuxiliaryRowsDecode_code
#print axioms componentAuxiliaryDropDecode
#print axioms componentAuxiliaryDropDecode_code
#print axioms componentProductionCodes_eq_auxiliaryWords_eq

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryDropDecoder
