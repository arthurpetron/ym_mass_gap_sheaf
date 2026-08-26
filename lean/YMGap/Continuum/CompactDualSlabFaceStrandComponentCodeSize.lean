/-
# The complete sparse drop code is controlled by its physical peel word

The auxiliary row bound is phrased in terms of the duplicate-free rooted
component list, while the stored physical code is the face-ID peel word.  This
module connects the two counts constructively.

Enumerate every bounded physical face-strand copy by a physical face ID and a
`Fin` slot, then filter that list by the rooted-component selector.  A direct
finite-range count proves that the filtered enumeration has exactly the same
length as the serialized peel word.  Every component copy embeds in that
filtered enumeration, so duplicate-freeness gives

```text
component.length <= peelFaces.length.
```

Together with the four-boundary-link row charge, the auxiliary table has at
most four rows per stored physical peel entry, and the complete two-part code
has at most five rows per peel entry.

Constructive contract: finite ranges, filters, explicit component membership,
and duplicate-free list pigeonhole only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Boolean counts are filtered finite-range lengths -/

/-- Filtering after a finite map has the same length as filtering its source
by the pulled-back Boolean predicate. -/
theorem filter_map_length_local {A B : Type}
    (map : A -> B) (selected : B -> Bool) : forall items : List A,
    (((items.map map).filter selected).length) =
      ((items.filter fun item => selected (map item)).length)
  | [] => rfl
  | head :: tail => by
      cases hselected : selected (map head) with
      | false =>
          simp only [List.map_cons, List.filter_cons, hselected,
            Bool.false_eq_true, ↓reduceIte]
          exact filter_map_length_local map selected tail
      | true =>
          simp only [List.map_cons, List.filter_cons, hselected,
            ↓reduceIte, List.length_cons]
          rw [filter_map_length_local map selected tail]

/-- A translated Boolean interval count is exactly the length of the
correspondingly filtered `Fin` range. -/
theorem finRange_filter_length_eq_boolCountFrom
    (selected : Nat -> Bool) : forall (start length : Nat),
    ((List.finRange length).filter fun offset =>
        selected (start + offset.val)).length =
      boolCountFrom selected start length
  | _, 0 => rfl
  | start, length + 1 => by
      rw [List.finRange_succ]
      have htailMap := filter_map_length_local
        (fun offset : Fin length => Fin.succ offset)
        (fun offset : Fin (length + 1) =>
          selected (start + offset.val))
        (List.finRange length)
      have htailPredicate :
          ((List.finRange length).filter fun offset =>
              selected (start + (Fin.succ offset).val)).length =
            ((List.finRange length).filter fun offset =>
              selected ((start + 1) + offset.val)).length := by
        congr 2
        funext offset
        congr 1
        simp only [Fin.val_succ]
        omega
      simp only [List.filter_cons, Fin.val_zero, Nat.add_zero]
      by_cases hselected : selected start = true
      · simp only [hselected, ↓reduceIte, List.length_cons]
        rw [htailMap, htailPredicate,
          finRange_filter_length_eq_boolCountFrom
            selected (start + 1) length,
          boolCountFrom]
        simp [hselected, boolIndicator]
        omega
      · have hfalse : selected start = false :=
          Bool.eq_false_iff.mpr hselected
        simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
        rw [htailMap, htailPredicate,
          finRange_filter_length_eq_boolCountFrom
            selected (start + 1) length,
          boolCountFrom]
        simp [hfalse, boolIndicator]

/-! ## 2. Enumerate and count selected physical face copies -/

/-- Every bounded strand slot of one physical face, as literal face-copy
data. -/
def faceStrandCopiesAt
    (physical : SlabLabelling) (faceId : Nat) :
    List (SlabFaceStrandCopy physical) :=
  (List.finRange (physical faceId)).map fun slot =>
    { faceId := faceId, slot := slot }

/-- Filtering one face's copy enumeration counts exactly its selected slots. -/
theorem faceStrandCopiesAt_filter_length
    {physical : SlabLabelling}
    (selected : SlabFaceStrandCopy physical -> Bool)
    (faceId : Nat) :
    ((faceStrandCopiesAt physical faceId).filter selected).length =
      slabFaceStrandSelectionCount selected faceId := by
  unfold faceStrandCopiesAt slabFaceStrandSelectionCount
  rw [filter_map_length_local]
  simpa only [Nat.zero_add, slabFaceStrandSelectionAt_fin] using
    (finRange_filter_length_eq_boolCountFrom
      (slabFaceStrandSelectionAt selected faceId)
      0 (physical faceId))

/-- Enumerate every bounded strand copy over the corrected-slab physical face
carrier. -/
def slabPhysicalFaceStrandCopies
    (extent : Nat) (physical : SlabLabelling) :
    List (SlabFaceStrandCopy physical) :=
  (slabPhysicalFaceEdges extent).flatMap
    (faceStrandCopiesAt physical)

/-- Over any face-ID list, selected copy enumeration and replication by the
per-face selection count have equal lengths. -/
theorem selectedFaceStrandCopiesFrom_length_eq_dropListFrom
    {physical : SlabLabelling}
    (selected : SlabFaceStrandCopy physical -> Bool) :
    forall faceIds : List Nat,
    (((faceIds.flatMap (faceStrandCopiesAt physical)).filter selected).length) =
      (faceIds.flatMap fun faceId =>
        List.replicate
          (slabFaceStrandSelectionCount selected faceId) faceId).length
  | [] => rfl
  | faceId :: faceIds => by
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.length_replicate]
      rw [faceStrandCopiesAt_filter_length selected faceId,
        selectedFaceStrandCopiesFrom_length_eq_dropListFrom selected faceIds]

/-- The filtered global physical-copy enumeration has exactly the serialized
physical peel length. -/
theorem slabPhysicalFaceStrandCopies_filter_length_eq_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    ((slabPhysicalFaceStrandCopies extent physical).filter seed.selected).length =
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold slabPhysicalFaceStrandCopies
    SlabFusionWitnessFaceStrandSeed.peelFaces slabFaceDropList
  exact selectedFaceStrandCopiesFrom_length_eq_dropListFrom
    seed.selected (slabPhysicalFaceEdges extent)

/-! ## 3. Embed the rooted component and contract the complete code size -/

/-- Every rooted-component copy occurs in the filtered global physical-copy
enumeration. -/
theorem SlabFusionWitnessFaceStrandSeed.component_mem_filteredPhysicalCopies
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (copy : SlabFaceStrandCopy physical)
    (hcopy : copy ∈ seed.component) :
    copy ∈
      (slabPhysicalFaceStrandCopies extent physical).filter seed.selected := by
  apply List.mem_filter.mpr
  constructor
  · unfold slabPhysicalFaceStrandCopies
    apply List.mem_flatMap.mpr
    refine ⟨copy.faceId,
      SlabFusionWitnessFaceStrandSeed.component_faceId_physical
        seed copy hcopy, ?_⟩
    unfold faceStrandCopiesAt
    apply List.mem_map.mpr
    exact ⟨copy.slot, List.mem_finRange copy.slot, by cases copy; rfl⟩
  · simp [SlabFaceStrandSeed.selected, hcopy]

/-- The duplicate-free component contains no more copies than its exact
serialized peel word. -/
theorem SlabFusionWitnessFaceStrandSeed.component_length_le_peelFaces_length
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    seed.component.length <=
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  have hbound := CayleyPruferInjection.nodup_subset_length_le
    seed.component
    ((slabPhysicalFaceStrandCopies extent physical).filter seed.selected)
    (by
      unfold SlabFaceStrandSeed.component
      exact rootComponent_nodup _ _ _)
    (fun copy hcopy =>
      SlabFusionWitnessFaceStrandSeed.component_mem_filteredPhysicalCopies
        seed copy hcopy)
  rw [slabPhysicalFaceStrandCopies_filter_length_eq_peelFaces seed] at hbound
  exact hbound

/-- The sparse auxiliary table has at most four rows per physical peel entry. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWords_length_le_four_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hnodup : links.Nodup) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords.length <=
      4 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  have hrows :=
    SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWords_length_le_four_mul_component
      seed hnodup
  have hcomponent :=
    SlabFusionWitnessFaceStrandSeed.component_length_le_peelFaces_length seed
  omega

/-- **Complete sparse-code size contraction.**  Counting physical peel entries
and retained auxiliary rows together costs at most five entries per physical
peel entry. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_totalRows_length_le_five_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hnodup : links.Nodup) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).physicalFaces.length +
        (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords.length <=
      5 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  have hrows :=
    SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWords_length_le_four_mul_peelFaces
      seed hnodup
  change (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length +
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords.length <=
    5 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length
  omega

#print axioms filter_map_length_local
#print axioms finRange_filter_length_eq_boolCountFrom
#print axioms faceStrandCopiesAt
#print axioms faceStrandCopiesAt_filter_length
#print axioms slabPhysicalFaceStrandCopies
#print axioms selectedFaceStrandCopiesFrom_length_eq_dropListFrom
#print axioms slabPhysicalFaceStrandCopies_filter_length_eq_peelFaces
#print axioms SlabFusionWitnessFaceStrandSeed.component_mem_filteredPhysicalCopies
#print axioms SlabFusionWitnessFaceStrandSeed.component_length_le_peelFaces_length
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWords_length_le_four_mul_peelFaces
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_totalRows_length_le_five_mul_peelFaces

end YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize
