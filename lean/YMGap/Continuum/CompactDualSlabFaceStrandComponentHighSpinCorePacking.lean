/-
# Pack core-attached strand components into the finite low-spin carrier

A blocked high-spin reserve check now carries an actual selected strand copy
whose slot is below the threshold.  This module contracts that local anchor
data into a family-level cardinality bound.

For one physical face, enumerate only the slots below both its actual
twice-spin label and the threshold.  Flat-mapping this enumeration over the
corrected-slab physical faces gives a duplicate-free finite core carrier of
size at most

```text
(number of physical faces) * threshold.
```

A constructively separated family of core-attached rooted components chooses
either equality or disjoint support for every two displayed entries.  Equal
anchor copies cannot lie in disjoint components, so the anchor map is
injective on the family.  Finite pigeonhole then bounds the number of family
entries by the finite core carrier.

This is the packing step only.  It does not yet construct the exhaustive
canonical component family, sum exterior decorations attached to the core,
or prove a finite-core spectral estimate.

Constructive contract: finite ranges, duplicate-free lists, explicit
equal-or-disjoint component data, and finite pigeonhole only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreAnchor
import YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCorePacking

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreAnchor
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The finite core-copy carrier -/

/-- The literal strand copies on one face whose slots are below `threshold`.
The `min` records simultaneously the physical slot bound and the core bound. -/
def faceCoreStrandCopiesAt
    (physical : SlabLabelling) (threshold faceId : Nat) :
    List (SlabFaceStrandCopy physical) :=
  (List.finRange (min (physical faceId) threshold)).map fun slot =>
    { faceId := faceId
      slot :=
        ⟨slot.val,
          Nat.lt_of_lt_of_le slot.isLt (Nat.min_le_left _ _)⟩ }

@[simp] theorem faceCoreStrandCopiesAt_length
    (physical : SlabLabelling) (threshold faceId : Nat) :
    (faceCoreStrandCopiesAt physical threshold faceId).length =
      min (physical faceId) threshold := by
  simp [faceCoreStrandCopiesAt]

/-- A physical copy below the threshold occurs in its face's core block. -/
theorem mem_faceCoreStrandCopiesAt_of_slot_lt
    {physical : SlabLabelling} {threshold : Nat}
    (copy : SlabFaceStrandCopy physical)
    (hslot : copy.slot.val < threshold) :
    copy ∈ faceCoreStrandCopiesAt physical threshold copy.faceId := by
  let coreSlot : Fin (min (physical copy.faceId) threshold) :=
    ⟨copy.slot.val, by omega⟩
  unfold faceCoreStrandCopiesAt
  apply List.mem_map.mpr
  refine ⟨coreSlot, List.mem_finRange coreSlot, ?_⟩
  cases copy with
  | mk faceId slot =>
      congr 1

private theorem nodup_map_of_injective
    {A B : Type} (map : A -> B)
    (hinjective : ∀ {left right}, map left = map right -> left = right) :
    ∀ {items : List A}, items.Nodup -> (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_of_injective map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective heq) ▸ hitem)

private theorem finRange_nodup :
    ∀ count : Nat, (List.finRange count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.finRange_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, _, heq⟩ := List.mem_map.mp hmem
        have hvalue := congrArg Fin.val heq
        simp at hvalue
      · exact nodup_map_of_injective Fin.succ
          (fun heq => by
            apply Fin.ext
            have hvalue := congrArg Fin.val heq
            simp only [Fin.val_succ] at hvalue
            omega)
          (finRange_nodup count)

private theorem range_nodup : ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨range_nodup count,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro item hitem last hlast heq
      have hlastEq : last = count := List.mem_singleton.mp hlast
      exact Nat.ne_of_lt (List.mem_range.mp hitem) (heq.trans hlastEq)

/-- One face's finite core block is duplicate-free. -/
theorem faceCoreStrandCopiesAt_nodup
    (physical : SlabLabelling) (threshold faceId : Nat) :
    (faceCoreStrandCopiesAt physical threshold faceId).Nodup := by
  unfold faceCoreStrandCopiesAt
  apply nodup_map_of_injective
  · intro left right heq
    apply Fin.ext
    exact congrArg (fun copy : SlabFaceStrandCopy physical => copy.slot.val) heq
  · exact finRange_nodup _

/-- Every low-spin copy over the corrected-slab physical face carrier. -/
def slabFiniteCoreFaceStrandCopies
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat) :
    List (SlabFaceStrandCopy physical) :=
  (slabPhysicalFaceEdges extent).flatMap
    (faceCoreStrandCopiesAt physical threshold)

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A -> List B) :
    ∀ source : List A, source.Nodup ->
      (∀ item, item ∈ source -> (block item).Nodup) ->
      (∀ left, left ∈ source -> ∀ right, right ∈ source ->
        left ≠ right -> ∀ value, value ∈ block left ->
          value ∉ block right) ->
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := by
        rw [heq]
        exact htail
      obtain ⟨item, hitem, hvalueItem⟩ :=
        List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro heqItem
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

/-- The complete finite core-copy carrier has no duplicate copy. -/
theorem slabFiniteCoreFaceStrandCopies_nodup
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat) :
    (slabFiniteCoreFaceStrandCopies extent physical threshold).Nodup := by
  unfold slabFiniteCoreFaceStrandCopies
  apply nodup_flatMap_of_disjoint_blocks
  · unfold slabPhysicalFaceEdges
    exact range_nodup _
  · intro faceId _
    exact faceCoreStrandCopiesAt_nodup physical threshold faceId
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftSlot, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightSlot, _, hrightEq⟩ := List.mem_map.mp hright
    have hface : left = right := by
      exact congrArg SlabFaceStrandCopy.faceId
        (hleftEq.trans hrightEq.symm)
    exact hne hface

private theorem length_flatMap_le
    {A B : Type} (block : A -> List B) (bound : Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items -> (block item).length <= bound) ->
      (items.flatMap block).length <= items.length * bound
  | [], _ => by simp
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := length_flatMap_le block bound tail
        (fun item hitem => hbound item (List.mem_cons_of_mem head hitem))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- The finite core has at most `threshold` copies per physical face. -/
theorem slabFiniteCoreFaceStrandCopies_length_le
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat) :
    (slabFiniteCoreFaceStrandCopies extent physical threshold).length <=
      (slabPhysicalFaceEdges extent).length * threshold := by
  unfold slabFiniteCoreFaceStrandCopies
  apply length_flatMap_le
  intro faceId _
  rw [faceCoreStrandCopiesAt_length]
  exact Nat.min_le_right _ _

/-! ## 2. Core-anchored component families -/

/-- One rooted component together with its decoded selected finite-core copy. -/
structure SlabCoreAnchoredComponent
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold : Nat) : Type where
  seed : SlabFusionWitnessFaceStrandSeed
    K extent physical links assignment hassignment
  anchor : SlabComponentCoreAnchor seed threshold

/-- Constructive separation data for a displayed component family.  Equality
is supplied positively; otherwise the two rooted supports are disjoint. -/
def SlabCoreAnchoredFamilySeparated
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {threshold : Nat}
    (entries : List (SlabCoreAnchoredComponent K extent physical links
      assignment hassignment threshold)) : Prop :=
  ∀ left, left ∈ entries -> ∀ right, right ∈ entries ->
    (left = right) ∨ SupportsDisjoint left.seed.component right.seed.component

/-- The decoded anchor is literally a member of its rooted component. -/
theorem SlabCoreAnchoredComponent.anchor_mem_component
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {threshold : Nat}
    (entry : SlabCoreAnchoredComponent K extent physical links assignment
      hassignment threshold) :
    entry.anchor.copy ∈ entry.seed.component := by
  have hselected := entry.anchor.selected_true
  unfold SlabFaceStrandSeed.selected at hselected
  exact of_decide_eq_true hselected

/-- Every decoded anchor lies in the global finite core carrier. -/
theorem SlabCoreAnchoredComponent.anchor_mem_finiteCore
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {threshold : Nat}
    (entry : SlabCoreAnchoredComponent K extent physical links assignment
      hassignment threshold) :
    entry.anchor.copy ∈
      slabFiniteCoreFaceStrandCopies extent physical threshold := by
  unfold slabFiniteCoreFaceStrandCopies
  apply List.mem_flatMap.mpr
  exact ⟨entry.anchor.copy.faceId, entry.anchor.face_physical,
    mem_faceCoreStrandCopiesAt_of_slot_lt
      entry.anchor.copy entry.anchor.slot_core⟩

/-- On a constructively separated family, equal anchor copies force equal
component entries. -/
theorem coreAnchorCopy_injective_on_separated_family
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {threshold : Nat}
    (entries : List (SlabCoreAnchoredComponent K extent physical links
      assignment hassignment threshold))
    (hseparated : SlabCoreAnchoredFamilySeparated entries) :
    ∀ left, left ∈ entries -> ∀ right, right ∈ entries ->
      left.anchor.copy = right.anchor.copy -> left = right := by
  intro left hleft right hright hcopy
  cases hseparated left hleft right hright with
  | inl heq => exact heq
  | inr hdisjoint =>
      exact False.elim
        (hdisjoint left.anchor.copy left.anchor_mem_component
          (hcopy ▸ right.anchor_mem_component))

/-- Distinct constructively separated core-attached components inject into
the finite low-spin copy carrier. -/
theorem coreAnchoredComponentFamily_length_le_finiteCore
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {threshold : Nat}
    (entries : List (SlabCoreAnchoredComponent K extent physical links
      assignment hassignment threshold))
    (hnodup : entries.Nodup)
    (hseparated : SlabCoreAnchoredFamilySeparated entries) :
    entries.length <=
      (slabFiniteCoreFaceStrandCopies extent physical threshold).length := by
  let anchorCopy := fun entry : SlabCoreAnchoredComponent K extent physical
      links assignment hassignment threshold => entry.anchor.copy
  have hanchorNodup : (entries.map anchorCopy).Nodup :=
    CayleyPruferInjection.nodup_map_of_injOn anchorCopy entries hnodup
      (coreAnchorCopy_injective_on_separated_family
        entries hseparated)
  have hbound := CayleyPruferInjection.nodup_subset_length_le
    (entries.map anchorCopy)
    (slabFiniteCoreFaceStrandCopies extent physical threshold)
    hanchorNodup
    (fun copy hcopy => by
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hcopy
      rw [← heq]
      exact entry.anchor_mem_finiteCore)
  simpa only [List.length_map] using hbound

/-- Final packing form: there are at most `threshold` core-attached disjoint
components per physical face. -/
theorem coreAnchoredComponentFamily_length_le_faces_mul_threshold
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {threshold : Nat}
    (entries : List (SlabCoreAnchoredComponent K extent physical links
      assignment hassignment threshold))
    (hnodup : entries.Nodup)
    (hseparated : SlabCoreAnchoredFamilySeparated entries) :
    entries.length <= (slabPhysicalFaceEdges extent).length * threshold :=
  Nat.le_trans
    (coreAnchoredComponentFamily_length_le_finiteCore
      entries hnodup hseparated)
    (slabFiniteCoreFaceStrandCopies_length_le extent physical threshold)

#print axioms faceCoreStrandCopiesAt
#print axioms faceCoreStrandCopiesAt_length
#print axioms mem_faceCoreStrandCopiesAt_of_slot_lt
#print axioms faceCoreStrandCopiesAt_nodup
#print axioms slabFiniteCoreFaceStrandCopies
#print axioms slabFiniteCoreFaceStrandCopies_nodup
#print axioms slabFiniteCoreFaceStrandCopies_length_le
#print axioms SlabCoreAnchoredComponent
#print axioms SlabCoreAnchoredFamilySeparated
#print axioms SlabCoreAnchoredComponent.anchor_mem_component
#print axioms SlabCoreAnchoredComponent.anchor_mem_finiteCore
#print axioms coreAnchorCopy_injective_on_separated_family
#print axioms coreAnchoredComponentFamily_length_le_finiteCore
#print axioms coreAnchoredComponentFamily_length_le_faces_mul_threshold

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCorePacking
