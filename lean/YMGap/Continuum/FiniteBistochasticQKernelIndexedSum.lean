/-
# Indexed block sums of finite bistochastic kernels

A higher-valence associator is block diagonal in a retained intermediate
representation.  Repeating the row/column proof separately at every valence
obscures that simple structure.  This module gives the constructive direct-sum
compiler once and for all.

The index carrier is the proof-carrying attachment of an explicit duplicate-
free list.  Consequently every element of the source and target types belongs
to one written block.  Entries between distinct blocks are zero; entries in a
common block are the supplied finite bistochastic kernel.  The resulting
dependent sum is again exactly bistochastic.

Constructive contract: finite lists, decidable index equality, dependent
transport, and exact `Q'` algebra only; no choice, `Classical`, `sorry`, or new
axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernel
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

namespace YMGap.Continuum.FiniteBistochasticQKernelIndexedSum

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- An element of one source block over the proof-carrying written index
carrier. -/
structure IndexedSource {Index : Type} (indices : List Index)
    (Source : Index → Type) where
  index : {i // i ∈ indices}
  value : Source index.val

/-- An element of one target block over the same written index carrier. -/
structure IndexedTarget {Index : Type} (indices : List Index)
    (Target : Index → Type) where
  index : {i // i ∈ indices}
  value : Target index.val

/-- Concatenate the explicit source lists of all written blocks. -/
def indexedSources {Index : Type} (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i)) :
    List (IndexedSource indices Source) :=
  indices.attach.flatMap fun index =>
    (kernel index.val).sources.map fun source =>
      { index := index, value := source }

/-- Concatenate the explicit target lists of all written blocks. -/
def indexedTargets {Index : Type} (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i)) :
    List (IndexedTarget indices Target) :=
  indices.attach.flatMap fun index =>
    (kernel index.val).targets.map fun target =>
      { index := index, value := target }

private theorem nodup_map_of_injective {A B : Type} (map : A → B)
    (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective head item heq.symm) ▸ hitem)

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A → List B) :
    ∀ source : List A, source.Nodup →
      (∀ item, item ∈ source → (block item).Nodup) →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        left ≠ right → ∀ value, value ∈ block left →
          value ∉ block right) →
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
      have hvalueTail : value ∈ tail.flatMap block := heq ▸ htail
      obtain ⟨item, hitem, hvalueItem⟩ :=
        List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

theorem indexedSources_nodup {Index : Type}
    (indices : List Index) (indices_nodup : indices.Nodup)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (local_nodup : ∀ i, (kernel i).sources.Nodup) :
    (indexedSources indices Source Target kernel).Nodup := by
  unfold indexedSources
  apply nodup_flatMap_of_disjoint_blocks
  · exact attach_nodup_of_nodup _ indices_nodup
  · intro index _
    apply nodup_map_of_injective
    · intro left right heq
      cases heq
      rfl
    · exact local_nodup index.val
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftValue, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightValue, _, hrightEq⟩ := List.mem_map.mp hright
    have hindex : left = right := by
      exact congrArg (fun source => source.index)
        (hleftEq.trans hrightEq.symm)
    exact hne hindex

theorem indexedTargets_nodup {Index : Type}
    (indices : List Index) (indices_nodup : indices.Nodup)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (local_nodup : ∀ i, (kernel i).targets.Nodup) :
    (indexedTargets indices Source Target kernel).Nodup := by
  unfold indexedTargets
  apply nodup_flatMap_of_disjoint_blocks
  · exact attach_nodup_of_nodup _ indices_nodup
  · intro index _
    apply nodup_map_of_injective
    · intro left right heq
      cases heq
      rfl
    · exact local_nodup index.val
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftValue, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightValue, _, hrightEq⟩ := List.mem_map.mp hright
    have hindex : left = right := by
      exact congrArg (fun target => target.index)
        (hleftEq.trans hrightEq.symm)
    exact hne hindex

theorem indexedSources_complete {Index : Type}
    (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (local_complete : ∀ i source, source ∈ (kernel i).sources)
    (source : IndexedSource indices Source) :
    source ∈ indexedSources indices Source Target kernel := by
  rcases source with ⟨index, value⟩
  apply List.mem_flatMap.mpr
  refine ⟨index, List.mem_attach _ index, ?_⟩
  apply List.mem_map.mpr
  exact ⟨value, local_complete index.val value, rfl⟩

theorem indexedTargets_complete {Index : Type}
    (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (local_complete : ∀ i target, target ∈ (kernel i).targets)
    (target : IndexedTarget indices Target) :
    target ∈ indexedTargets indices Source Target kernel := by
  rcases target with ⟨index, value⟩
  apply List.mem_flatMap.mpr
  refine ⟨index, List.mem_attach _ index, ?_⟩
  apply List.mem_map.mpr
  exact ⟨value, local_complete index.val value, rfl⟩

/-- A constructive finite change of variables along an explicit two-sided
inverse preserves a nonnegative `listQSum`.  The lists need not have the same
written order. -/
theorem listQSum_equiv {A B : Type} [DecidableEq A] [DecidableEq B]
    (left : List A) (right : List B)
    (forward : A → B) (backward : B → A)
    (left_inverse : ∀ a, backward (forward a) = a)
    (right_inverse : ∀ b, forward (backward b) = b)
    (left_nodup : left.Nodup) (right_nodup : right.Nodup)
    (forward_mem : ∀ a, a ∈ left → forward a ∈ right)
    (backward_mem : ∀ b, b ∈ right → backward b ∈ left)
    (value : B → Q')
    (value_nonnegative : ∀ b, (0 : Q') ≤ value b) :
    listQSum (fun a => value (forward a)) left ≈
      listQSum value right := by
  have hforward :
      listQSum (fun a => value (forward a)) left ≤
        listQSum value right :=
    listQSum_le_of_injective left right
      (fun a => value (forward a)) value forward left_nodup
      forward_mem
      (by
        intro x _ y _ heq
        have h := congrArg backward heq
        simpa only [left_inverse] using h)
      (fun _ _ => Q'.le_refl' _)
      (fun b _ => value_nonnegative b)
  have hbackward :
      listQSum value right ≤
        listQSum (fun a => value (forward a)) left :=
    listQSum_le_of_injective right left value
      (fun a => value (forward a)) backward right_nodup
      backward_mem
      (by
        intro x _ y _ heq
        have h := congrArg forward heq
        simpa only [right_inverse] using h)
      (by
        intro b _
        change value b ≤ value (forward (backward b))
        rw [right_inverse]
        exact Q'.le_refl' _)
      (fun a _ => value_nonnegative (forward a))
  exact Int.le_antisymm hforward hbackward

/-- Zero-extended block-diagonal entry. -/
def indexedSumWeight {Index : Type} [DecidableEq Index]
    (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (source : IndexedSource indices Source)
    (target : IndexedTarget indices Target) : Q' :=
  if h : source.index = target.index then
    (kernel source.index.val).weight source.value (h.symm ▸ target.value)
  else 0

/-- On a common written sector, the zero-extended entry is exactly the local
block entry. -/
theorem indexedSumWeight_same {Index : Type} [DecidableEq Index]
    (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (index : {i // i ∈ indices})
    (source : Source index.val) (target : Target index.val) :
    indexedSumWeight indices Source Target kernel
        { index := index, value := source }
        { index := index, value := target } ≈
      (kernel index.val).weight source target := by
  simp only [indexedSumWeight, dite_true]
  exact Q'.eqv_refl _

/-- Distinct written sectors have zero coupling. -/
theorem indexedSumWeight_different {Index : Type} [DecidableEq Index]
    (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (source : IndexedSource indices Source)
    (target : IndexedTarget indices Target)
    (hindex : source.index ≠ target.index) :
    indexedSumWeight indices Source Target kernel source target ≈ 0 := by
  unfold indexedSumWeight
  rw [dif_neg hindex]
  exact Q'.eqv_refl _

theorem indexedSumWeight_nonnegative {Index : Type} [DecidableEq Index]
    (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (source : IndexedSource indices Source)
    (target : IndexedTarget indices Target) :
    (0 : Q') ≤ indexedSumWeight indices Source Target kernel source target := by
  unfold indexedSumWeight
  split
  · exact (kernel source.index.val).weight_nonnegative _ _
  · exact Q'.le_refl' 0

private theorem row_fiber_mass {Index : Type} [DecidableEq Index]
    (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (source : IndexedSource indices Source)
    (index : {i // i ∈ indices}) :
    listQSum
        (indexedSumWeight indices Source Target kernel source)
        ((kernel index.val).targets.map fun target =>
          ({ index := index, value := target } :
            IndexedTarget indices Target)) ≈
      deterministicKernel (fun _ : Unit => source.index) () index := by
  rcases source with ⟨sourceIndex, sourceValue⟩
  by_cases hindex : sourceIndex = index
  · subst index
    simp only [listQSum_map, indexedSumWeight, deterministicKernel,
      dite_true]
    exact (kernel sourceIndex.val).row_normalized sourceValue
  · have hreverse : index ≠ sourceIndex := fun h => hindex h.symm
    simp only [listQSum_map, indexedSumWeight, deterministicKernel,
      hindex, hreverse, dite_false]
    exact listQSum_zero _

private theorem column_fiber_mass {Index : Type} [DecidableEq Index]
    (indices : List Index)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (target : IndexedTarget indices Target)
    (index : {i // i ∈ indices}) :
    listQSum
        (fun source =>
          indexedSumWeight indices Source Target kernel source target)
        ((kernel index.val).sources.map fun source =>
          ({ index := index, value := source } :
            IndexedSource indices Source)) ≈
      deterministicKernel (fun _ : Unit => target.index) () index := by
  rcases target with ⟨targetIndex, targetValue⟩
  by_cases hindex : index = targetIndex
  · subst index
    simp only [listQSum_map, indexedSumWeight, deterministicKernel,
      dite_true]
    exact (kernel targetIndex.val).column_normalized targetValue
  · simp only [listQSum_map, indexedSumWeight, deterministicKernel,
      hindex, dite_false]
    exact listQSum_zero _

theorem indexedSumWeight_row_normalized
    {Index : Type} [DecidableEq Index]
    (indices : List Index) (indices_nodup : indices.Nodup)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (source : IndexedSource indices Source) :
    listQSum
        (indexedSumWeight indices Source Target kernel source)
        (indexedTargets indices Source Target kernel) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        listQSum
          (indexedSumWeight indices Source Target kernel source)
          ((kernel index.val).targets.map fun target =>
            ({ index := index, value := target } :
              IndexedTarget indices Target)))
      indices.attach) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (deterministicKernel (fun _ : Unit => source.index) ())
        indices.attach) _ ?_ ?_
    · exact listQSum_congr
        (fun index =>
          row_fiber_mass indices Source Target kernel source index)
        indices.attach
    · exact deterministicKernel_row_normalized
        (fun _ : Unit => source.index) () indices.attach
        (attach_nodup_of_nodup _ indices_nodup)
        (List.mem_attach _ source.index)

theorem indexedSumWeight_column_normalized
    {Index : Type} [DecidableEq Index]
    (indices : List Index) (indices_nodup : indices.Nodup)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i))
    (target : IndexedTarget indices Target) :
    listQSum
        (fun source =>
          indexedSumWeight indices Source Target kernel source target)
        (indexedSources indices Source Target kernel) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        listQSum
          (fun source =>
            indexedSumWeight indices Source Target kernel source target)
          ((kernel index.val).sources.map fun source =>
            ({ index := index, value := source } :
              IndexedSource indices Source)))
      indices.attach) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (deterministicKernel (fun _ : Unit => target.index) ())
        indices.attach) _ ?_ ?_
    · exact listQSum_congr
        (fun index =>
          column_fiber_mass indices Source Target kernel target index)
        indices.attach
    · exact deterministicKernel_row_normalized
        (fun _ : Unit => target.index) () indices.attach
        (attach_nodup_of_nodup _ indices_nodup)
        (List.mem_attach _ target.index)

/-- **A finite dependent direct sum of exact bistochastic blocks is exactly
bistochastic.** -/
def indexedSum {Index : Type} [DecidableEq Index]
    (indices : List Index) (indices_nodup : indices.Nodup)
    (Source Target : Index → Type)
    (kernel : ∀ i, FiniteBistochasticQKernel (Source i) (Target i)) :
    FiniteBistochasticQKernel
      (IndexedSource indices Source)
      (IndexedTarget indices Target) where
  sources := indexedSources indices Source Target kernel
  targets := indexedTargets indices Source Target kernel
  weight := indexedSumWeight indices Source Target kernel
  weight_nonnegative := indexedSumWeight_nonnegative indices Source Target kernel
  row_normalized :=
    indexedSumWeight_row_normalized indices indices_nodup Source Target kernel
  column_normalized :=
    indexedSumWeight_column_normalized indices indices_nodup Source Target kernel

end YMGap.Continuum.FiniteBistochasticQKernelIndexedSum

#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSumWeight_nonnegative
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSources_nodup
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedTargets_nodup
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSources_complete
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedTargets_complete
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.listQSum_equiv
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSumWeight_same
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSumWeight_different
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSumWeight_row_normalized
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSumWeight_column_normalized
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSum
