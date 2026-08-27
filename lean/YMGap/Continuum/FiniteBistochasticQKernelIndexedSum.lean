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
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSumWeight_row_normalized
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSumWeight_column_normalized
#print axioms YMGap.Continuum.FiniteBistochasticQKernelIndexedSum.indexedSum
