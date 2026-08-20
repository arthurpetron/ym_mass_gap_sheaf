/-
# Ternary radix lookup for finite scoped factor tables

`allSeqs 3 k` lists ternary words in lexicographic order, while
`scopedTableIndex 3` interprets a word as a base-three numeral.  This module
proves constructively that the two conventions are inverse at lookup time.
It is a reusable computer-science lemma: an externally proposed dense table
can be audited once as `(allSeqs 3 k).map value`, after which arbitrary local
lookups use the theorem rather than repeating the complete finite scan.
-/

import YMGap.Continuum.FiniteScopedFactorTableCertificate

namespace YMGap.Continuum.FiniteScopedFactorTernaryRadixLookup

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteScopedFactorTableCertificate

private theorem getD_append_left
    {Item : Type} (left right : List Item) (index : Nat) (fallback : Item)
    (hindex : index < left.length) :
    (left ++ right).getD index fallback = left.getD index fallback := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hindex]

private theorem getD_append_right
    {Item : Type} (left right : List Item) (index : Nat) (fallback : Item)
    (hindex : left.length ≤ index) :
    (left ++ right).getD index fallback =
      right.getD (index - left.length) fallback := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right hindex]

private theorem getD_three_blocks_zero
    {Item : Type} (first second third : List Item)
    (index : Nat) (fallback : Item)
    (hindex : index < first.length) :
    (first ++ second ++ third).getD index fallback =
      first.getD index fallback := by
  rw [List.append_assoc]
  exact getD_append_left first (second ++ third) index fallback hindex

private theorem getD_three_blocks_one
    {Item : Type} (first second third : List Item)
    (blockSize index : Nat) (fallback : Item)
    (hfirst : first.length = blockSize)
    (hsecond : second.length = blockSize)
    (hindex : index < blockSize) :
    (first ++ second ++ third).getD (blockSize + index) fallback =
      second.getD index fallback := by
  rw [List.append_assoc]
  rw [getD_append_right first (second ++ third) (blockSize + index)
    fallback (by omega)]
  have hsub : blockSize + index - first.length = index := by omega
  rw [hsub]
  exact getD_append_left second third index fallback (by omega)

private theorem getD_three_blocks_two
    {Item : Type} (first second third : List Item)
    (blockSize index : Nat) (fallback : Item)
    (hfirst : first.length = blockSize)
    (hsecond : second.length = blockSize)
    (hindex : index < blockSize) :
    (first ++ second ++ third).getD
        (blockSize + (blockSize + index)) fallback =
      third.getD index fallback := by
  rw [List.append_assoc]
  rw [getD_append_right first (second ++ third)
    (blockSize + (blockSize + index)) fallback (by omega)]
  have hsubFirst :
      blockSize + (blockSize + index) - first.length =
        blockSize + index := by omega
  rw [hsubFirst]
  rw [getD_append_right second third (blockSize + index)
    fallback (by omega)]
  have hsubSecond : blockSize + index - second.length = index := by omega
  rw [hsubSecond]

private theorem allSeqs_three_succ (length : Nat) :
    allSeqs 3 (length + 1) =
      (allSeqs 3 length).map (fun tail => 0 :: tail) ++
      (allSeqs 3 length).map (fun tail => 1 :: tail) ++
      (allSeqs 3 length).map (fun tail => 2 :: tail) := by
  change
    (List.range 3).flatMap
        (fun c => (allSeqs 3 length).map (fun tail => c :: tail)) = _
  have hrange : List.range 3 = [0, 1, 2] := by decide
  rw [hrange]
  simp

/-- Lookup in a mapped ternary Cartesian table returns the value at the
base-three word index. -/
theorem map_allSeqs_three_getD_scopedTableIndex
    {Value : Type} (fallback : Value) :
    ∀ (value : List Nat → Value) (labels : List Nat),
      (∀ label, label ∈ labels → label < 3) →
        ((allSeqs 3 labels.length).map value).getD
            (scopedTableIndex 3 labels) fallback = value labels := by
  intro value labels
  induction labels generalizing value with
  | nil =>
      intro _
      rfl
  | cons head tail induction =>
      intro hbounded
      have hhead : head < 3 := hbounded head List.mem_cons_self
      have htail : ∀ label, label ∈ tail → label < 3 :=
        fun label hlabel =>
          hbounded label (List.mem_cons_of_mem head hlabel)
      have hindex :
          scopedTableIndex 3 tail < 3 ^ tail.length :=
        scopedTableIndex_lt_pow htail
      have hlength : (allSeqs 3 tail.length).length = 3 ^ tail.length :=
        length_allSeqs 3 tail.length
      have hinduction :=
        induction (fun rest => value (head :: rest)) htail
      have hcases : head = 0 ∨ head = 1 ∨ head = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · rw [List.length_cons, allSeqs_three_succ]
        simp only [List.map_append, List.map_map, scopedTableIndex,
          Nat.zero_mul, Nat.zero_add]
        refine Eq.trans
          (getD_three_blocks_zero _ _ _ _ fallback (by
            simpa only [List.length_map, hlength] using hindex)) ?_
        simpa only [Function.comp_apply] using hinduction
      · rw [List.length_cons, allSeqs_three_succ]
        simp only [List.map_append, List.map_map, scopedTableIndex,
          Nat.one_mul]
        refine Eq.trans
          (getD_three_blocks_one _ _ _ (3 ^ tail.length)
            (scopedTableIndex 3 tail) fallback
            (by simp only [List.length_map, hlength])
            (by simp only [List.length_map, hlength]) hindex) ?_
        simpa only [Function.comp_apply] using hinduction
      · rw [List.length_cons, allSeqs_three_succ]
        simp only [List.map_append, List.map_map, scopedTableIndex]
        rw [show 2 * 3 ^ tail.length + scopedTableIndex 3 tail =
            3 ^ tail.length +
              (3 ^ tail.length + scopedTableIndex 3 tail) by omega]
        refine Eq.trans
          (getD_three_blocks_two _ _ _ (3 ^ tail.length)
            (scopedTableIndex 3 tail) fallback
            (by simp only [List.length_map, hlength])
            (by simp only [List.length_map, hlength]) hindex) ?_
        simpa only [Function.comp_apply] using hinduction

/-- Semantic form for a scoped table: bounded scope labels select exactly
their mapped table entry. -/
theorem scopedTableValue_map_allSeqs_three
    {Value : Type} (scope : List Nat) (labelling : Nat → Nat)
    (value : List Nat → Value) (fallback : Value)
    (hbounded : ∀ id, id ∈ scope → labelling id < 3) :
    ((allSeqs 3 scope.length).map value).getD
        (scopedTableIndex 3 (scope.map labelling)) fallback =
      value (scope.map labelling) := by
  simpa only [List.length_map] using
    (map_allSeqs_three_getD_scopedTableIndex fallback value
      (scope.map labelling) (by
        intro label hlabel
        rcases List.mem_map.mp hlabel with ⟨id, hid, rfl⟩
        exact hbounded id hid))

end YMGap.Continuum.FiniteScopedFactorTernaryRadixLookup

#print axioms
  YMGap.Continuum.FiniteScopedFactorTernaryRadixLookup.map_allSeqs_three_getD_scopedTableIndex
#print axioms
  YMGap.Continuum.FiniteScopedFactorTernaryRadixLookup.scopedTableValue_map_allSeqs_three
