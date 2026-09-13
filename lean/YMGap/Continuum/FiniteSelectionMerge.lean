/-
# Canonical ambient-order merging of finite selections

A selection of a duplicate-free ambient list is determined by its support.
The merge is a computed ambient filter, not a concatenation or a chosen
permutation. These facts supply literal inverses for rooted-family coding.
-/

import YMGap.Continuum.FiniteSelectionOrder

namespace YMGap.Continuum.FiniteSelectionMerge

set_option autoImplicit false

open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder

theorem sublist_filter_pin {A : Type} [DecidableEq A] {xs ys : List A}
    (h : ys.Sublist xs) : xs.Nodup → xs.filter (fun a => decide (a ∈ ys)) = ys := by
  induction h with
  | slnil => intro _; rfl
  | @cons ys xs a h ih =>
      intro hn
      have ha : a ∉ ys := fun ha => (List.nodup_cons.mp hn).1 (h.subset ha)
      simpa only [List.filter_cons, decide_eq_false ha] using ih (List.nodup_cons.mp hn).2
  | @cons₂ ys xs a _ ih =>
      intro hn
      have hf : xs.filter (fun x => decide (x ∈ a::ys)) = xs.filter (fun x => decide (x ∈ ys)) := by
        apply List.filter_congr
        intro x hx
        have hxa : x ≠ a := fun he => (List.nodup_cons.mp hn).1 (he ▸ hx)
        simp only [List.mem_cons, hxa, false_or]
      simp only [List.filter_cons, decide_eq_true (List.mem_cons_self : a ∈ a::ys), hf]
      exact congrArg (List.cons a) (ih (List.nodup_cons.mp hn).2)

theorem selected_eq_of_mem_iff {A : Type} [DecidableEq A] {ambient xs ys : List A}
    (hn : ambient.Nodup) (hx : xs ∈ selections ambient) (hy : ys ∈ selections ambient)
    (hmem : ∀ a, a ∈ xs ↔ a ∈ ys) : xs = ys := by
  rw [← sublist_filter_pin (selected_sublist hx) hn, ← sublist_filter_pin (selected_sublist hy) hn]
  apply List.filter_congr
  intro a _
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using hmem a

def merge {A : Type} [DecidableEq A] (ambient left right : List A) : List A :=
  ambient.filter (fun a => decide (a ∈ left ∨ a ∈ right))

theorem merge_selected {A : Type} [DecidableEq A] (ambient left right : List A) :
    merge ambient left right ∈ selections ambient := filter_selected _ _

theorem merge_mem_iff {A : Type} [DecidableEq A] {ambient left right : List A} {a : A} :
    a ∈ merge ambient left right ↔ a ∈ ambient ∧ (a ∈ left ∨ a ∈ right) := by
  simp only [merge, List.mem_filter, decide_eq_true_eq]

theorem merge_recovers {A : Type} [DecidableEq A] {ambient ids left right : List A}
    (hn : ambient.Nodup) (hi : ids ∈ selections ambient)
    (hsplit : ∀ a, a ∈ ids ↔ a ∈ left ∨ a ∈ right) : merge ambient left right = ids := by
  apply selected_eq_of_mem_iff hn (merge_selected _ _ _) hi
  intro a
  constructor
  · intro ha
    exact (hsplit a).mpr (merge_mem_iff.mp ha).2
  · intro ha
    exact merge_mem_iff.mpr ⟨selected_mem hi a ha, (hsplit a).mp ha⟩

end YMGap.Continuum.FiniteSelectionMerge

#print axioms YMGap.Continuum.FiniteSelectionMerge.sublist_filter_pin
#print axioms YMGap.Continuum.FiniteSelectionMerge.selected_eq_of_mem_iff
#print axioms YMGap.Continuum.FiniteSelectionMerge.merge
#print axioms YMGap.Continuum.FiniteSelectionMerge.merge_selected
#print axioms YMGap.Continuum.FiniteSelectionMerge.merge_mem_iff
#print axioms YMGap.Continuum.FiniteSelectionMerge.merge_recovers
