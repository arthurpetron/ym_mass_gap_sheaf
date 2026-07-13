/-
# Finite fiberwise weighted domination

Pointwise exceptional-code domination is stronger than necessary.  This file
proves the exact constructive replacement: a possibly noninjective encoder
is sufficient when the complete source fiber over each target code has weight
at most that target's weight.  The proof partitions the source list by the
head target code and recurses over a `Nodup` target enumeration.
-/

import YMGap.Continuum.XiExceptionalBranchPackingFence

namespace YMGap.Continuum.XiExceptionalFiberwiseInjection

open YMGap.Constructive
open YMGap.Continuum.XiExceptionalWeightedInjection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Nonnegative filtered sums -/

theorem qListSum_filter_partition (weight : α → Q') (p : α → Bool) :
    ∀ xs : List α,
      qListSum weight xs ≈
        qListSum weight (xs.filter p) +
          qListSum weight (xs.filter (fun x => !(p x)))
  | [] => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | x :: xs => by
      have ih := qListSum_filter_partition weight p xs
      cases hp : p x with
      | false =>
          simp only [qListSum_cons, List.filter_cons, hp,
            Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (weight x) _ _ ih) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.add_comm_eqv (weight x)
                (qListSum weight (xs.filter p)))) ?_
          exact Q'.add_assoc_eqv _ _ _
      | true =>
          simp only [qListSum_cons, List.filter_cons, hp, ↓reduceIte,
            Bool.not_true, Bool.false_eq_true]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (weight x) _ _ ih) ?_
          exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

theorem qListSum_filter_mono (weight : α → Q')
    (p q : α → Bool) :
    ∀ xs : List α,
      (∀ x, x ∈ xs → (0 : Q') ≤ weight x) →
      (∀ x, x ∈ xs → p x = true → q x = true) →
      qListSum weight (xs.filter p) ≤ qListSum weight (xs.filter q)
  | [], _, _ => Q'.le_refl' 0
  | x :: xs, hnonneg, himp => by
      have htailNonneg : ∀ z, z ∈ xs → (0 : Q') ≤ weight z :=
        fun z hz => hnonneg z (List.mem_cons_of_mem x hz)
      have htailImp : ∀ z, z ∈ xs → p z = true → q z = true :=
        fun z hz => himp z (List.mem_cons_of_mem x hz)
      have ih := qListSum_filter_mono weight p q xs htailNonneg htailImp
      cases hp : p x with
      | false =>
          cases hq : q x with
          | false =>
              simpa [List.filter_cons, hp, hq] using ih
          | true =>
              simp only [List.filter_cons, hp, hq, Bool.false_eq_true,
                ↓reduceIte, qListSum_cons]
              have hplus : qListSum weight (xs.filter q) ≤
                  qListSum weight (xs.filter q) + weight x :=
                Q'.add_le_self_of_nonneg _ _
                  (hnonneg x List.mem_cons_self)
              exact Q'.le_trans' _ _ _ ih
                (Q'.le_trans' _ _ _ hplus
                  (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
      | true =>
          have hq : q x = true := himp x List.mem_cons_self hp
          simp only [List.filter_cons, hp, hq, ↓reduceIte, qListSum_cons]
          exact Q'.add_le_add (Q'.le_refl' _) ih

/-! ## 2. The fiberwise finite summation theorem -/

theorem qListSum_le_of_fibers [DecidableEq β]
    (source : List α) (target : List β)
    (sourceWeight : α → Q') (targetWeight : β → Q')
    (encode : α → β)
    (htarget : target.Nodup)
    (hmem : ∀ x, x ∈ source → encode x ∈ target)
    (hsourceNonneg : ∀ x, x ∈ source → (0 : Q') ≤ sourceWeight x)
    (hfiber : ∀ y, y ∈ target →
      qListSum sourceWeight
          (source.filter (fun x => decide (encode x = y))) ≤
        targetWeight y) :
    qListSum sourceWeight source ≤ qListSum targetWeight target := by
  induction target generalizing source with
  | nil =>
      cases source with
      | nil => exact Q'.le_refl' 0
      | cons x xs =>
          have hx := hmem x List.mem_cons_self
          cases hx
  | cons y ys ih =>
      have hnd := List.nodup_cons.mp htarget
      let same := source.filter (fun x => decide (encode x = y))
      let rest := source.filter (fun x => !(decide (encode x = y)))
      have hpart : qListSum sourceWeight source ≈
          qListSum sourceWeight same + qListSum sourceWeight rest :=
        qListSum_filter_partition sourceWeight
          (fun x => decide (encode x = y)) source
      have hsame : qListSum sourceWeight same ≤ targetWeight y :=
        hfiber y List.mem_cons_self
      have hrestMem : ∀ x, x ∈ rest → encode x ∈ ys := by
        intro x hx
        have hp := List.mem_filter.mp hx
        have himage := hmem x hp.1
        rcases List.mem_cons.mp himage with hxy | hys
        · have heq : decide (encode x = y) = true :=
            decide_eq_true hxy
          rw [heq] at hp
          exact absurd hp.2 (by decide)
        · exact hys
      have hrestNonneg : ∀ x, x ∈ rest → (0 : Q') ≤ sourceWeight x := by
        intro x hx
        exact hsourceNonneg x (List.mem_filter.mp hx).1
      have hrestFiber : ∀ z, z ∈ ys →
          qListSum sourceWeight
              (rest.filter (fun x => decide (encode x = z))) ≤
            targetWeight z := by
        intro z hz
        have hsub : qListSum sourceWeight
              (rest.filter (fun x => decide (encode x = z))) ≤
            qListSum sourceWeight
              (source.filter (fun x => decide (encode x = z))) := by
          unfold rest
          rw [List.filter_filter]
          apply qListSum_filter_mono sourceWeight
            (fun x => decide (encode x = z) &&
              !(decide (encode x = y)))
            (fun x => decide (encode x = z)) source hsourceNonneg
          intro x _ hx
          exact (Bool.and_eq_true _ _).mp hx |>.1
        exact Q'.le_trans' _ _ _ hsub
          (hfiber z (List.mem_cons_of_mem y hz))
      have hrest : qListSum sourceWeight rest ≤
          qListSum targetWeight ys :=
        ih rest hnd.2 hrestMem hrestNonneg hrestFiber
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpart)
        (Q'.add_le_add hsame hrest)

#print axioms qListSum_filter_partition
#print axioms qListSum_filter_mono
#print axioms qListSum_le_of_fibers

end YMGap.Continuum.XiExceptionalFiberwiseInjection
