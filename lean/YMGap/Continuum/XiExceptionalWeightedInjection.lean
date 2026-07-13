/-
# Finite weighted injections for exceptional Xi configurations

The corrected disagreement switch is now injective even though its cut is
computed from the source pair.  Turning that pointwise fact into a bound on a
finite partition sum requires a constructive weighted-injection principle.

This file proves that principle directly for `Q'`-weighted lists.  The proof
removes the image of the current source code from the target list, so no
cardinality theorem, quotient, choice, or classical finite-set API is used.
The source list is required to be `Nodup`: without occurrence-distinct codes,
an injective value map cannot account for duplicate source positions.
-/

import YMGap.Continuum.XiExceptionalDistinctInjection

namespace YMGap.Continuum.XiExceptionalWeightedInjection

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive rational list sums -/

def qListSum (weight : α → Q') : List α → Q'
  | [] => 0
  | x :: xs => weight x + qListSum weight xs

@[simp] theorem qListSum_nil (weight : α → Q') :
    qListSum weight [] = 0 := rfl

@[simp] theorem qListSum_cons (weight : α → Q') (x : α)
    (xs : List α) :
    qListSum weight (x :: xs) = weight x + qListSum weight xs := rfl

theorem qListSum_nonnegative (weight : α → Q') :
    ∀ (xs : List α), (∀ x, x ∈ xs → (0 : Q') ≤ weight x) →
      (0 : Q') ≤ qListSum weight xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h => by
      apply Q'.zero_le_add
      · exact h x (List.mem_cons_self)
      · exact qListSum_nonnegative weight xs
          (fun y hy => h y (List.mem_cons_of_mem x hy))

/-! ## 2. Erasing one target code -/

theorem mem_erase_of_mem_of_ne [DecidableEq α] {x y : α}
    (hxy : x ≠ y) :
    ∀ {xs : List α}, x ∈ xs → x ∈ xs.erase y
  | [], hx => by cases hx
  | a :: xs, hx => by
      by_cases hay : a = y
      · subst a
        rw [List.erase_cons_head]
        exact (List.mem_cons.mp hx).resolve_left hxy
      · rw [List.erase_cons_tail (by simpa [hay])]
        rcases List.mem_cons.mp hx with hxa | hxs
        · exact List.mem_cons.mpr (Or.inl hxa)
        · exact List.mem_cons.mpr
            (Or.inr (mem_erase_of_mem_of_ne hxy hxs))

/-- Removing the first occurrence of `y` exposes its weight additively, up
to the rational setoid.  The order in which the prefix weights occur is
irrelevant because addition in `Q'` is commutative up to `eqv`. -/
theorem qListSum_erase_decompose [DecidableEq α]
    (weight : α → Q') :
    ∀ (xs : List α) (y : α), y ∈ xs →
      qListSum weight xs ≈
        weight y + qListSum weight (xs.erase y)
  | [], _, hy => by cases hy
  | x :: xs, y, hy => by
      by_cases hxy : x = y
      · subst x
        rw [List.erase_cons_head]
        exact Q'.eqv_refl _
      · have hyTail : y ∈ xs :=
          (List.mem_cons.mp hy).resolve_left (fun h => hxy h.symm)
        rw [List.erase_cons_tail (a := y) (b := x) (by simp [hxy])]
        have ih := qListSum_erase_decompose weight xs y hyTail
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (weight x) _ _ ih) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_assoc_eqv (weight x) (weight y)
              (qListSum weight (xs.erase y)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            (weight x + weight y) (weight y + weight x)
            (qListSum weight (xs.erase y))
            (Q'.add_comm_eqv (weight x) (weight y))) ?_
        exact Q'.add_assoc_eqv (weight y) (weight x)
          (qListSum weight (xs.erase y))

/-! ## 3. The finite weighted-injection theorem -/

/-- A pointwise weight domination along an injective code map sums to a
global domination by the target list.  This is the precise finite summation
step needed after an exceptional pair has been encoded into a carrier term:
the remaining work is to supply the concrete target code and its term bound.
-/
theorem qListSum_le_of_injective [DecidableEq β]
    (source : List α) (target : List β)
    (sourceWeight : α → Q') (targetWeight : β → Q')
    (encode : α → β)
    (hsource : source.Nodup)
    (hmem : ∀ x, x ∈ source → encode x ∈ target)
    (hinjective : ∀ x, x ∈ source → ∀ y, y ∈ source →
      encode x = encode y → x = y)
    (hterm : ∀ x, x ∈ source →
      sourceWeight x ≤ targetWeight (encode x))
    (htarget : ∀ y, y ∈ target → (0 : Q') ≤ targetWeight y) :
    qListSum sourceWeight source ≤ qListSum targetWeight target := by
  induction source generalizing target with
  | nil =>
      exact qListSum_nonnegative targetWeight target htarget
  | cons x xs ih =>
      have hnd := List.nodup_cons.mp hsource
      have hxmem : x ∈ x :: xs := List.mem_cons_self
      have henc : encode x ∈ target := hmem x hxmem
      have hrest : qListSum sourceWeight xs ≤
          qListSum targetWeight (target.erase (encode x)) := by
        apply ih (target.erase (encode x)) hnd.2
        · intro y hy
          have hySource : y ∈ x :: xs := List.mem_cons_of_mem x hy
          have hne : encode y ≠ encode x := by
            intro heq
            have hyx := hinjective y hySource x hxmem heq
            subst y
            exact hnd.1 hy
          exact mem_erase_of_mem_of_ne hne (hmem y hySource)
        · intro y hy z hz heq
          exact hinjective y (List.mem_cons_of_mem x hy)
            z (List.mem_cons_of_mem x hz) heq
        · intro y hy
          exact hterm y (List.mem_cons_of_mem x hy)
        · intro y hy
          exact htarget y (List.mem_of_mem_erase hy)
      have hadd : sourceWeight x + qListSum sourceWeight xs ≤
          targetWeight (encode x) +
            qListSum targetWeight (target.erase (encode x)) :=
        Q'.add_le_add (hterm x hxmem) hrest
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (Q'.eqv_symm
          (qListSum_erase_decompose targetWeight target (encode x) henc)))

#print axioms qListSum_nonnegative
#print axioms mem_erase_of_mem_of_ne
#print axioms qListSum_erase_decompose
#print axioms qListSum_le_of_injective

end YMGap.Continuum.XiExceptionalWeightedInjection
