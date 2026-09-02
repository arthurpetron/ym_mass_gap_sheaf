/-
# Constructive positive maximum entry of a finite rational list

A nonnegative finite rational family with strictly positive total has a
constructively selected positive maximum-weight occurrence.  The carrier may
contain duplicate values; selection is by literal list occurrence.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.FiniteBistochasticPositiveTarget

namespace YMGap.Continuum.FinitePositiveMaximumEntry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticPositiveTarget
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

private theorem q_le_of_not_le {left right : Q'}
    (hnot : ¬ left ≤ right) :
    right ≤ left := by
  show
    right.num * (left.den : Int) ≤
      left.num * (right.den : Int)
  have hcross :
      ¬ left.num * (right.den : Int) ≤
        right.num * (left.den : Int) :=
    hnot
  exact Int.le_of_lt (Int.not_le.mp hcross)

/-- A listed occurrence whose rational value dominates every listed
occurrence. -/
structure FiniteMaximumEntry {A : Type}
    (value : A → Q') (items : List A) : Type where
  item : A
  item_mem : item ∈ items
  maximal : ∀ other, other ∈ items → value other ≤ value item

/-- A constructive maximum of a nonempty finite rational family.  Ties retain
the later recursively selected occurrence. -/
def finiteMaximumEntry {A : Type} (value : A → Q') :
    (head : A) → (tail : List A) →
      FiniteMaximumEntry value (head :: tail)
  | head, [] =>
      { item := head
        item_mem := List.mem_cons_self
        maximal := by
          intro other hother
          have heq : other = head := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using hother
          rw [heq]
          exact Q'.le_refl' _ }
  | head, next :: tail =>
      let rest := finiteMaximumEntry value next tail
      if hhead : value head ≤ value rest.item then
        { item := rest.item
          item_mem := List.mem_cons_of_mem head rest.item_mem
          maximal := by
            intro other hother
            rcases List.mem_cons.mp hother with heq | hrest
            · rw [heq]
              exact hhead
            · exact rest.maximal other hrest }
      else
        { item := head
          item_mem := List.mem_cons_self
          maximal := by
            intro other hother
            rcases List.mem_cons.mp hother with heq | hrest
            · rw [heq]
              exact Q'.le_refl' _
            · exact Q'.le_trans' _ _ _
                (rest.maximal other hrest)
                (q_le_of_not_le hhead) }

/-- A maximum occurrence whose value is strictly positive. -/
structure FinitePositiveMaximumEntry {A : Type}
    (value : A → Q') (items : List A) extends
      FiniteMaximumEntry value items where
  value_pos : (0 : Q') < value item

/-- Nonnegative entries with positive finite sum admit a constructive
positive maximum occurrence. -/
opaque finitePositiveMaximumEntryOfSumPos
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item)
    (items : List A)
    (htotal : (0 : Q') < listQSum value items) :
    FinitePositiveMaximumEntry value items := by
  let positive := finitePositiveEntryOfSumPos
    value hvalue items htotal
  cases hitems : items with
  | nil =>
      have himpossible : positive.item ∈ ([] : List A) := by
        simpa only [hitems] using positive.item_mem
      exact False.elim (List.not_mem_nil himpossible)
  | cons head tail =>
      let maximum := finiteMaximumEntry value head tail
      have hpositiveMem : positive.item ∈ head :: tail := by
        simpa only [hitems] using positive.item_mem
      exact
        { item := maximum.item
          item_mem := by
            simpa only [hitems] using maximum.item_mem
          maximal := by
            intro other hother
            apply maximum.maximal other
            simpa only [hitems] using hother
          value_pos :=
            Q'.pos_of_lt_of_le positive.value_pos
              (maximum.maximal positive.item hpositiveMem) }

end YMGap.Continuum.FinitePositiveMaximumEntry

#print axioms
  YMGap.Continuum.FinitePositiveMaximumEntry.finiteMaximumEntry
#print axioms
  YMGap.Continuum.FinitePositiveMaximumEntry.finitePositiveMaximumEntryOfSumPos
