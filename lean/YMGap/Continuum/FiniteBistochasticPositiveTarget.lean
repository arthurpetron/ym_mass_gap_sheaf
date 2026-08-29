/-
# A constructive positive target in every finite bistochastic row

A nonnegative finite row whose exact sum is one contains a strictly positive
entry.  This module makes that elementary fact computational: structural
recursion scans the written target list and returns the first positive entry,
together with its membership and positivity witnesses.  Specializing to a
finite bistochastic rational kernel gives a data-bearing positive target for
every source row.

Unlike the existing first-target selector, this compiler uses row
normalization and guarantees strict positivity.  It is independent of the
origin of the kernel and introduces no Yang--Mills hypothesis.

Constructive contract: decidable rational order, finite-list recursion, and
exact row normalization only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticQKernel

namespace YMGap.Continuum.FiniteBistochasticPositiveTarget

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The finite positive-entry compiler -/

/-- A literal member of a finite list at which a rational value is strictly
positive. -/
structure FinitePositiveEntry
    {A : Type} (value : A → Q') (items : List A) : Type where
  item : A
  item_mem : item ∈ items
  value_pos : (0 : Q') < value item

private theorem q_nonpositive_of_not_positive {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

/-- Structural search for a positive member of a nonnegative finite sum.
The strict positivity of the whole sum rules out the empty branch. -/
def finitePositiveEntryOfSumPos
    {A : Type} (value : A → Q')
    (hnonnegative : ∀ item, (0 : Q') ≤ value item) :
    (items : List A) → (0 : Q') < listQSum value items →
      FinitePositiveEntry value items
  | [], hsum => False.elim
      ((Int.not_lt_of_ge (Q'.le_refl' 0)) hsum)
  | head :: tail, hsum => by
      by_cases hhead : (0 : Q') < value head
      · exact
          { item := head
            item_mem := List.mem_cons_self
            value_pos := hhead }
      · have hheadZero : value head ≈ 0 :=
          Q'.eqv_of_le_le
            (q_nonpositive_of_not_positive hhead)
            (hnonnegative head)
        have hsumEqTail :
            listQSum value (head :: tail) ≈ listQSum value tail := by
          refine Q'.eqv_trans _ (0 + listQSum value tail) _ ?_ ?_
          · exact Q'.add_eqv_congr' hheadZero (Q'.eqv_refl _)
          · exact Q'.eqv_of_eq (Q'.zero_add' (listQSum value tail))
        have htailPos : (0 : Q') < listQSum value tail :=
          Q'.pos_of_lt_of_le hsum (Q'.le_of_eqv hsumEqTail)
        let selected := finitePositiveEntryOfSumPos
          value hnonnegative tail htailPos
        exact
          { item := selected.item
            item_mem := List.mem_cons_of_mem head selected.item_mem
            value_pos := selected.value_pos }

/-! ## 2. Specialization to an arbitrary bistochastic row -/

/-- A written target of one source row carrying strictly positive kernel
weight. -/
structure FiniteBistochasticPositiveTarget
    {Source Target : Type}
    (kernel : FiniteBistochasticQKernel Source Target)
    (source : Source) : Type where
  target : Target
  target_mem : target ∈ kernel.targets
  weight_pos : (0 : Q') < kernel.weight source target

/-- Every source row of a finite nonnegative exactly normalized rational
kernel constructively returns a positive target. -/
def FiniteBistochasticQKernel.positiveTarget
    {Source Target : Type}
    (kernel : FiniteBistochasticQKernel Source Target)
    (source : Source) : FiniteBistochasticPositiveTarget kernel source := by
  have hsumPos :
      (0 : Q') < listQSum (kernel.weight source) kernel.targets := by
    have hone : (0 : Q') < (1 : Q') := by decide
    exact Q'.pos_of_lt_of_le hone
      (Q'.le_of_eqv (Q'.eqv_symm (kernel.row_normalized source)))
  let selected := finitePositiveEntryOfSumPos
    (kernel.weight source)
    (kernel.weight_nonnegative source)
    kernel.targets hsumPos
  exact
    { target := selected.item
      target_mem := selected.item_mem
      weight_pos := selected.value_pos }

/-- Unqualified public spelling of the positive-row compiler, convenient in
modules which already use the kernel structure namespace. -/
abbrev finiteBistochasticPositiveTarget
    {Source Target : Type}
    (kernel : FiniteBistochasticQKernel Source Target)
    (source : Source) : FiniteBistochasticPositiveTarget kernel source :=
  FiniteBistochasticQKernel.positiveTarget kernel source

#print axioms FinitePositiveEntry
#print axioms finitePositiveEntryOfSumPos
#print axioms FiniteBistochasticPositiveTarget
#print axioms FiniteBistochasticQKernel.positiveTarget
#print axioms finiteBistochasticPositiveTarget

end YMGap.Continuum.FiniteBistochasticPositiveTarget
