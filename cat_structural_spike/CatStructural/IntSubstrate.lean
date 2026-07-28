/-
CatStructural/IntSubstrate.lean

The `Int` instantiation of `GapSubstrate` — the trivial-setoid instance
(`eqv := Eq`), recovering the concrete `DominatedGrowth.lean` layer as
a special case of the generic one and providing the first of the two
instances that justify the abstraction.

The cancellation laws are the only nontrivial content; `pos_cancel`
re-derives the `pos_of_mul_le` argument.  A kernel-`decide`d demo at
the end re-runs the toy three-scale anchor through the GENERIC chain,
confirming the generic and concrete layers compute identically.

Mathlib-free, Classical-free, sorry-free.
-/

import CatStructural.Substrate
import CatStructural.DomOver
import CatStructural.DominatedGrowth

namespace CatStructural

/-- `Int` as a `GapSubstrate` with `eqv := Eq`.  All laws are Lean-core
    `Int` lemmas; `pos_cancel` reuses the spike's `pos_of_mul_le`.
    Reducible so that literal and `Decidable` synthesis see `Int`
    through the record fields. -/
@[reducible] def intSubstrate : GapSubstrate where
  Carrier := Int
  eqv := Eq
  le := (· ≤ ·)
  lt := (· < ·)
  zero := 0
  one := 1
  mul := (· * ·)
  eqv_refl _ := rfl
  eqv_symm h := h.symm
  eqv_trans h₁ h₂ := h₁.trans h₂
  le_of_eqv h := Int.le_of_eq h
  le_trans h₁ h₂ := Int.le_trans h₁ h₂
  le_of_lt h := Int.le_of_lt h
  lt_of_lt_of_le h₁ h₂ := Int.lt_of_lt_of_le h₁ h₂
  mul_congr h₁ h₂ := by rw [h₁, h₂]
  mul_assoc_eqv a b c := Int.mul_assoc a b c
  mul_comm_eqv a b := Int.mul_comm a b
  one_mul_eqv a := Int.one_mul a
  zero_lt_one := by decide
  mul_nonneg h₁ h₂ := Int.mul_nonneg h₁ h₂
  mul_pos h₁ h₂ := Int.mul_pos h₁ h₂
  mul_le_mul_left h hc := Int.mul_le_mul_of_nonneg_left h hc
  mul_right_cancel_eqv hc h :=
    Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hc) h
  le_of_mul_le_mul_left h hc := Int.le_of_mul_le_mul_left h hc
  pos_cancel hd hn h := pos_of_mul_le hd hn h

/-- The generic layer at `Int` reproduces the concrete toy anchor:
    same three-scale ledger, same composite ratio 405/600, checked by
    kernel `decide` through `chainG`. -/
def toyMG : Nat → MassG intSubstrate
  | 0 => ⟨120, by decide⟩ | 1 => ⟨100, by decide⟩
  | 2 => ⟨90, by decide⟩ | _ => ⟨81, by decide⟩

def toyStepG : ∀ k, DomG (toyMG k) (toyMG (k + 1))
  | 0 => ⟨5, 6, by decide, by decide, by decide⟩
  | 1 => ⟨9, 10, by decide, by decide, by decide⟩
  | 2 => ⟨9, 10, by decide, by decide, by decide⟩
  | _ + 3 => ⟨1, 1, by decide, by decide, Int.le_refl _⟩

/-- Generic-at-`Int` composite matches the concrete spike's numbers. -/
theorem toyG_composite_ratio :
    (chainG toyMG toyStepG 3).num = 405 ∧
    (chainG toyMG toyStepG 3).den = 600 := by
  constructor <;> decide

#print axioms intSubstrate
#print axioms toyG_composite_ratio

end CatStructural
