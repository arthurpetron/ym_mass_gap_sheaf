/-
# Finite timed words in the ORIGINAL Wilson generators

Each atom retains its source loop and spin. A word multiplies the corresponding
scalar characters; it never reorders links within a nonabelian holonomy.
The explicit time bound is exactly the original window support condition.
This finite syntax is used by the chronological operator realization.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.BF4WilsonTimedWord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow

structure TimedLoop (base : Nat) where
  offset : Nat
  loop : SourceLoop base
  spin : Nat

def wordExpression {base : Nat} : List (TimedLoop base) → WindowExpression base
  | [] => .one
  | a :: rest => .mul (.loop a.offset a.loop a.spin) (wordExpression rest)

def WordWithin {base : Nat} (H : Nat) (word : List (TimedLoop base)) : Prop :=
  ∀ a, a ∈ word → a.offset ≤ H

theorem wordWithin_nil {base : Nat} (H : Nat) : WordWithin H ([] : List (TimedLoop base)) := by
  intro a ha
  cases ha

theorem wordWithin_cons {base : Nat} (H : Nat) (a : TimedLoop base)
    (rest : List (TimedLoop base)) :
    WordWithin H (a :: rest) ↔ a.offset ≤ H ∧ WordWithin H rest := by
  constructor
  · intro h
    exact ⟨h a (List.mem_cons_self), fun b hb => h b (List.mem_cons_of_mem a hb)⟩
  · rintro ⟨ha, hr⟩ b hb
    rcases List.mem_cons.mp hb with h | h
    · subst b
      exact ha
    · exact hr b h

theorem wordExpression_within {base : Nat} (H : Nat) (word : List (TimedLoop base)) :
    Within H (wordExpression word) ↔ WordWithin H word := by
  induction word with
  | nil => exact ⟨fun _ => wordWithin_nil H, fun _ => True.intro⟩
  | cons a rest ih =>
      change (a.offset ≤ H ∧ Within H (wordExpression rest)) ↔ _
      rw [ih, wordWithin_cons]

def Descending {base : Nat} : List (TimedLoop base) → Prop
  | [] => True
  | a :: rest => WordWithin a.offset rest ∧ Descending rest

#print axioms TimedLoop
#print axioms wordExpression
#print axioms WordWithin
#print axioms wordWithin_nil
#print axioms wordWithin_cons
#print axioms wordExpression_within
#print axioms Descending

end YMGap.Continuum.BF4WilsonTimedWord
