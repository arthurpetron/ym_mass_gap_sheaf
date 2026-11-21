/-
# Steps n = 2..5 fineAt OPEN interfaces, instance B (step-2 fine nome `279/500`)

Additive copy of `Steps25Open` over `fineAtB` (`Robust3CrossUniformW558`).  Bare `Prop`
placeholders at rate `1/64`; indexing unchanged: `fineAtB W n f` is the two-step factor at nome
index `0+n+1` and width `W (0+n+1)`.  Only step 2 (nome index 3, now `279/500`) differs from the
original; `hfine_stepkB_OPEN_iff` (k = 3, 4, 5) proves the other three are literally the
original OPEN interfaces (via `fineAtB_iff`).

Mathlib-free; no sorry.  Not chart closure / not gap evidence.
-/

import YMGap.RG.Robust3CrossUniformW558
import YMGap.RG.Steps25Open

namespace YMGap.RG.Steps25OpenW558

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RG.Robust3CrossUniformW558 (fineAtB fineAtB_iff)
open YMGap.RG.Steps25Open (hfine_step3_OPEN hfine_step4_OPEN hfine_step5_OPEN)

/-- OPEN: instance-B fine two-step factor `1/64` at crossover step n = 2 (nome `279/500`). -/
def hfine_step2B_OPEN : Prop :=
  ∀ W : Nat → Nat, fineAtB W 2 (Q'.mkPos 1 64 (by decide))

/-- OPEN: instance-B fine factor `1/64` at step n = 3 (same nome as the original). -/
def hfine_step3B_OPEN : Prop :=
  ∀ W : Nat → Nat, fineAtB W 3 (Q'.mkPos 1 64 (by decide))

/-- OPEN: instance-B fine factor `1/64` at step n = 4 (same nome as the original). -/
def hfine_step4B_OPEN : Prop :=
  ∀ W : Nat → Nat, fineAtB W 4 (Q'.mkPos 1 64 (by decide))

/-- OPEN: instance-B fine factor `1/64` at step n = 5 (same nome as the original). -/
def hfine_step5B_OPEN : Prop :=
  ∀ W : Nat → Nat, fineAtB W 5 (Q'.mkPos 1 64 (by decide))

theorem hfine_step3B_OPEN_iff : hfine_step3B_OPEN ↔ hfine_step3_OPEN :=
  ⟨fun h W => (fineAtB_iff W 3 _ (by decide)).mp (h W),
   fun h W => (fineAtB_iff W 3 _ (by decide)).mpr (h W)⟩

theorem hfine_step4B_OPEN_iff : hfine_step4B_OPEN ↔ hfine_step4_OPEN :=
  ⟨fun h W => (fineAtB_iff W 4 _ (by decide)).mp (h W),
   fun h W => (fineAtB_iff W 4 _ (by decide)).mpr (h W)⟩

theorem hfine_step5B_OPEN_iff : hfine_step5B_OPEN ↔ hfine_step5_OPEN :=
  ⟨fun h W => (fineAtB_iff W 5 _ (by decide)).mp (h W),
   fun h W => (fineAtB_iff W 5 _ (by decide)).mpr (h W)⟩

end YMGap.RG.Steps25OpenW558

#print axioms YMGap.RG.Steps25OpenW558.hfine_step3B_OPEN_iff
#print axioms YMGap.RG.Steps25OpenW558.hfine_step4B_OPEN_iff
#print axioms YMGap.RG.Steps25OpenW558.hfine_step5B_OPEN_iff
