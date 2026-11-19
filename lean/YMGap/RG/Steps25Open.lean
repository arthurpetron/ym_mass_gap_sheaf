/-
# Steps n = 2..5 fineAt OPEN interfaces

Additive.  Bare `Prop` placeholders for the four remaining crossover fine
factors at rate `1/64`.  Same `fineAt` / nome indexing as Step0/Step1:
`fineAt W n f` = `WilsonVacuumSqTwoStepFactor` at `nome_pos (0+n+1)`
(i.e. r3Nome(n+1)) and width `W (0+n+1)`.

With steps 0–1 under their OPEN Dobrushin hypotheses
(`fineAt_step0_all_widths` / `fineAt_step1_all_widths`) plus these four,
`CoarseConstantZero.hcross_unif_of_fine` would close `hcross_unif` at `c = 0`.
This file does NOT prove that join — defs + comments only.

Mathlib-free; no sorry.  Not chart closure / not gap evidence.
-/

import YMGap.RG.Robust3CrossUniform

namespace YMGap.RG.Steps25Open

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RG.Robust3CrossUniform (fineAt)

/-- OPEN: fine two-step factor `1/64` at crossover step n = 2 (nome index 0+2+1). -/
def hfine_step2_OPEN : Prop :=
  ∀ W : Nat → Nat, fineAt W 2 (Q'.mkPos 1 64 (by decide))

/-- OPEN: fine two-step factor `1/64` at crossover step n = 3 (nome index 0+3+1). -/
def hfine_step3_OPEN : Prop :=
  ∀ W : Nat → Nat, fineAt W 3 (Q'.mkPos 1 64 (by decide))

/-- OPEN: fine two-step factor `1/64` at crossover step n = 4 (nome index 0+4+1). -/
def hfine_step4_OPEN : Prop :=
  ∀ W : Nat → Nat, fineAt W 4 (Q'.mkPos 1 64 (by decide))

/-- OPEN: fine two-step factor `1/64` at crossover step n = 5 (nome index 0+5+1). -/
def hfine_step5_OPEN : Prop :=
  ∀ W : Nat → Nat, fineAt W 5 (Q'.mkPos 1 64 (by decide))

end YMGap.RG.Steps25Open
