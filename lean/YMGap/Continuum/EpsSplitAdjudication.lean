/-
`EpsSplitAdjudication` — Milestone 13.3: the ε-SPLIT ADJUDICATION (the one
remaining named candidate for a legal strictly-weaker decomposition of the
atomic Clay core `singleStep`) — VERDICT: EQUI-INHABITS (C++), machine-checked.

# The candidate split (the Balaban small-field/large-field architecture)

Split the per-step margin degradation into a PERTURBATIVE part (the model
bound holds up to a non-perturbative loss `L k`) and a LARGE-FIELD part
(the loss is absorbed by the slack between a fine model `afrF` and a coarse
model `afrC`):

  * `PertStepProp afrF tm L`  :  ∀ k, (1 − δF k)·tm k ≤ tm (k+1) + L k
  * `AbsorbProp afrF afrC tm L` : ∀ k, (1 − δC k)·tm k + L k ≤ (1 − δF k)·tm k

# The machine-checked adjudication (ledger rule (b) applied)

  * **PRODUCER (`singleStepProp_of_split`, PROVED):**
    `PertStep ∧ Absorb → SingleStepProp afrC tm` — the split composes back
    to the core at the coarse rate (`le_add_cancel_right`, the `Q'`
    order-cancellation proved here via negation).
  * **CONVERSE (`split_of_singleStepProp`, PROVED):** `SingleStepProp afr tm`
    yields the split with ZERO loss at `afrC := afrF := afr` — so the PAIR
    equi-inhabits `singleStep`.
  * **VACUITY OF CONJUNCT (i) (`pertStep_vacuous`, PROVED):**
    `PertStepProp` ALONE is satisfiable for EVERY `afr, tm` (nonneg margins)
    by the loss that swallows everything (`L k := (1 − δF k)·tm k`) — the
    perturbative conjunct carries NO `singleStep` content by itself.
  * **LOAD TRANSFER (`absorb_forces_nonpos`, PROVED):** against that vacuous
    loss, `AbsorbProp` FORCES `(1 − δC k)·tm k ≤ 0` — i.e. it is REFUTED on
    every positive-margin instance.  The entire `singleStep` load provably
    concentrates in conjunct (ii).

# VERDICT (recorded per the anti-loop rule — do NOT campaign on this split)

As bare types the ε-split is a RE-FRAMING of `singleStep`: the pair
equi-inhabits the core, conjunct (i) alone is vacuous, and conjunct (ii)
with pinned loss carries the full load — exactly the collapse pattern of
the per-move (`SITE1PerMoveDefect`) and resummation
(`ResummationAdjudication`) adjudications.  **The last named candidate
F-split is dead; `F = 1` (atomic `singleStep`) is STRENGTHENED.**  The
surviving genuine content of the small/large-field architecture is a
CONSTRUCTION task, not a decomposition: pin `L k` to a constructed
finite-volume large-field functional with chessboard/RP bounds and prove
`AbsorbProp` for it — that is front (a) (direct construction; the
Koch–Wittwer certified route of item 12 / Milestone 13.4), where the
campaign continues.  The Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.SingleStepDecompositionAdjudication

namespace YMGap.Continuum.EpsSplitAdjudication

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDecompositionAdjudication

/-! ## 0. `Q'` order-cancellation (via negation — no new Int plumbing) -/

/-- `a + c ≤ b + c → a ≤ b` (add `−c`, collapse with `add_neg_self`). -/
theorem le_add_cancel_right {a b c : Q'} (h : a + c ≤ b + c) : a ≤ b := by
  have hcol : ∀ x : Q', ((x + c) + (-c)).eqv x := fun x =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv x c (-c))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left x (c + -c) 0 (Q'.add_neg_self_eqv c))
        (Q'.eqv_of_eq (Q'.add_zero' x)))
  have h3 : (a + c) + (-c) ≤ (b + c) + (-c) :=
    Q'.add_le_add_right _ _ _ h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hcol a))
    (Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv (hcol b)))

/-! ## 1. The two conjuncts of the candidate split -/

/-- **(i) The PERTURBATIVE conjunct:** the fine model bounds the per-step
degradation UP TO a non-perturbative loss `L k`. -/
def PertStepProp (afrF : AFRateCalibration.AFRateModulus) (tm L : Nat → Q') : Prop :=
  ∀ k : Nat, (1 - afDefectSeq afrF k) * tm k ≤ tm (k + 1) + L k

/-- **(ii) The LARGE-FIELD conjunct:** the loss is absorbed by the slack
between the coarse model `afrC` and the fine model `afrF`. -/
def AbsorbProp (afrF afrC : AFRateCalibration.AFRateModulus) (tm L : Nat → Q') : Prop :=
  ∀ k : Nat, (1 - afDefectSeq afrC k) * tm k + L k
    ≤ (1 - afDefectSeq afrF k) * tm k

/-! ## 2. PRODUCER: the split composes back to the core -/

/-- **`singleStepProp_of_split` (PROVED).**  `(i) ∧ (ii) → singleStep` at
the coarse rate. -/
theorem singleStepProp_of_split {afrF afrC : AFRateCalibration.AFRateModulus}
    {tm L : Nat → Q'}
    (hP : PertStepProp afrF tm L) (hA : AbsorbProp afrF afrC tm L) :
    SingleStepProp afrC tm := by
  intro k
  refine le_add_cancel_right (c := L k) ?_
  exact Q'.le_trans' _ _ _ (hA k) (hP k)

/-! ## 3. CONVERSE: the core yields the split with zero loss -/

/-- **`split_of_singleStepProp` (PROVED).**  `singleStep` inhabits BOTH
conjuncts at zero loss and equal rates — the PAIR equi-inhabits the core. -/
theorem split_of_singleStepProp {afr : AFRateCalibration.AFRateModulus} {tm : Nat → Q'}
    (h : SingleStepProp afr tm) :
    PertStepProp afr tm (fun _ => 0) ∧ AbsorbProp afr afr tm (fun _ => 0) := by
  constructor
  · intro k
    rw [Q'.add_zero']
    exact h k
  · intro k
    rw [Q'.add_zero']
    exact Q'.le_refl' _

/-! ## 4. VACUITY of conjunct (i) and the LOAD TRANSFER to conjunct (ii) -/

/-- **`pertStep_vacuous` (PROVED — conjunct (i) alone carries NO content).**
For EVERY rate and every nonneg-margin sequence, the loss that swallows the
whole step (`L k := (1 − δF k)·tm k`) satisfies `PertStepProp`. -/
theorem pertStep_vacuous (afrF : AFRateCalibration.AFRateModulus) (tm : Nat → Q')
    (htm : ∀ k, (0 : Q') ≤ tm (k + 1)) :
    PertStepProp afrF tm (fun k => (1 - afDefectSeq afrF k) * tm k) := by
  intro k
  have h := Q'.add_le_add_right _ _ ((1 - afDefectSeq afrF k) * tm k) (htm k)
  rwa [Q'.zero_add'] at h

/-- **`absorb_forces_nonpos` (PROVED — the load transfer).**  Against the
vacuous loss, conjunct (ii) FORCES the coarse step to be nonpositive:
`(1 − δC k)·tm k ≤ 0` — refuted on every positive-margin instance.  The
entire `singleStep` load lives in (ii). -/
theorem absorb_forces_nonpos {afrF afrC : AFRateCalibration.AFRateModulus} {tm : Nat → Q'}
    (hA : AbsorbProp afrF afrC tm
      (fun k => (1 - afDefectSeq afrF k) * tm k)) :
    ∀ k, (1 - afDefectSeq afrC k) * tm k ≤ 0 := by
  intro k
  refine le_add_cancel_right (c := (1 - afDefectSeq afrF k) * tm k) ?_
  have h := hA k
  rwa [← Q'.zero_add' ((1 - afDefectSeq afrF k) * tm k)] at h

end YMGap.Continuum.EpsSplitAdjudication

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.EpsSplitAdjudication.le_add_cancel_right
#print axioms YMGap.Continuum.EpsSplitAdjudication.singleStepProp_of_split
#print axioms YMGap.Continuum.EpsSplitAdjudication.split_of_singleStepProp
#print axioms YMGap.Continuum.EpsSplitAdjudication.pertStep_vacuous
#print axioms YMGap.Continuum.EpsSplitAdjudication.absorb_forces_nonpos
