/-
# Dyadic crossover schedule, instance B: step-2 fine nome `279/500` (additive W558 copy)

**Label: PROVED construction plus PROVED decidable step checks. NOT gap evidence.**
Additive copy of `DyadicCrossoverSchedule` with exactly one table entry changed:
`dyTableB 3 = 279/500` (instead of `14/25`).  Decision: step 2 moved to w = 279/500
(steps25_H2rest_status.md, Option A, Nov 21).  The original schedule is untouched.

Spacing (decidable, exact rationals, `DyadicRGStep`): `7/20 → 279/500` and
`279/500 → 67/100` both pass.  The second is tight: (AF) for `wf = 67/100` needs
`wc ≥ 0.5571113…` (`dyadic_step_67_tight` below; the spec's "w ≥ 0.557111" is that
value truncated).

U(1) note unchanged from `DyadicCrossoverSchedule`: not non-abelian evidence.
Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.DyadicCrossoverSchedule

namespace YMGap.RG.DyadicCrossoverScheduleW558

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afNomeSchedule)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.StrongCouplingNomeThreshold (inv55)
open YMGap.RG.DyadicCrossoverSchedule (DyadicRGStep dyTable)

/-- The 12 crossover nomes of instance B (indices `0..11`); only index 3 differs. -/
def dyTableB : Nat → Q'
  | 0 => Q'.mkPos 1 64 (by decide)
  | 1 => Q'.mkPos 1 8 (by decide)
  | 2 => Q'.mkPos 7 20 (by decide)
  | 3 => Q'.mkPos 279 500 (by decide)
  | 4 => Q'.mkPos 67 100 (by decide)
  | 5 => Q'.mkPos 147 200 (by decide)
  | 6 => Q'.mkPos 779 1000 (by decide)
  | 7 => Q'.mkPos 81 100 (by decide)
  | 8 => Q'.mkPos 5 6 (by decide)
  | 9 => Q'.mkPos 17 20 (by decide)
  | 10 => Q'.mkPos 173 200 (by decide)
  | _ => Q'.mkPos 877 1000 (by decide)

/-- Instance B agrees with the original table away from index 3. -/
theorem dyTableB_eq (j : Nat) (h : j ≠ 3) : dyTableB j = dyTable j := by
  match j, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, h => exact absurd rfl h
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | _ + 11, _ => rfl

theorem dyTableB_three : dyTableB 3 = Q'.mkPos 279 500 (by decide) := rfl

/-- Instance-B nome: table below 12, `afNome` (same index) from 12 on. -/
def dyNomeB (j : Nat) : Q' := if j < 12 then dyTableB j else afNomeSchedule.nome j

private theorem tableB_pos : ∀ j, j < 12 → (0 : Q') < dyTableB j := by decide
private theorem tableB_lt_one : ∀ j, j < 12 → dyTableB j < (1 : Q') := by decide
private theorem tableB_mono : ∀ j, j < 11 → dyTableB j ≤ dyTableB (j+1) := by decide
private theorem tableB_join : dyTableB 11 ≤ afNomeSchedule.nome 12 := by decide

private theorem eq_elevenB {j : Nat} (h1 : j < 12) (h2 : ¬ j + 1 < 12) : j = 11 :=
  Nat.le_antisymm (Nat.le_of_lt_succ h1) (Nat.le_of_succ_le_succ (Nat.not_lt.mp h2))

private theorem dyB_mono (j : Nat) : dyNomeB j ≤ dyNomeB (j+1) := by
  unfold dyNomeB
  by_cases a : j + 1 < 12
  · rw [if_pos (Nat.lt_trans (Nat.lt_succ_self j) a), if_pos a]
    exact tableB_mono j (Nat.lt_of_succ_lt_succ a)
  · rw [if_neg a]
    by_cases b : j < 12
    · rw [if_pos b, eq_elevenB b a]
      exact tableB_join
    · rw [if_neg b]
      exact afNomeSchedule.nome_mono j

/-- **Instance B is a `NomeSchedule` (PROVED; proofs copied from the original).** -/
def dyadicCrossoverScheduleB : NomeSchedule where
  nome := dyNomeB
  nome_pos := fun j => by
    unfold dyNomeB
    by_cases a : j < 12
    · rw [if_pos a]; exact tableB_pos j a
    · rw [if_neg a]; exact afNomeSchedule.nome_pos j
  nome_lt_one := fun j => by
    unfold dyNomeB
    by_cases a : j < 12
    · rw [if_pos a]; exact tableB_lt_one j a
    · rw [if_neg a]; exact afNomeSchedule.nome_lt_one j
  nome_mono := dyB_mono
  limitModulus := fun eps => 12 + afNomeSchedule.limitModulus eps
  nome_limit := fun eps he j hj => by
    unfold dyNomeB
    have a : ¬ j < 12 := fun h =>
      Nat.lt_irrefl j (Nat.lt_of_lt_of_le h (Nat.le_trans (Nat.le_add_right 12 _) hj))
    rw [if_neg a]
    exact afNomeSchedule.nome_limit eps he j (Nat.le_trans (Nat.le_add_left _ _) hj)

theorem dyB_nome_zero_le_inv55 : dyadicCrossoverScheduleB.nome 0 ≤ inv55 := by decide

/-- **Every instance-B crossover step, including the join `11 → 12`, is one dyadic RG step
(decidable).**  In particular `7/20 → 279/500` and `279/500 → 67/100`. -/
theorem dyadic_steps_crossoverB :
    ∀ n, n < 12 → DyadicRGStep (dyadicCrossoverScheduleB.nome n)
      (dyadicCrossoverScheduleB.nome (n+1)) := by
  decide

/-- The two new spacing checks, stated explicitly (decidable). -/
theorem dyadic_step_2_3B :
    DyadicRGStep (Q'.mkPos 7 20 (by decide)) (Q'.mkPos 279 500 (by decide)) ∧
      DyadicRGStep (Q'.mkPos 279 500 (by decide)) (Q'.mkPos 67 100 (by decide)) := by
  decide

/-- Tightness of `→ 67/100` (decidable): fails at coarse nome `0.557111`, passes at
`0.557112`; the exact (AF) threshold is `0.5571113…`. -/
theorem dyadic_step_67_tight :
    ¬ DyadicRGStep (Q'.mkPos 557111 1000000 (by decide)) (Q'.mkPos 67 100 (by decide)) ∧
      DyadicRGStep (Q'.mkPos 557112 1000000 (by decide)) (Q'.mkPos 67 100 (by decide)) := by
  decide

end YMGap.RG.DyadicCrossoverScheduleW558

#print axioms YMGap.RG.DyadicCrossoverScheduleW558.dyTableB_eq
#print axioms YMGap.RG.DyadicCrossoverScheduleW558.dyadic_steps_crossoverB
#print axioms YMGap.RG.DyadicCrossoverScheduleW558.dyadic_step_2_3B
#print axioms YMGap.RG.DyadicCrossoverScheduleW558.dyadic_step_67_tight
