/-
# A crossover schedule with no scale-skipping step: `1/64` → `afNome 12` in 12 dyadic steps

**Label: PROVED construction plus PROVED decidable step checks. NOT gap evidence.**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).
Convention: repo nome `w` matches the Numerics `t = -4 ln w`; U(1) is confined only for
w ≤ 1/8 and already Coulomb (massless) at w = 1/2 and 0.5145 (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).
Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.

Motivation (YM Numerics README §4, numerical only, not proof): the old schedule
`smoothAfNomeSchedule 8 4` joins `afNome` at index 12 in one step `0.779 → 0.8875`, which skips
about 8 dyadic scales. Here the crossover is spread over 12 steps, each within one dyadic RG step.

**One dyadic RG step (`DyadicRGStep wc wf`, definition).** Both of the following hold:
* (SC) `wf² ≤ wc`, i.e. `t_f ≥ t_c / 2` (the strong-coupling mass `m ≈ 3t` at most halves);
* (AF) `2·afA·((1-wc) - (1-wf)) ≤ 3·(1-wc)(1-wf)`, i.e. the AF-equivalent index
  `D(w) := afA/(1-w)` (for `afNome`, `D(w_j) = j + (51/121)⌊log2(j+1)⌋ + 4` exactly) advances
  by at most `3/2`. This exceeds the largest `afNome` increment `1 + 51/121`.
`afNome` is NOT of the form `w_{j+1} = w_j^{1/2}`; its step is one unit of `D`.

Schedule (`j0 = 0`, `k = 12`, index-aligned with `afNome`, so `hafδ` at `n ≥ 12` uses
`afGap n` at the schedule's own nome):
`1/64, 1/8, 7/20, 14/25, 67/100, 147/200, 779/1000, 81/100, 5/6, 17/20, 173/200, 877/1000`,
then `afNome j` for `j ≥ 12` (`afNome 12 = 927009/1044500 ≈ 0.88751`).

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.SmoothSeededAfNomeSchedule

namespace YMGap.RG.DyadicCrossoverSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afNomeSchedule afA)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.StrongCouplingNomeThreshold (inv55)

/-- **One dyadic RG step** from coarse nome `wc` to fine nome `wf` (see header): (SC) `wf² ≤ wc`
and (AF) `2·afA·((1-wc)-(1-wf)) ≤ 3·(1-wc)(1-wf)`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
def DyadicRGStep (wc wf : Q') : Prop :=
  wf * wf ≤ wc ∧ (2 : Q') * afA * (((1 : Q') - wc) - ((1 : Q') - wf)) ≤
    (3 : Q') * (((1 : Q') - wc) * ((1 : Q') - wf))

instance (wc wf : Q') : Decidable (DyadicRGStep wc wf) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The 12 crossover nomes (indices `0..11`). -/
def dyTable : Nat → Q'
  | 0 => Q'.mkPos 1 64 (by decide)
  | 1 => Q'.mkPos 1 8 (by decide)
  | 2 => Q'.mkPos 7 20 (by decide)
  | 3 => Q'.mkPos 14 25 (by decide)
  | 4 => Q'.mkPos 67 100 (by decide)
  | 5 => Q'.mkPos 147 200 (by decide)
  | 6 => Q'.mkPos 779 1000 (by decide)
  | 7 => Q'.mkPos 81 100 (by decide)
  | 8 => Q'.mkPos 5 6 (by decide)
  | 9 => Q'.mkPos 17 20 (by decide)
  | 10 => Q'.mkPos 173 200 (by decide)
  | _ => Q'.mkPos 877 1000 (by decide)

/-- The dyadic crossover nome: table below 12, `afNome` (same index) from 12 on. -/
def dyNome (j : Nat) : Q' := if j < 12 then dyTable j else afNomeSchedule.nome j

private theorem table_pos : ∀ j, j < 12 → (0 : Q') < dyTable j := by decide
private theorem table_lt_one : ∀ j, j < 12 → dyTable j < (1 : Q') := by decide
private theorem table_mono : ∀ j, j < 11 → dyTable j ≤ dyTable (j+1) := by decide
private theorem table_join : dyTable 11 ≤ afNomeSchedule.nome 12 := by decide

private theorem eq_eleven {j : Nat} (h1 : j < 12) (h2 : ¬ j + 1 < 12) : j = 11 :=
  Nat.le_antisymm (Nat.le_of_lt_succ h1) (Nat.le_of_succ_le_succ (Nat.not_lt.mp h2))

private theorem dy_mono (j : Nat) : dyNome j ≤ dyNome (j+1) := by
  unfold dyNome
  by_cases a : j + 1 < 12
  · rw [if_pos (Nat.lt_trans (Nat.lt_succ_self j) a), if_pos a]
    exact table_mono j (Nat.lt_of_succ_lt_succ a)
  · rw [if_neg a]
    by_cases b : j < 12
    · rw [if_pos b, eq_eleven b a]
      exact table_join
    · rw [if_neg b]
      exact afNomeSchedule.nome_mono j

/-- **The dyadic crossover schedule is a `NomeSchedule` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
def dyadicCrossoverSchedule : NomeSchedule where
  nome := dyNome
  nome_pos := fun j => by
    unfold dyNome
    by_cases a : j < 12
    · rw [if_pos a]; exact table_pos j a
    · rw [if_neg a]; exact afNomeSchedule.nome_pos j
  nome_lt_one := fun j => by
    unfold dyNome
    by_cases a : j < 12
    · rw [if_pos a]; exact table_lt_one j a
    · rw [if_neg a]; exact afNomeSchedule.nome_lt_one j
  nome_mono := dy_mono
  limitModulus := fun eps => 12 + afNomeSchedule.limitModulus eps
  nome_limit := fun eps he j hj => by
    unfold dyNome
    have a : ¬ j < 12 := fun h =>
      Nat.lt_irrefl j (Nat.lt_of_lt_of_le h (Nat.le_trans (Nat.le_add_right 12 _) hj))
    rw [if_neg a]
    exact afNomeSchedule.nome_limit eps he j (Nat.le_trans (Nat.le_add_left _ _) hj)

/-- The seed nome `w_0 = 1/64 ≤ 1/55` (proved strong-coupling region).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem dy_nome_zero_le_inv55 : dyadicCrossoverSchedule.nome 0 ≤ inv55 := by decide

/-- From index 12 on the schedule IS `afNome` (same index, so `hafδ` uses `afGap n`).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem dy_nome_af (j : Nat) (hj : 12 ≤ j) : dyadicCrossoverSchedule.nome j = afNomeSchedule.nome j := by
  show dyNome j = _
  unfold dyNome
  rw [if_neg (Nat.not_lt.mpr hj)]

/-- **Every crossover step, including the join `11 → 12`, is one dyadic RG step (decidable).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem dyadic_steps_crossover :
    ∀ n, n < 12 → DyadicRGStep (dyadicCrossoverSchedule.nome n) (dyadicCrossoverSchedule.nome (n+1)) := by
  decide

/-- **The first AF steps `12 → 13 → … → 28` are dyadic too (decidable spot check).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem dyadic_steps_af_prefix :
    ∀ m, m < 16 → DyadicRGStep (afNomeSchedule.nome (12+m)) (afNomeSchedule.nome (12+m+1)) := by
  decide

/-- **None of the four old crossover steps of `smoothAfNomeSchedule 8 4` is dyadic (decidable).**
Steps 0 and 3 fail both parts; steps 1 and 2 fail (AF) only (this definition is conservative there).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem old_steps_not_dyadic :
    ∀ n, n < 4 → ¬ DyadicRGStep
      ((YMGap.RG.SmoothSeededAfNomeSchedule.smoothAfNomeSchedule 8 4).nome (8+n))
      ((YMGap.RG.SmoothSeededAfNomeSchedule.smoothAfNomeSchedule 8 4).nome (8+n+1)) := by
  decide

end YMGap.RG.DyadicCrossoverSchedule
