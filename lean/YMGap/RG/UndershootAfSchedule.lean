/-
# An undershooting AF nome schedule (ℓ_j = log₂(a_j/a_{j+1}) < 1 by design)

**Label: PROVED `NomeSchedule` construction plus PROVED decidable `DyadicRGStep` checks. The
undershoot design (two-loop running with a `c·g⁴` undershoot, plus finer steps across the data
window β ≈ 2.0–2.98) is MOTIVATION from numerics (audit), NOT a theorem. NOT gap evidence.
`δ_min = 0` for `ℓ ≤ 1` is only a NECESSARY condition: it removes the obstruction but does not
prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.

Schedule `undershootSchedule` (index-consistent with `scaleChain`, no offset):
* `j < 6`: the dyadic crossover `dyTable` (`1/64, 1/8, 7/20, 14/25, 67/100, 147/200`);
* `6 ≤ j ≤ 10`: `usTab`, five fine steps through the data window (`779/1000 → … → 417199/500000`),
  each sized so that the slope band of the data gives `ℓ_j ≤ 1 − 0.03·g_j⁴` (audit);
* `j ≥ 11`: `1 − 1941658544/usF (j−11)`, where `usF` is an explicit Nat recursion. Its increment is
  `10⁹·(1 − 7/((i+8)(i+16)))` (the undershoot: `7/((i+8)(i+16)) ≈ 0.029–0.030·g⁴`) plus the
  two-loop terms `10⁹·(κ'/D + 0.34/D²)` with `D = usF/10⁹` and `κ' = κ/ln 2 = 0.608078`, plus 1.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.DyadicCrossoverSchedule

namespace YMGap.RG.UndershootAfSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.StrongCouplingNomeThreshold (inv55)
open YMGap.RG.DyadicCrossoverSchedule (DyadicRGStep dyTable)

/-- Data-window table, `j = 6..10`. -/
def usTab : Nat → Q'
  | 6 => Q'.mkPos 779 1000 (by decide)
  | 7 => Q'.mkPos 1987 2500 (by decide)
  | 8 => Q'.mkPos 81081 100000 (by decide)
  | 9 => Q'.mkPos 205731 250000 (by decide)
  | _ => Q'.mkPos 417199 500000 (by decide)

/-- Tail increment at tail step `i` from the current value `f`. -/
def usInc (i f : Nat) : Nat :=
  (1000000000 - 7000000000 / ((i + 8) * (i + 16))) + 608078000000000000 / f
    + 340000000000000000000000000 / (f * f) + 1

/-- Tail recursion (`usF i ≈ 10⁹·A/(1 − w_{11+i})`). -/
def usF : Nat → Nat
  | 0 => 12577219337
  | i+1 => usF i + usInc i (usF i)

theorem usF_mono (i : Nat) : usF i ≤ usF (i+1) := Nat.le_add_right _ _

theorem usF_ge (i : Nat) : 12577219337 + i ≤ usF i := by
  induction i with
  | zero => exact Nat.le_refl _
  | succ i ih =>
    show 12577219337 + i + 1 ≤ usF i + usInc i (usF i)
    exact Nat.add_le_add ih (Nat.succ_pos _)

theorem usF_pos (i : Nat) : 0 < usF i :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_trans (Nat.le_add_right 12577219337 i) (usF_ge i))

/-- Tail gap `1 − w_{11+i} = 1941658544/usF i`. -/
def usGap (i : Nat) : Q' := Q'.mkPos 1941658544 (usF i) (usF_pos i)

theorem usGap_den (i : Nat) : (usGap i).den = usF i := by
  unfold usGap; rw [Q'.mkPos_den]

theorem usGap_anti (i : Nat) : usGap (i+1) ≤ usGap i := by
  show (1941658544 : Int) * ((usGap i).den : Int) ≤ 1941658544 * ((usGap (i+1)).den : Int)
  rw [usGap_den, usGap_den]
  exact Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr (usF_mono i)) (by decide)

theorem usGap_pos (i : Nat) : (0 : Q') < usGap i := by
  show (0 : Int) * ((usGap i).den : Int) < 1941658544 * 1
  rw [Int.zero_mul]; decide

theorem usGap_lt_one (i : Nat) : usGap i < (1 : Q') := by
  show (1941658544 : Int) * 1 < 1 * ((usGap i).den : Int)
  rw [usGap_den, Int.mul_one, Int.one_mul]
  exact Int.ofNat_lt.mpr (Nat.lt_of_lt_of_le (by decide : 1941658544 < 12577219337 + 0)
    (Nat.le_trans (Nat.add_le_add_left (Nat.zero_le i) _) (usF_ge i)))

theorem usGap_le_of_modulus (eps : Q') (he : (0 : Q') < eps) (i : Nat)
    (hi : 1941658544 * eps.den ≤ i) : usGap i ≤ eps := by
  have hn1 : (1 : Int) ≤ eps.num := Int.add_one_le_of_lt (Q'.num_pos_of_pos he)
  show (1941658544 : Int) * (eps.den : Int) ≤ eps.num * ((usGap i).den : Int)
  rw [usGap_den]
  have hE : 1941658544 * eps.den ≤ usF i :=
    Nat.le_trans hi (Nat.le_trans (Nat.le_add_left i 12577219337) (usF_ge i))
  have h1 : ((1941658544 * eps.den : Nat) : Int) ≤ ((usF i : Nat) : Int) := Int.ofNat_le.mpr hE
  rw [Int.natCast_mul] at h1
  have h2 : (1 : Int) * ((usF i : Nat) : Int) ≤ eps.num * ((usF i : Nat) : Int) :=
    Int.mul_le_mul_of_nonneg_right hn1 (Int.natCast_nonneg _)
  rw [Int.one_mul] at h2
  exact Int.le_trans h1 h2

/-- The undershooting nome joined to the dyadic crossover. -/
def usNome (j : Nat) : Q' :=
  if j < 6 then dyTable j else if j < 11 then usTab j else (1 : Q') - usGap (j - 11)

private theorem not_lt_of_le' {a b : Nat} (h : b ≤ a) : ¬ a < b := fun h' =>
  Nat.lt_irrefl a (Nat.lt_of_lt_of_le h' h)

private theorem tail_eq (j : Nat) (hj : 11 ≤ j) : usNome j = (1 : Q') - usGap (j - 11) := by
  unfold usNome
  rw [if_neg (not_lt_of_le' (Nat.le_trans (by decide : 6 ≤ 11) hj)), if_neg (not_lt_of_le' hj)]

private theorem head_pos : ∀ j, j < 11 → (0 : Q') < usNome j := by decide
private theorem head_lt_one : ∀ j, j < 11 → usNome j < (1 : Q') := by decide
private theorem head_mono : ∀ j, j < 11 → usNome j ≤ usNome (j+1) := by decide

private theorem one_sub_le {a b : Q'} (h : a ≤ b) : (1 : Q') - b ≤ (1 : Q') - a :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

private theorem us_mono (j : Nat) : usNome j ≤ usNome (j+1) := by
  by_cases h : j < 11
  · exact head_mono j h
  · have hj : 11 ≤ j := Nat.not_lt.mp h
    have e : j + 1 - 11 = (j - 11) + 1 := Nat.succ_sub hj
    rw [tail_eq j hj, tail_eq (j+1) (Nat.le_succ_of_le hj), e]
    exact one_sub_le (usGap_anti (j - 11))

/-- **The undershooting schedule is a `NomeSchedule` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
def undershootSchedule : NomeSchedule where
  nome := usNome
  nome_pos := fun j => by
    by_cases h : j < 11
    · exact head_pos j h
    · rw [tail_eq j (Nat.not_lt.mp h)]
      exact YMGap.Continuum.HKPos.one_sub_pos (usGap_lt_one _)
  nome_lt_one := fun j => by
    by_cases h : j < 11
    · exact head_lt_one j h
    · rw [tail_eq j (Nat.not_lt.mp h)]
      exact YMGap.Continuum.AFTrajectoryCertificate.one_sub_lt_one (usGap_pos _)
  nome_mono := us_mono
  limitModulus := fun eps => 11 + 1941658544 * eps.den
  nome_limit := fun eps he j hj => by
    rw [tail_eq j (Nat.le_trans (Nat.le_add_right 11 _) hj)]
    have hj' : 1941658544 * eps.den + 11 ≤ j := by rw [Nat.add_comm]; exact hj
    exact one_sub_le (usGap_le_of_modulus eps he (j - 11) (Nat.le_sub_of_add_le hj'))

/-- Seed `w_0 = 1/64 ≤ 1/55`; `w_j = dyTable j` for `j < 6`; `w_6 = 779/1000` (join).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem undershoot_join :
    undershootSchedule.nome 0 ≤ inv55 ∧
    (∀ j, j < 6 → undershootSchedule.nome j = dyTable j) ∧
    undershootSchedule.nome 6 = Q'.mkPos 779 1000 (by decide) := by
  decide

/-- **Every step `0 → … → 45` passes `DyadicRGStep` (decidable).** `DyadicRGStep` only bounds a
step from above (SC: `w_f² ≤ w_c`; AF: `D` grows by at most `3/2`), so it accepts undershooting steps
`ℓ < 1`; the data-window and tail steps are all undershooting by design.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem undershoot_steps :
    ∀ n, n < 45 → DyadicRGStep (undershootSchedule.nome n) (undershootSchedule.nome (n+1)) := by
  decide

end YMGap.RG.UndershootAfSchedule
