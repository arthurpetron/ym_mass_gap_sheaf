/-
# A map-robust undershooting AF nome schedule (additive variant of `UndershootAfSchedule`)

**Label: PROVED `NomeSchedule` construction plus PROVED decidable `DyadicRGStep` checks. The robust design
is MOTIVATION from numerics (audit), NOT a theorem. NOT gap evidence. `δ_min = 0` for `ℓ ≤ 1` is only a
NECESSARY condition: it removes the obstruction but does not prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.

Schedule `robustUndershootSchedule` (index-consistent with `scaleChain`, no offset):
* `j < 6`: the dyadic crossover `dyTable` (`1/64, 1/8, 7/20, 14/25, 67/100, 147/200`);
* `6 ≤ j ≤ 10`: `ruTab`, five data-window steps `779/1000 → 794701/1000000 → 808737/1000000 →
  32873/40000 → 166761/200000`. Each is the largest step for which every model of Numerics §9 (naive
  FHK/BSS knots, BSS slope 2L/hold, matched BSS knots, naive 2L/3L±q, matched 2L/3L+q, c_top held,
  c trend) has `1 − ℓ − 2σ ≥ 0.03` (audit);
* `j ≥ 11`: `1 − 1941658544/ruF (j−11)`, an explicit Nat recursion. Its undershoot is
  `13/((i+6)(i+20))`: the realised naive two-loop undershoot is `0.050–0.057·g⁴` (≥ 0.045), and every
  tail model has `1 − ℓ − 2σ ≥ 0.0072·g⁴` (audit).

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.DyadicCrossoverSchedule

namespace YMGap.RG.RobustUndershootAfSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.StrongCouplingNomeThreshold (inv55)
open YMGap.RG.DyadicCrossoverSchedule (DyadicRGStep dyTable)

/-- Data-window table, `j = 6..10`. -/
def ruTab : Nat → Q'
  | 6 => Q'.mkPos 779 1000 (by decide)
  | 7 => Q'.mkPos 794701 1000000 (by decide)
  | 8 => Q'.mkPos 808737 1000000 (by decide)
  | 9 => Q'.mkPos 32873 40000 (by decide)
  | _ => Q'.mkPos 166761 200000 (by decide)

/-- Tail increment at tail step `i` from the current value `f`. -/
def ruInc (i f : Nat) : Nat :=
  (1000000000 - 13000000000 / ((i + 6) * (i + 20))) + 608078000000000000 / f
    + 340000000000000000000000000 / (f * f) + 1

/-- Tail recursion (`ruF i ≈ 10⁹·A/(1 − w_{11+i})`). -/
def ruF : Nat → Nat
  | 0 => 12516735175
  | i+1 => ruF i + ruInc i (ruF i)

theorem ruF_mono (i : Nat) : ruF i ≤ ruF (i+1) := Nat.le_add_right _ _

theorem ruF_ge (i : Nat) : 12516735175 + i ≤ ruF i := by
  induction i with
  | zero => exact Nat.le_refl _
  | succ i ih =>
    show 12516735175 + i + 1 ≤ ruF i + ruInc i (ruF i)
    exact Nat.add_le_add ih (Nat.succ_pos _)

theorem ruF_pos (i : Nat) : 0 < ruF i :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_trans (Nat.le_add_right 12516735175 i) (ruF_ge i))

/-- Tail gap `1 − w_{11+i} = 1941658544/ruF i`. -/
def ruGap (i : Nat) : Q' := Q'.mkPos 1941658544 (ruF i) (ruF_pos i)

theorem ruGap_den (i : Nat) : (ruGap i).den = ruF i := by
  unfold ruGap; rw [Q'.mkPos_den]

theorem ruGap_anti (i : Nat) : ruGap (i+1) ≤ ruGap i := by
  show (1941658544 : Int) * ((ruGap i).den : Int) ≤ 1941658544 * ((ruGap (i+1)).den : Int)
  rw [ruGap_den, ruGap_den]
  exact Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr (ruF_mono i)) (by decide)

theorem ruGap_pos (i : Nat) : (0 : Q') < ruGap i := by
  show (0 : Int) * ((ruGap i).den : Int) < 1941658544 * 1
  rw [Int.zero_mul]; decide

theorem ruGap_lt_one (i : Nat) : ruGap i < (1 : Q') := by
  show (1941658544 : Int) * 1 < 1 * ((ruGap i).den : Int)
  rw [ruGap_den, Int.mul_one, Int.one_mul]
  exact Int.ofNat_lt.mpr (Nat.lt_of_lt_of_le (by decide : 1941658544 < 12516735175 + 0)
    (Nat.le_trans (Nat.add_le_add_left (Nat.zero_le i) _) (ruF_ge i)))

theorem ruGap_le_of_modulus (eps : Q') (he : (0 : Q') < eps) (i : Nat)
    (hi : 1941658544 * eps.den ≤ i) : ruGap i ≤ eps := by
  have hn1 : (1 : Int) ≤ eps.num := Int.add_one_le_of_lt (Q'.num_pos_of_pos he)
  show (1941658544 : Int) * (eps.den : Int) ≤ eps.num * ((ruGap i).den : Int)
  rw [ruGap_den]
  have hE : 1941658544 * eps.den ≤ ruF i :=
    Nat.le_trans hi (Nat.le_trans (Nat.le_add_left i 12516735175) (ruF_ge i))
  have h1 : ((1941658544 * eps.den : Nat) : Int) ≤ ((ruF i : Nat) : Int) := Int.ofNat_le.mpr hE
  rw [Int.natCast_mul] at h1
  have h2 : (1 : Int) * ((ruF i : Nat) : Int) ≤ eps.num * ((ruF i : Nat) : Int) :=
    Int.mul_le_mul_of_nonneg_right hn1 (Int.natCast_nonneg _)
  rw [Int.one_mul] at h2
  exact Int.le_trans h1 h2

/-- The undershooting nome joined to the dyadic crossover. -/
def ruNome (j : Nat) : Q' :=
  if j < 6 then dyTable j else if j < 11 then ruTab j else (1 : Q') - ruGap (j - 11)

private theorem not_lt_of_le' {a b : Nat} (h : b ≤ a) : ¬ a < b := fun h' =>
  Nat.lt_irrefl a (Nat.lt_of_lt_of_le h' h)

private theorem tail_eq (j : Nat) (hj : 11 ≤ j) : ruNome j = (1 : Q') - ruGap (j - 11) := by
  unfold ruNome
  rw [if_neg (not_lt_of_le' (Nat.le_trans (by decide : 6 ≤ 11) hj)), if_neg (not_lt_of_le' hj)]

private theorem head_pos : ∀ j, j < 11 → (0 : Q') < ruNome j := by decide
private theorem head_lt_one : ∀ j, j < 11 → ruNome j < (1 : Q') := by decide
private theorem head_mono : ∀ j, j < 11 → ruNome j ≤ ruNome (j+1) := by decide

private theorem one_sub_le {a b : Q'} (h : a ≤ b) : (1 : Q') - b ≤ (1 : Q') - a :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

private theorem ru_mono (j : Nat) : ruNome j ≤ ruNome (j+1) := by
  by_cases h : j < 11
  · exact head_mono j h
  · have hj : 11 ≤ j := Nat.not_lt.mp h
    have e : j + 1 - 11 = (j - 11) + 1 := Nat.succ_sub hj
    rw [tail_eq j hj, tail_eq (j+1) (Nat.le_succ_of_le hj), e]
    exact one_sub_le (ruGap_anti (j - 11))

/-- **The undershooting schedule is a `NomeSchedule` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
def robustUndershootSchedule : NomeSchedule where
  nome := ruNome
  nome_pos := fun j => by
    by_cases h : j < 11
    · exact head_pos j h
    · rw [tail_eq j (Nat.not_lt.mp h)]
      exact YMGap.Continuum.HKPos.one_sub_pos (ruGap_lt_one _)
  nome_lt_one := fun j => by
    by_cases h : j < 11
    · exact head_lt_one j h
    · rw [tail_eq j (Nat.not_lt.mp h)]
      exact YMGap.Continuum.AFTrajectoryCertificate.one_sub_lt_one (ruGap_pos _)
  nome_mono := ru_mono
  limitModulus := fun eps => 11 + 1941658544 * eps.den
  nome_limit := fun eps he j hj => by
    rw [tail_eq j (Nat.le_trans (Nat.le_add_right 11 _) hj)]
    have hj' : 1941658544 * eps.den + 11 ≤ j := by rw [Nat.add_comm]; exact hj
    exact one_sub_le (ruGap_le_of_modulus eps he (j - 11) (Nat.le_sub_of_add_le hj'))

/-- Seed `w_0 = 1/64 ≤ 1/55`; `w_j = dyTable j` for `j < 6`; `w_6 = 779/1000` (join).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem robust_join :
    robustUndershootSchedule.nome 0 ≤ inv55 ∧
    (∀ j, j < 6 → robustUndershootSchedule.nome j = dyTable j) ∧
    robustUndershootSchedule.nome 6 = Q'.mkPos 779 1000 (by decide) := by
  decide

/-- **Every step `0 → … → 45` passes `DyadicRGStep` (decidable).** `DyadicRGStep` only bounds a
step from above (SC: `w_f² ≤ w_c`; AF: `D` grows by at most `3/2`), so it accepts undershooting steps
`ℓ < 1`; the data-window and tail steps are all undershooting by design.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem robust_steps :
    ∀ n, n < 45 → DyadicRGStep (robustUndershootSchedule.nome n) (robustUndershootSchedule.nome (n+1)) := by
  decide

end YMGap.RG.RobustUndershootAfSchedule
