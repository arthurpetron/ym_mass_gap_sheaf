/-
# A two-loop AF nome schedule: step `j → j+1` is a factor-2 change of lattice spacing

**Label: PROVED `NomeSchedule` construction plus PROVED decidable step checks. The two-loop
derivation is MOTIVATION (in the audit), NOT a theorem. NOT gap evidence.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).

Convention: the repo nome `w` matches the Numerics `t = -4 ln w`, `g² = 2t`; per the numerics,
the U(1) transition lies between 1/8 and 1/2, inside the crossover.

Schedule `twoLoopSchedule` (index-consistent with `scaleChain`, no offset):
* `j < 6`: the dyadic crossover `dyTable` (`1/64, 1/8, 7/20, 14/25, 67/100, 147/200`);
* `6 ≤ j ≤ 30`: `tlTable j`, the two-loop SU(2) nome `w_j = e^{-t_j/4}`, `g_j² = 2t_j`, with
  `a_j = 2^{-(j-6)} a_6` and `w_6 = 779/1000`, rounded to `1 - w_j ∈ 10⁻⁶ ℤ` (audit);
* `j ≥ 31`: the explicit tail `1 - 1941659/E_j`, `E_j = 10⁶ j + 1197103 + Σ_{k=1}^{j} ⌊608078/k⌋`
  (`1941659/10⁶ ≈ A = 1/(16 b0 ln 2)`, `0.608078 ≈ κ/ln 2`, `κ = b1/(2b0²) = 51/121`; the
  floor-harmonic sum is a rational surrogate of `κ log₂ j`). Numerically (audit) it matches
  two-loop to `≈ 3·10⁻⁴` relative in `1-w` and `|log₂(a_j/a_{j+1}) - 1| ≤ 1.2·10⁻³` per step.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.DyadicCrossoverSchedule

namespace YMGap.RG.TwoLoopAfSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afNomeSchedule)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.StrongCouplingNomeThreshold (inv55)
open YMGap.RG.DyadicCrossoverSchedule (DyadicRGStep dyTable)

/-- Two-loop table, `j = 6..30` (`1 - w_j` rounded to `10⁻⁶`). -/
def tlTable : Nat → Q'
  | 6 => Q'.mkPos 779 1000 (by decide)
  | 7 => Q'.mkPos 32123 40000 (by decide)
  | 8 => Q'.mkPos 822281 1000000 (by decide)
  | 9 => Q'.mkPos 418991 500000 (by decide)
  | 10 => Q'.mkPos 851071 1000000 (by decide)
  | 11 => Q'.mkPos 10777 12500 (by decide)
  | 12 => Q'.mkPos 871679 1000000 (by decide)
  | 13 => Q'.mkPos 175989 200000 (by decide)
  | 14 => Q'.mkPos 110899 125000 (by decide)
  | 15 => Q'.mkPos 893599 1000000 (by decide)
  | 16 => Q'.mkPos 899307 1000000 (by decide)
  | 17 => Q'.mkPos 36177 40000 (by decide)
  | 18 => Q'.mkPos 11363 12500 (by decide)
  | 19 => Q'.mkPos 114153 125000 (by decide)
  | 20 => Q'.mkPos 183407 200000 (by decide)
  | 21 => Q'.mkPos 460261 500000 (by decide)
  | 22 => Q'.mkPos 923723 1000000 (by decide)
  | 23 => Q'.mkPos 463337 500000 (by decide)
  | 24 => Q'.mkPos 929403 1000000 (by decide)
  | 25 => Q'.mkPos 465967 500000 (by decide)
  | 26 => Q'.mkPos 934287 1000000 (by decide)
  | 27 => Q'.mkPos 468241 500000 (by decide)
  | 28 => Q'.mkPos 469267 500000 (by decide)
  | 29 => Q'.mkPos 117557 125000 (by decide)
  | _ => Q'.mkPos 47113 50000 (by decide)

/-- Floor-harmonic surrogate `Σ_{k=1}^{j} ⌊608078/k⌋`. -/
def hn : Nat → Nat
  | 0 => 0
  | i+1 => hn i + 608078 / (i+1)

/-- Tail denominator `E_j = 10⁶ j + 1197103 + hn j`. -/
def tlE (j : Nat) : Nat := 1000000 * j + 1197103 + hn j

theorem tlE_pos (j : Nat) : 0 < tlE j :=
  Nat.lt_of_lt_of_le (by decide : 0 < 1197103)
    (Nat.le_trans (Nat.le_add_left 1197103 (1000000 * j)) (Nat.le_add_right _ _))

/-- Tail gap `1 - w_j = 1941659/E_j`. -/
def tlGap (j : Nat) : Q' := Q'.mkPos 1941659 (tlE j) (tlE_pos j)

theorem tlGap_den (j : Nat) : (tlGap j).den = tlE j := by
  unfold tlGap; rw [Q'.mkPos_den]

theorem tlE_mono (j : Nat) : tlE j ≤ tlE (j+1) :=
  Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 1000000 (Nat.le_succ j)) 1197103)
    (Nat.le_add_right (hn j) _)

theorem tlGap_anti (j : Nat) : tlGap (j+1) ≤ tlGap j := by
  show (1941659 : Int) * ((tlGap j).den : Int) ≤ 1941659 * ((tlGap (j+1)).den : Int)
  rw [tlGap_den, tlGap_den]
  exact Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr (tlE_mono j)) (by decide)

theorem tlGap_pos (j : Nat) : (0 : Q') < tlGap j := by
  show (0 : Int) * ((tlGap j).den : Int) < 1941659 * 1
  rw [Int.zero_mul]; decide

theorem tlGap_lt_one (j : Nat) (hj : 1 ≤ j) : tlGap j < (1 : Q') := by
  show (1941659 : Int) * 1 < 1 * ((tlGap j).den : Int)
  rw [tlGap_den, Int.mul_one, Int.one_mul]
  exact Int.ofNat_lt.mpr (Nat.lt_of_lt_of_le (by decide : 1941659 < 1000000 * 1 + 1197103)
    (Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 1000000 hj) 1197103)
      (Nat.le_add_right _ _)))

/-- Modulus: `tlGap j ≤ ε` once `j ≥ 1941659·ε.den`. -/
theorem tlGap_le_of_modulus (eps : Q') (he : (0 : Q') < eps) (j : Nat)
    (hj : 1941659 * eps.den ≤ j) : tlGap j ≤ eps := by
  have hn1 : (1 : Int) ≤ eps.num := Int.add_one_le_of_lt (Q'.num_pos_of_pos he)
  show (1941659 : Int) * (eps.den : Int) ≤ eps.num * ((tlGap j).den : Int)
  rw [tlGap_den]
  have hE : 1941659 * eps.den ≤ tlE j :=
    Nat.le_trans hj (Nat.le_trans (Nat.le_mul_of_pos_left j (by decide : 0 < 1000000))
      (Nat.le_trans (Nat.le_add_right _ 1197103) (Nat.le_add_right _ _)))
  have h1 : ((1941659 * eps.den : Nat) : Int) ≤ ((tlE j : Nat) : Int) := Int.ofNat_le.mpr hE
  rw [Int.natCast_mul] at h1
  have h2 : (1 : Int) * ((tlE j : Nat) : Int) ≤ eps.num * ((tlE j : Nat) : Int) :=
    Int.mul_le_mul_of_nonneg_right hn1 (Int.natCast_nonneg _)
  rw [Int.one_mul] at h2
  exact Int.le_trans h1 h2

/-- The two-loop nome joined to the dyadic crossover. -/
def tlNome (j : Nat) : Q' :=
  if j < 6 then dyTable j else if j < 31 then tlTable j else (1 : Q') - tlGap j

private theorem not_lt_of_le' {a b : Nat} (h : b ≤ a) : ¬ a < b := fun h' =>
  Nat.lt_irrefl a (Nat.lt_of_lt_of_le h' h)

private theorem tail_eq (j : Nat) (hj : 31 ≤ j) : tlNome j = (1 : Q') - tlGap j := by
  unfold tlNome
  rw [if_neg (not_lt_of_le' (Nat.le_trans (by decide : 6 ≤ 31) hj)), if_neg (not_lt_of_le' hj)]

private theorem head_pos : ∀ j, j < 31 → (0 : Q') < tlNome j := by decide
private theorem head_lt_one : ∀ j, j < 31 → tlNome j < (1 : Q') := by decide
private theorem head_mono : ∀ j, j < 31 → tlNome j ≤ tlNome (j+1) := by decide

private theorem one_sub_le {a b : Q'} (h : a ≤ b) : (1 : Q') - b ≤ (1 : Q') - a :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

private theorem tl_mono (j : Nat) : tlNome j ≤ tlNome (j+1) := by
  by_cases h : j < 31
  · exact head_mono j h
  · have hj : 31 ≤ j := Nat.not_lt.mp h
    rw [tail_eq j hj, tail_eq (j+1) (Nat.le_succ_of_le hj)]
    exact one_sub_le (tlGap_anti j)

/-- **The two-loop schedule (joined to the dyadic crossover) is a `NomeSchedule` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
def twoLoopSchedule : NomeSchedule where
  nome := tlNome
  nome_pos := fun j => by
    by_cases h : j < 31
    · exact head_pos j h
    · have hj : 31 ≤ j := Nat.not_lt.mp h
      rw [tail_eq j hj]
      exact YMGap.Continuum.HKPos.one_sub_pos
        (tlGap_lt_one j (Nat.le_trans (by decide : 1 ≤ 31) hj))
  nome_lt_one := fun j => by
    by_cases h : j < 31
    · exact head_lt_one j h
    · have hj : 31 ≤ j := Nat.not_lt.mp h
      rw [tail_eq j hj]
      exact YMGap.Continuum.AFTrajectoryCertificate.one_sub_lt_one (tlGap_pos j)
  nome_mono := tl_mono
  limitModulus := fun eps => 31 + 1941659 * eps.den
  nome_limit := fun eps he j hj => by
    rw [tail_eq j (Nat.le_trans (Nat.le_add_right 31 _) hj)]
    exact one_sub_le (tlGap_le_of_modulus eps he j (Nat.le_trans (Nat.le_add_left _ 31) hj))

/-- Seed `w_0 = 1/64 ≤ 1/55`; `w_j = dyTable j` for `j < 6`; `w_6 = 779/1000` (join).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem twoLoop_join :
    twoLoopSchedule.nome 0 ≤ inv55 ∧
    (∀ j, j < 6 → twoLoopSchedule.nome j = dyTable j) ∧
    twoLoopSchedule.nome 6 = Q'.mkPos 779 1000 (by decide) := by
  decide

/-- **Every step `0 → 1 → … → 40` is one dyadic RG step (`DyadicRGStep`, decidable)**: the
crossover, the join `5 → 6`, the two-loop table and the table-to-tail junction `30 → 31`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem twoLoop_steps :
    ∀ n, n < 40 → DyadicRGStep (twoLoopSchedule.nome n) (twoLoopSchedule.nome (n+1)) := by
  decide

/-- **Comparison (decidable):** the two-loop nome at index 14 is within `10⁻³` of `afNome 12`
(the old crossover endpoint), so the old schedule reached it 2 scale indices early.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem twoLoop14_near_afNome12 :
    twoLoopSchedule.nome 14 + -afNomeSchedule.nome 12 < Q'.mkPos 1 1000 (by decide) ∧
    afNomeSchedule.nome 12 + -twoLoopSchedule.nome 14 < Q'.mkPos 1 1000 (by decide) := by
  decide

end YMGap.RG.TwoLoopAfSchedule
