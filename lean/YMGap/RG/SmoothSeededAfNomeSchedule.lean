/-
# Smooth seeded schedule: `1/64` → AF over `k` geometric crossover steps

**Label: PROVED construction. NOT gap evidence.**
U(1) note: the seed region is abelian-valid strong coupling; nothing here is non-abelian evidence.

`smoothNome w0 j0 k j` (with `A := afNomeSchedule.nome (j0+k)`):
* `j ≤ j0`: `w0` (inside the proved strong-coupling region, `w0 ≤ 1/55`);
* `j0 < j < j0+k`: `w0 + (A - w0)·(1 - 2^-(j-j0))` (geometric in `A - w`);
* `j ≥ j0+k`: `afNomeSchedule.nome j` (same index, so the gap is `afGap j`).

The `k` chain steps `n < k` (scales `j0+n → j0+n+1`) are the crossover; steps `n ≥ k` are AF.
`smoothSchedule` proves all `NomeSchedule` obligations for every `j0`, `k`, `0 < w0 ≤ 1/55`.
The crossover is where 4D U(1) has its phase transition; non-abelian input must enter there.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.SeededAfNomeSchedule

namespace YMGap.RG.SmoothSeededAfNomeSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afNomeSchedule)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.StrongCouplingNomeThreshold (inv55)

/-- Geometric crossover value `w0 + (A - w0)(1 - 2^-i)`. -/
def cross (w0 A : Q') (i : Nat) : Q' := w0 + (A + -w0) * ((1 : Q') + -HalfPow.half ^ i)

/-- The smooth seeded nome. -/
def smoothNome (w0 : Q') (j0 k j : Nat) : Q' :=
  if j ≤ j0 then w0 else
    if j < j0+k then cross w0 (afNomeSchedule.nome (j0+k)) (j - j0) else afNomeSchedule.nome j

private theorem le_af {w0 : Q'} (h : w0 ≤ inv55) : ∀ k, w0 ≤ afNomeSchedule.nome k
  | 0 => Q'.le_trans' _ _ _ h (by decide)
  | k+1 => Q'.le_trans' _ _ _ (le_af h k) (afNomeSchedule.nome_mono k)

private theorem half_pow_le_one (i : Nat) : HalfPow.half ^ i ≤ (1 : Q') := by
  have h := ExpNeg.pow_half_antitone 0 i
  rw [Nat.zero_add] at h
  exact h

private theorem half_pow_nonneg (i : Nat) : (0 : Q') ≤ HalfPow.half ^ i :=
  Q'.pow_nonneg _ (by decide) i

private theorem one_sub_nonneg {h : Q'} (h1 : h ≤ (1 : Q')) : (0 : Q') ≤ (1 : Q') + -h :=
  Q'.sub_nonneg_of_le h1

private theorem w0_le_cross {w0 A : Q'} (hA : w0 ≤ A) (i : Nat) : w0 ≤ cross w0 A i :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv w0))
    (Q'.add_le_add_left w0 0 _ (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hA)
      (one_sub_nonneg (half_pow_le_one i))))

private theorem cross_le_A {w0 A : Q'} (hA : w0 ≤ A) (i : Nat) : cross w0 A i ≤ A := by
  have h1 : (1 : Q') + -HalfPow.half ^ i ≤ (1 : Q') := by
    have := Q'.add_le_add_left (1 : Q') (-HalfPow.half ^ i) 0
      (by
        have hn := Q'.neg_le_neg (half_pow_nonneg i)
        exact Q'.le_trans' _ _ _ hn (by decide))
    exact Q'.le_trans' _ _ _ this (Q'.le_of_eqv (QPoly.q_add_zero_eqv 1))
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ _ h1 (Q'.sub_nonneg_of_le hA)
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_left w0 _ _ hm)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.add (.var 1) (.neg (.var 0))) (.const 1))) (.var 1) (by decide)
      (fun | 0 => w0 | _ => A)))

private theorem cross_mono {w0 A : Q'} (hA : w0 ≤ A) (i : Nat) :
    cross w0 A i ≤ cross w0 A (i+1) :=
  Q'.add_le_add_left w0 _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (ExpNeg.pow_half_antitone i 1)))
    (Q'.sub_nonneg_of_le hA))

private theorem smooth_mono {w0 : Q'} (h : w0 ≤ inv55) (j0 k j : Nat) :
    smoothNome w0 j0 k j ≤ smoothNome w0 j0 k (j+1) := by
  have hA := le_af h (j0+k)
  unfold smoothNome
  by_cases a1 : j+1 ≤ j0
  · rw [if_pos (Nat.le_trans (Nat.le_succ j) a1), if_pos a1]
    exact Q'.le_refl' _
  · rw [if_neg a1]
    by_cases a0 : j ≤ j0
    · rw [if_pos a0]
      by_cases b1 : j+1 < j0+k
      · rw [if_pos b1]; exact w0_le_cross hA _
      · rw [if_neg b1]; exact le_af h (j+1)
    · rw [if_neg a0]
      have hj0 : j0 ≤ j := Nat.le_of_lt (Nat.lt_of_not_le a0)
      by_cases b0 : j < j0+k
      · rw [if_pos b0]
        by_cases b1 : j+1 < j0+k
        · rw [if_pos b1, Nat.succ_sub hj0]; exact cross_mono hA _
        · rw [if_neg b1]
          have he : j+1 = j0+k := Nat.le_antisymm (Nat.succ_le_of_lt b0) (Nat.not_lt.mp b1)
          rw [he]; exact cross_le_A hA _
      · have b1 : ¬ j+1 < j0+k := fun hb => b0 (Nat.lt_trans (Nat.lt_succ_self j) hb)
        rw [if_neg b0, if_neg b1]
        exact afNomeSchedule.nome_mono j

/-- **The smooth seeded schedule is a `NomeSchedule` (PROVED)** for every `j0`, `k`, `0 < w0 ≤ 1/55`.
U(1) note: abelian-valid strong-coupling seed; not non-abelian evidence. -/
def smoothSchedule (w0 : Q') (hw0 : (0 : Q') < w0) (h55 : w0 ≤ inv55) (j0 k : Nat) :
    NomeSchedule where
  nome := smoothNome w0 j0 k
  nome_pos := fun j => by
    have hA := le_af h55 (j0+k)
    unfold smoothNome
    by_cases a : j ≤ j0
    · rw [if_pos a]; exact hw0
    · rw [if_neg a]
      by_cases b : j < j0+k
      · rw [if_pos b]; exact YMGap.Continuum.MatchedRetuneBridge.q_lt_of_lt_of_le hw0 (w0_le_cross hA _)
      · rw [if_neg b]; exact afNomeSchedule.nome_pos j
  nome_lt_one := fun j => by
    have hA := le_af h55 (j0+k)
    unfold smoothNome
    by_cases a : j ≤ j0
    · rw [if_pos a]; exact Q'.lt_of_le_of_lt h55 (by decide)
    · rw [if_neg a]
      by_cases b : j < j0+k
      · rw [if_pos b]
        exact Q'.lt_of_le_of_lt (cross_le_A hA _) (afNomeSchedule.nome_lt_one (j0+k))
      · rw [if_neg b]; exact afNomeSchedule.nome_lt_one j
  nome_mono := smooth_mono h55 j0 k
  limitModulus := fun eps => (j0+k+1) + afNomeSchedule.limitModulus eps
  nome_limit := fun eps he j hj => by
    unfold smoothNome
    have h1 : j0+k+1 ≤ j := Nat.le_trans (Nat.le_add_right _ _) hj
    have hk : j0+k ≤ j := Nat.le_trans (Nat.le_succ _) h1
    have a : ¬ j ≤ j0 := fun h =>
      Nat.not_succ_le_self j0 (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right j0 k))
        (Nat.le_trans h1 h))
    rw [if_neg a, if_neg (Nat.not_lt.mpr hk)]
    exact afNomeSchedule.nome_limit eps he j (Nat.le_trans (Nat.le_add_left _ _) hj)

/-- `smoothAfNomeSchedule j0 k`: `w0 = 1/64`, `k` crossover steps.
U(1) note: abelian-valid strong-coupling seed; not non-abelian evidence. -/
def smoothAfNomeSchedule (j0 k : Nat) : NomeSchedule :=
  smoothSchedule YMGap.RG.SeededAfNomeSchedule.inv64 (by decide) (by decide) j0 k

/-- Up to `j0` the schedule sits at `1/64 ≤ 1/55` (proved strong-coupling region).
U(1) note: abelian-valid strong-coupling seed; not non-abelian evidence. -/
theorem smooth_nome_le_inv55 (j0 k j : Nat) (hj : j ≤ j0) :
    (smoothAfNomeSchedule j0 k).nome j ≤ inv55 := by
  change smoothNome YMGap.RG.SeededAfNomeSchedule.inv64 j0 k j ≤ inv55
  unfold smoothNome
  rw [if_pos hj]
  decide

/-- From `j0+k` on the schedule IS the AF schedule (gap `afGap j`).
U(1) note: abelian-valid strong-coupling seed; not non-abelian evidence. -/
theorem smooth_nome_af (j0 k j : Nat) (hj0 : ¬ j ≤ j0) (hk : j0+k ≤ j) :
    (smoothAfNomeSchedule j0 k).nome j = afNomeSchedule.nome j := by
  change smoothNome YMGap.RG.SeededAfNomeSchedule.inv64 j0 k j = _
  unfold smoothNome
  rw [if_neg hj0, if_neg (Nat.not_lt.mpr hk)]

end YMGap.RG.SmoothSeededAfNomeSchedule
