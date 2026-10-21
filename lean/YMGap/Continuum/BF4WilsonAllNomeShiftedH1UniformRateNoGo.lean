/-
# NO-GO: a uniform contraction rate is incompatible with the shifted H1

Label: **NO-GO lemma.** Consumes `path_shiftedEps_forces_rate`
(`BF4WilsonAllNomeShiftedH1Anchor.lean`): under the shifted H1
`PathShiftedEpsBound tr c0` and nondegeneracy, every certified one-step
Rayleigh rate satisfies `side_j·(1 - r_j) ≤ c0` for `j ≥ 1`.

If the rates were uniform, `r_j ≤ r < 1`, then `side_j·(1 - r) ≤ c0` for every
`j ≥ 1`. But `side_j = 2^j` is unbounded and `1 - r > 0`, so `side_j·(1 - r)`
grows past `c0` (Archimedean step, explicit witness). Hence
`PathShiftedEpsBound ∧ PathShiftedNondegenerate ∧ (uniform rate r < 1)` is
contradictory (`shiftedH1_uniformRate_noGo`).

Reading: the shifted H1 is consistent only with rates `r_j → 1` at least as
fast as `1 - c0/side_j`, i.e. a lattice-unit gap closing like `1/side_j`
(fixed physical gap). It can NOT coexist with a scale-uniform lattice-unit gap.
This is an obstruction statement only; nothing about the mass gap is proved.

Axioms: `propext`, `Quot.sound` only (checked with `#print axioms`).
-/

import YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
import YMGap.Constructive.CubeRoot
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.BF4WilsonAllNomeShiftedH1UniformRateNoGo

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeH1FixedScale (WilsonVacuumRayleighRate)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
  (PathShiftedEpsBound PathShiftedNondegenerate path_shiftedEps_forces_rate)

local infix:50 " ≈ " => Q'.eqv

/-- Archimedean step with explicit witness: `B < ofNat M` once `B.num.toNat + 1 ≤ M`. -/
theorem lt_ofNat_of_ge (B : Q') (M : Nat) (hM : B.num.toNat + 1 ≤ M) : B < Q'.ofNat M := by
  show B.num * (((Q'.ofNat M).den : Nat) : Int) < (M : Int) * (B.den : Int)
  have hd : (((Q'.ofNat M).den : Nat) : Int) = 1 := rfl
  rw [hd, Int.mul_one]
  have hP : B.num ≤ (B.num.toNat : Int) := Int.self_le_toNat B.num
  have hD : (1 : Int) ≤ (B.den : Int) := Int.ofNat_le.mpr B.den_pos
  have hm : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg M
  have h1 : (M : Int) * 1 ≤ (M : Int) * (B.den : Int) := Int.mul_le_mul_of_nonneg_left hD hm
  rw [Int.mul_one] at h1
  have h2 : (B.num.toNat : Int) < (M : Int) :=
    Int.ofNat_lt.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hM)
  exact Int.lt_of_lt_of_le (Int.lt_of_le_of_lt hP h2) h1

/-- `side_j` is unbounded: `n ≤ side n`. -/
theorem le_side (n : Nat) : n ≤ side n :=
  Nat.le_of_lt (Nat.lt_pow_self (a := 2) (n := n) (by decide))

private theorem nog_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  show (0 : Int) * 1 ≤ (n : Int) * 1
  rw [Int.zero_mul, Int.mul_one]
  exact Int.natCast_nonneg n

/-- `1 - r > 0` from `r < 1`. -/
theorem sub_pos_of_lt {r : Q'} (h : r < 1) : (0 : Q') < 1 - r := by
  have h' : r.num * 1 < 1 * (r.den : Int) := h
  rw [Int.mul_one, Int.one_mul] at h'
  show (0 : Int) * (((1 : Q').den * r.den - 1 + 1 : Nat) : Int) <
    ((1 : Int) * (r.den : Int) + -r.num * 1) * 1
  rw [Int.zero_mul, Int.mul_one, Int.mul_one, Int.one_mul, ← Int.sub_eq_add_neg]
  exact Int.sub_pos.mpr h'

/-- **Archimedean growth.** For `e > 0` and any `c0` there is `j ≥ 1` with
`c0 < e · side_j`. -/
theorem exists_side_mul_gt (c0 e : Q') (he : (0 : Q') < e) :
    ∃ j : Nat, 1 ≤ j ∧ c0 < e * Q'.ofNat (side j) := by
  refine ⟨(c0 * Q'.recipPos e he).num.toNat + 1, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  have hlt := lt_ofNat_of_ge (c0 * Q'.recipPos e he)
    (side ((c0 * Q'.recipPos e he).num.toNat + 1)) (le_side _)
  have hm := Q'.mul_lt_mul_of_pos_left he hlt
  have hc : e * (c0 * Q'.recipPos e he) ≈ c0 :=
    Q'.eqv_trans _ _ _
      (RingNormaliser.poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => e | 1 => c0 | _ => Q'.recipPos e he))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c0 _ _ (Q'.mul_recipPos_eqv e he))
        (Q'.mul_one_eqv c0))
  exact Q'.lt_of_le_of_lt (Q'.ge_of_eqv hc) hm

/-- **NO-GO.** A contraction rate `r_j ≤ r < 1`, uniform across scales, is
incompatible with the shifted H1 `PathShiftedEpsBound tr c0` (given the qualitative
nondegeneracy that `path_shiftedEps_forces_rate` consumes): `side_j·(1 - r)`
grows past `c0`. -/
theorem shiftedH1_uniformRate_noGo (tr : DyadicSmoothedTrajectory) (c0 r : Q') (rj : Nat → Q')
    (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : PathShiftedEpsBound tr c0) (Hnd : PathShiftedNondegenerate tr fl)
    (Hr : ∀ j, WilsonVacuumRayleighRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth j) (rj j))
    (hunif : ∀ j, rj j ≤ r) (hr1 : r < 1) : False := by
  obtain ⟨j, hj, hgt⟩ := exists_side_mul_gt c0 (1 - r) (sub_pos_of_lt hr1)
  have hforce := path_shiftedEps_forces_rate tr c0 rj fl hfl H1s Hnd Hr j hj
  have hgap : (1 : Q') - r ≤ 1 - rj j :=
    Q'.add_le_add_left 1 (-r) (-(rj j)) (Q'.neg_le_neg (hunif j))
  have hmono := Q'.mul_le_mul_of_nonneg_left _ _ _ hgap (nog_ofNat_nonneg (side j))
  have hX : (1 - r) * Q'.ofNat (side j) ≤ c0 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) (Q'.le_trans' _ _ _ hmono hforce)
  exact Int.lt_irrefl _ (Q'.lt_of_le_of_lt hX hgt)

/-- Contrapositive form: under shifted H1 + nondegeneracy, no uniform rate `r < 1`
bounds the certified rates. -/
theorem shiftedH1_forbids_uniformRate (tr : DyadicSmoothedTrajectory) (c0 r : Q')
    (rj : Nat → Q') (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : PathShiftedEpsBound tr c0) (Hnd : PathShiftedNondegenerate tr fl)
    (Hr : ∀ j, WilsonVacuumRayleighRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth j) (rj j))
    (hr1 : r < 1) : ¬ (∀ j, rj j ≤ r) :=
  fun hunif => shiftedH1_uniformRate_noGo tr c0 r rj fl hfl H1s Hnd Hr hunif hr1

end YMGap.Continuum.BF4WilsonAllNomeShiftedH1UniformRateNoGo
