import YMGap.RG.Robust3LemmaFiiiAlg

/-!
# Robust3: Lemma F (iii) of the task2i proof note, on partial sums (tail `m ≥ 60`)

Proof note §4 (4f) (iii): `η_C = |E^L_C − B·D(m)| ≤ (2m+1)2^{-n}` and
`η' = |(E^L_F − E^L_C) − B·Δ| ≤ (3m+3)2^{-n}`, `n = m+10`, with ideal `B`, `κ'` (hence ideal `D`, `Δ`).

PROVED here (rational, `m = k+4 ≥ 60`, `n = k+14`, any `j`): the same bounds with the ideal `B`, `κ'` replaced
by the Lean partial-sum values at a deeper index `N` (`N = n+j` for `η_C`, `N = n+1+j` for `η'`):
* `lemmaF_iii_C`: `|E^L_C − D(κ'_N, m)·B_N| ≤ (2m+1)·2^{-n}` (two one-sided inequalities);
* `lemmaF_iii_P`: `|(E^L_F − E^L_C) − (D(κ'_N, m+1) − D(κ'_N, m))·B_N| ≤ (3m+3)·2^{-n}` (subtraction-free).

NAMED ASSUMPTION `SERIES_LIMITS_OPEN` (not formalised, unchanged): `ln2 = lim L_N`, `π²/18 = lim S_N`; under it
`B_N → B`, `κ'_N → κ'` and (by continuity of the polynomial `D(·, m)`) these become Lemma F (iii).
-/

namespace YMGap.RG.Robust3LemmaFiii
open YMGap.Constructive
open YMGap.RG.Robust3UndershootAfSchedule
open YMGap.RG.Robust3SeriesBrackets
open YMGap.RG.Robust3StrictFloor
open YMGap.RG.Robust3EcompMonoBounds
open YMGap.RG.Robust3EcompMono
open YMGap.RG.Robust3LemmaF

/-- `(2m+1)` and `(3m+3)` as `Q'`, `m = k+4`. -/
def MC (k : Nat) : Q' := Q'.mkPos ((2 * (k + 4) + 1 : Nat) : Int) 1 (by decide)
def MP (k : Nat) : Q' := Q'.mkPos ((3 * (k + 4) + 3 : Nat) : Int) 1 (by decide)

theorem DQ_nonneg (k : Nat) : (0 : Q') ≤ DQ (kQ k) k :=
  Q'.le_trans' _ _ _ (toQ_nonneg _) (Q'.le_of_eqv (D_eqv' k))

theorem one_le_MC (k : Nat) : (1 : Q') ≤ MC k := by
  show ((1 : Q').num) * ((MC k).den : Int) ≤ ((2 * (k + 4) + 1 : Nat) : Int) * ((1 : Q').den : Int)
  unfold MC; rw [Q'.mkPos_den]
  show (1 : Int) * ((1 : Nat) : Int) ≤ ((2 * (k + 4) + 1 : Nat) : Int) * ((1 : Nat) : Int)
  have key : 1 * 1 ≤ (2 * (k + 4) + 1) * 1 := by simp +arith
  exact_mod_cast key

theorem twom_le_MC (k : Nat) : Q'.mkPos ((2 * (k + 4) : Nat) : Int) 1 (by decide) ≤ MC k := by
  unfold MC
  show ((2 * (k + 4) : Nat) : Int) * ((Q'.mkPos ((2 * (k + 4) + 1 : Nat) : Int) 1 _).den : Int)
    ≤ ((2 * (k + 4) + 1 : Nat) : Int) * ((Q'.mkPos ((2 * (k + 4) : Nat) : Int) 1 _).den : Int)
  rw [Q'.mkPos_den, Q'.mkPos_den]
  have key : 2 * (k + 4) * 1 ≤ (2 * (k + 4) + 1) * 1 := by simp +arith
  exact_mod_cast key

/-- **Lemma F (iii), `η_C`, on partial sums** (`m = k+4 ≥ 60`, `n = k+14`, `N = n+j`):
`E^L_C ≤ D(κ'_N, m)·B_N + 2^{-n}(2m+1)` and `D(κ'_N, m)·B_N ≤ E^L_C + 2^{-n}(2m+1)`. -/
theorem lemmaF_iii_C (k j : Nat) (h56 : 56 ≤ k) :
    NQ.toQ (ecomp k) ≤ DQ (kn (k + 14 + j)) k * Bn (k + 14 + j) + eN k * MC k ∧
      DQ (kn (k + 14 + j)) k * Bn (k + 14 + j) ≤ NQ.toQ (ecomp k) + eN k * MC k := by
  have hB := lemmaF_i k j
  have hD := dD_lean k j
  have hB'1 : Bn (k + 14 + j) ≤ 1 := by have h := B_le_one (k + j); rw [ix] at h; exact h
  have hB'0 : (0 : Q') ≤ Bn (k + 14 + j) := toQ_nonneg _
  have hD0 := DQ_nonneg k
  have he := eN_nonneg k
  have hE := ecomp_eqv k
  constructor
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hE) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hB.1 hD0) ?_
    refine Q'.le_trans' _ _ _ (mul_up hB'0 hD.2) (Q'.add_le_add_left _ _ _ ?_)
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hB'1 he)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (one_le_MC k) he)
  · refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hD.1 hB'0) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hB.2 hD0) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _)) (add_le_add2 (Q'.ge_of_eqv hE) ?_)
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
      (D_le _ k h56 (toQ_nonneg _) (kQ_le k)) he) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (twom_le_MC k) he)

/-! ## `η'` -/

theorem ac4b (a b c d : Q') : ((a + b) + (c + d)).eqv ((c + a) + (d + b)) :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _))
    (Q'.eqv_trans _ _ _ (ac4' _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _))))

theorem eN_succ (k : Nat) : (eN (k + 1)).eqv (eN k * Q'.mkPos 1 2 (by decide)) := by
  unfold eN Q'.eqv
  simp only [mul_num', Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_num]
  have key : 1 * (2 ^ (k + 14) * 2) = 1 * 1 * 2 ^ (k + 1 + 14) := by
    rw [Nat.one_mul, Nat.one_mul, Nat.add_right_comm k 1 14]; exact (Nat.pow_succ 2 (k + 14)).symm
  exact_mod_cast key

theorem closedP (k : Nat) : MC k + Q'.mkPos 1 2 (by decide) * MC (k + 1) ≤ MP k := by
  unfold MC MP
  show Q'.le _ _
  unfold Q'.le
  simp only [add_num', mul_num', Q'.mkPos_num]
  simp only [Q'.add_den_cast]
  simp only [Q'.mul_den_cast]
  simp only [Q'.mkPos_den]
  norm_cast
  simp +arith

theorem eps_sum (k : Nat) : eN k * MC k + eN (k + 1) * MC (k + 1) ≤ eN k * MP k := by
  have h : (eN (k + 1) * MC (k + 1)).eqv (eN k * (Q'.mkPos 1 2 (by decide) * MC (k + 1))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (eN_succ k)) (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ h))
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (closedP k) (eN_nonneg k)))

theorem ixP (k j : Nat) : k + 1 + 14 + j = k + 14 + (j + 1) := by simp +arith

/-- **Lemma F (iii), `η'`, on partial sums** (`m = k+4 ≥ 60`, `n = k+14`, `N = n+1+j`), subtraction-free form of
`|(E^L_F − E^L_C) − (D(κ'_N, m+1) − D(κ'_N, m))·B_N| ≤ 2^{-n}(3m+3)`, with `E^L_F = ecomp (k+1)`. -/
theorem lemmaF_iii_P (k j : Nat) (h56 : 56 ≤ k) :
    NQ.toQ (ecomp (k + 1)) + DQ (kn (k + 14 + (j + 1))) k * Bn (k + 14 + (j + 1))
        ≤ (NQ.toQ (ecomp k) + DQ (kn (k + 14 + (j + 1))) (k + 1) * Bn (k + 14 + (j + 1))) + eN k * MP k ∧
      NQ.toQ (ecomp k) + DQ (kn (k + 14 + (j + 1))) (k + 1) * Bn (k + 14 + (j + 1))
        ≤ (NQ.toQ (ecomp (k + 1)) + DQ (kn (k + 14 + (j + 1))) k * Bn (k + 14 + (j + 1))) + eN k * MP k := by
  have hC := lemmaF_iii_C k (j + 1) h56
  have hF := lemmaF_iii_C (k + 1) j (Nat.le_succ_of_le h56)
  rw [ixP] at hF
  have hs := eps_sum k
  have hs' : eN (k + 1) * MC (k + 1) + eN k * MC k ≤ eN k * MP k :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) hs
  constructor
  · exact Q'.le_trans' _ _ _ (add_le_add2 hF.1 hC.2)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ac4b _ _ _ _)) (Q'.add_le_add_left _ _ _ hs))
  · exact Q'.le_trans' _ _ _ (add_le_add2 hC.1 hF.2)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ac4b _ _ _ _)) (Q'.add_le_add_left _ _ _ hs'))

end YMGap.RG.Robust3LemmaFiii
