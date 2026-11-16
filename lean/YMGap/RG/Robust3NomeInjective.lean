import YMGap.RG.Robust3SpacingHeatKernel
import YMGap.RG.Robust3EcompMono

/-!
# Robust3: `r3Nome` is strictly increasing (hence injective), and a genuine `aHK : Q' → Q'` witness

* `ecomp_strict`: `E_k < E_{k+1}` (strict; margin `D_{k+1} ≥ D_k + 1/4`, `B_k ≥ 11/30`).
* `r3Nome_strict : i < j → r3Nome i < r3Nome j` (head by `decide`, tail from `ecomp_strict`), so
  `r3Nome_inj : (r3Nome i).eqv (r3Nome j) → i = j` (semantic equality; structural equality implies it).
* `aHKw w`: a bounded decidable search (no classical choice): the first `j < 4·w.den + 12` with `r3Nome j ≃ w`
  (`Q'.eqv` is decidable), value `2^{-j}`; default `1` if none. `j < 4·(r3Nome j).den + 12` holds for every `j`
  (`bound_ok`, from the floor `(k+1)/4 ≤ E_k`), so `aHKw (r3Nome j) = 2^{-j}` (`aHKw_nome`).
* `aHKw_hyps`: `hposHK aHKw ∧ hspacingHK_win aHKw lo hi ∧ hspacingHK_off aHKw lo hi` for all `lo hi`.
Covers ONLY the spacing/positivity hypotheses; `aHKw` is a toy function, not the physical string tension.
-/

namespace YMGap.RG.Robust3NomeInjective

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RG.Robust3UndershootAfSchedule
open YMGap.RG.Robust3SeriesBrackets
open YMGap.RG.Robust3StrictFloor
open YMGap.RG.Robust3EcompMonoBounds
open YMGap.RG.Robust3EcompMono
open YMGap.RG.Robust3SpacingHeatKernel

theorem num_pos' {c : Q'} (hc : (0 : Q') < c) : 0 < c.num := by
  have h : (0 : Int) * (c.den : Int) < c.num * ((0 : Q').den : Int) := hc
  rw [Int.zero_mul] at h
  have e : ((0 : Q').den : Int) = 1 := rfl
  rw [e, Int.mul_one] at h; exact h

theorem lt_add_pos (x c : Q') (hc : (0 : Q') < c) : x < x + c := by
  show x.num * ((x + c).den : Int) < (x + c).num * (x.den : Int)
  rw [Q'.add_den_cast]
  show x.num * ((x.den : Int) * (c.den : Int)) < (x.num * (c.den : Int) + c.num * (x.den : Int)) * (x.den : Int)
  have hd : (0 : Int) < (x.den : Int) := by exact_mod_cast Q'.den_pos x
  rw [Int.add_mul]
  have e : x.num * ((x.den : Int) * (c.den : Int)) = x.num * (c.den : Int) * (x.den : Int) := by ac_rfl
  rw [e]
  exact Int.lt_add_of_pos_right _ (Int.mul_pos (Int.mul_pos (num_pos' hc) hd) hd)

/-! ## Strict monotonicity of `ecomp` -/

theorem B_low (k : Nat) : Q'.mkPos 11 30 (by decide) ≤ NQ.toQ (Bnq k) := by
  have hLd := lnS_d_pos (k + 14)
  have hPd := pUp_d_pos (k + 14)
  have hPn : 0 < (pUp (k + 14)).n := n_pos_of_lower hPd (by decide) (by decide) (P_nine k)
  have hXd : 0 < (NQ.mul ⟨22, 3⟩ (lnS (k + 14))).d := mul_d_pos (by decide) hLd
  have hX : Q'.mkPos 11 3 (by decide) ≤ NQ.toQ (NQ.mul ⟨22, 3⟩ (lnS (k + 14))) :=
    Q'.le_trans' _ _ _
      (show Q'.mkPos 11 3 (by decide) ≤ Q'.mkPos 22 3 (by decide) * Q'.mkPos 1 2 (by decide) by decide)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (L_half k) (by decide))
        (Q'.ge_of_eqv (X22_eqv k)))
  exact div_lower _ _ hXd hPd hPn hX (P_ten k)

/-- `D_k + 1/4 ≤ D_{k+1}`. -/
theorem D_step (k : Nat) : NQ.toQ (Dnq k) + Q'.mkPos 1 4 (by decide) ≤ NQ.toQ (Dnq (k + 1)) := by
  have h3 : Zq k + Q'.mkPos 1 4 (by decide) ≤ (Q'.mkPos 4 17 (by decide) + Q'.mkPos 1 4 (by decide)) + Zq (k + 1) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (Z_step k)) (Q'.le_of_eqv (swap_eqv _ _ _))
  have hc := core (C := NQ.toQ ⟨9989, 2000⟩) (t2' := T2 (k + 1)) (hA := A_succ k) (h1 := T1_step k)
    (h2 := T2_le k) (h2' := toQ_nonneg _) (h3 := h3) (he := by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (D_eqv k))
    (Q'.add_assoc_eqv _ _ _))) (Q'.le_trans' _ _ _ hc (Q'.ge_of_eqv (D_eqv (k + 1))))

/-- **`E_k < E_{k+1}`** (strict), all `k`. -/
theorem ecomp_strict (k : Nat) : NQ.toQ (ecomp k) < NQ.toQ (ecomp (k + 1)) := by
  rw [ecomp_def, ecomp_def]
  have hB0 : (0 : Q') ≤ NQ.toQ (Bnq k) := toQ_nonneg _
  have hq : (0 : Q') ≤ Q'.mkPos 1 4 (by decide) := by decide
  refine lt_of_lt_of_le' (lt_add_pos _ (Q'.mkPos 1 4 (by decide) * Q'.mkPos 11 30 (by decide)) (by decide)) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (Q'.le_of_eqv (toQ_mul _ _ (Dnq_d_pos k) (Bnq_d_pos k)))) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (B_low k) hq)) ?_
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (add_mul_eqv _ _ _)) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (D_step k) hB0) ?_
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (B_mono k) (toQ_nonneg _))
    (Q'.ge_of_eqv (toQ_mul _ _ (Dnq_d_pos (k + 1)) (Bnq_d_pos (k + 1))))

/-! ## `r3Nome` strictly increasing -/

theorem r3E_strict (k : Nat) : r3E k < r3E (k + 1) := by
  rw [r3E_eq k, r3E_eq (k + 1)]; exact ecomp_strict k

theorem r3Gap_strict (k : Nat) : r3Gap (k + 1) < r3Gap k := by
  show ((r3E (k+1)).den : Int) * ((r3Gap k).den : Int) < ((r3E k).den : Int) * ((r3Gap (k+1)).den : Int)
  rw [r3Gap_den, r3Gap_den]
  have h : (r3E k).num * ((r3E (k+1)).den : Int) < (r3E (k+1)).num * ((r3E k).den : Int) := r3E_strict k
  rw [Int.mul_comm ((r3E (k+1)).den : Int), Int.mul_comm ((r3E k).den : Int)]
  exact h

theorem one_sub_lt {a b : Q'} (h : a < b) : (1 : Q') - b < (1 : Q') - a := by
  have h' : a.num * (b.den : Int) < b.num * (a.den : Int) := h
  show ((1 : Int) * (b.den : Int) + -b.num * 1) * (((1 : Q') + -a).den : Int)
    < ((1 : Int) * (a.den : Int) + -a.num * 1) * (((1 : Q') + -b).den : Int)
  rw [Q'.add_den_cast, Q'.add_den_cast]
  show ((1 : Int) * (b.den : Int) + -b.num * 1) * (((1 : Nat) : Int) * (a.den : Int))
    < ((1 : Int) * (a.den : Int) + -a.num * 1) * (((1 : Nat) : Int) * (b.den : Int))
  have e1 : ((1 : Int) * (b.den : Int) + -b.num * 1) * (((1 : Nat) : Int) * (a.den : Int))
      = (b.den : Int) * (a.den : Int) + -(b.num * (a.den : Int)) := by
    rw [Int.one_mul, Int.mul_one, Int.natCast_one, Int.one_mul, Int.add_mul, Int.neg_mul]
  have e2 : ((1 : Int) * (a.den : Int) + -a.num * 1) * (((1 : Nat) : Int) * (b.den : Int))
      = (b.den : Int) * (a.den : Int) + -(a.num * (b.den : Int)) := by
    rw [Int.one_mul, Int.mul_one, Int.natCast_one, Int.one_mul, Int.add_mul, Int.neg_mul, Int.mul_comm (a.den : Int)]
  rw [e1, e2]
  exact Int.add_lt_add_left (Int.neg_lt_neg h') _

theorem tail_eq' (j : Nat) (hj : 11 ≤ j) : r3Nome j = (1 : Q') - r3Gap (j - 11) := by
  have h6 : ¬ j < 6 := fun h => Nat.lt_irrefl j (Nat.lt_of_lt_of_le h (Nat.le_trans (by decide) hj))
  have h11 : ¬ j < 11 := fun h => Nat.lt_irrefl j (Nat.lt_of_lt_of_le h hj)
  unfold r3Nome; rw [if_neg h6, if_neg h11]

theorem head_strict : ∀ j, j < 11 → r3Nome j < r3Nome (j+1) := by decide

theorem r3Nome_step (j : Nat) : r3Nome j < r3Nome (j+1) := by
  by_cases h : j < 11
  · exact head_strict j h
  · have hj : 11 ≤ j := Nat.not_lt.mp h
    rw [tail_eq' j hj, tail_eq' (j+1) (Nat.le_succ_of_le hj), Nat.succ_sub hj]
    exact one_sub_lt (r3Gap_strict (j - 11))

/-- **`r3Nome` is strictly increasing.** -/
theorem r3Nome_strict {i j : Nat} (h : i < j) : r3Nome i < r3Nome j := by
  induction j with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact lt_of_lt_of_le' (ih h') (Q'.le_of_lt (r3Nome_step j))
    · rw [h']; exact r3Nome_step j

theorem not_lt_of_eqv {a b : Q'} (he : a.eqv b) : ¬ a < b := fun hl => by
  have h1 : a.num * (b.den : Int) < b.num * (a.den : Int) := hl
  have h2 : a.num * (b.den : Int) = b.num * (a.den : Int) := he
  rw [h2] at h1; exact Int.lt_irrefl _ h1

/-- **`r3Nome` is injective** (up to `Q'.eqv`, hence also for `=`). -/
theorem r3Nome_inj {i j : Nat} (he : (r3Nome i).eqv (r3Nome j)) : i = j := by
  rcases Nat.lt_or_ge i j with h | h
  · exact absurd (r3Nome_strict h) (not_lt_of_eqv he)
  · rcases Nat.lt_or_eq_of_le h with h' | h'
    · exact absurd (r3Nome_strict h') (not_lt_of_eqv (Q'.eqv_symm he))
    · exact h'.symm

/-! ## A genuine `aHK : Q' → Q'` by bounded decidable search -/

/-- First `j < n` with `r3Nome j ≃ w` (decidable `Q'.eqv`; no classical choice). -/
def firstHit (w : Q') : Nat → Option Nat
  | 0 => none
  | n + 1 => match firstHit w n with
    | some i => some i
    | none => if (r3Nome n).eqv w then some n else none

theorem firstHit_nome (j : Nat) : ∀ n, firstHit (r3Nome j) n = if j < n then some j else none
  | 0 => by rw [if_neg (Nat.not_lt_zero j)]; rfl
  | n + 1 => by
    show (match firstHit (r3Nome j) n with
      | some i => some i
      | none => if (r3Nome n).eqv (r3Nome j) then some n else none) = _
    rw [firstHit_nome j n]
    by_cases hjn : j < n
    · rw [if_pos hjn, if_pos (Nat.lt_succ_of_lt hjn)]
    · rw [if_neg hjn]
      show (if (r3Nome n).eqv (r3Nome j) then some n else none) = _
      by_cases hj : j = n
      · subst hj; rw [if_pos (Q'.eqv_refl _), if_pos (Nat.lt_succ_self _)]
      · rw [if_neg (fun he => hj (r3Nome_inj he).symm)]
        rw [if_neg (fun h => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
          · exact hjn h'
          · exact hj h')]

/-- Every index lies inside its own search window: `j < 4·(r3Nome j).den + 12`. -/
theorem bound_ok (j : Nat) : j < 4 * (r3Nome j).den + 12 := by
  by_cases h : j < 11
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt h) (Nat.le_add_left 12 _)
  · have hj : 11 ≤ j := Nat.not_lt.mp h
    rw [tail_eq' j hj]
    have hd : (((1 : Q') - r3Gap (j - 11)).den : Int) = (r3E (j - 11)).num := by
      show (((1 : Q') + -r3Gap (j - 11)).den : Int) = _
      rw [Q'.add_den_cast]
      show ((1 : Nat) : Int) * ((r3Gap (j - 11)).den : Int) = _
      rw [Int.natCast_one, Int.one_mul, r3Gap_den]
    have hf : ((j - 11 + 1 : Nat) : Int) * ((r3E (j - 11)).den : Int) ≤ (r3E (j - 11)).num * ((4 : Nat) : Int) :=
      r3Floor_le (j - 11)
    rw [← hd] at hf
    have hN : (j - 11 + 1) * (r3E (j - 11)).den ≤ ((1 : Q') - r3Gap (j - 11)).den * 4 := by exact_mod_cast hf
    have h4 : j - 11 + 1 ≤ 4 * ((1 : Q') - r3Gap (j - 11)).den := by
      rw [Nat.mul_comm 4]
      exact Nat.le_trans (Nat.le_mul_of_pos_right _ (Q'.den_pos _)) hN
    have e : j - 11 + 1 + 11 + 1 = j + 2 := by rw [Nat.add_right_comm (j - 11) 1 11, Nat.sub_add_cancel hj]
    exact Nat.lt_of_lt_of_le (show j < j - 11 + 1 + 11 + 1 by rw [e]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self j))
      (Nat.add_le_add_right (Nat.add_le_add_right h4 11) 1)

/-- The witness: `2^{-j}` at the nome `w = r3Nome j` (found by `firstHit`), `1` elsewhere. -/
def aHKw (w : Q') : Q' :=
  match firstHit w (4 * w.den + 12) with
  | some j => aSeq j
  | none => Q'.mkPos 1 1 (by decide)

theorem aHKw_nome (j : Nat) : aHKw (r3Nome j) = aSeq j := by
  unfold aHKw
  rw [firstHit_nome j, if_pos (bound_ok j)]

/-- **Non-vacuity, function level:** `aHKw` satisfies `hposHK`, `hspacingHK_win` and `hspacingHK_off`
for every window `lo, hi` (spacing/positivity part only). -/
theorem aHKw_hyps (lo hi : Nat) :
    hposHK aHKw ∧ hspacingHK_win aHKw lo hi ∧ hspacingHK_off aHKw lo hi :=
  HK_hyps_of_seq aHKw aHKw_nome lo hi

end YMGap.RG.Robust3NomeInjective
