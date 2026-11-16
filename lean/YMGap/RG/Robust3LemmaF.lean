import YMGap.RG.Robust3EcompMono

/-!
# Robust3: Lemma F (i)–(ii) of the task2i proof note, on partial sums

Proof note (task2i version, `results/task2h_proof_note.md` §4 (4f)) Lemma F compares Lean constants
`B_n = 22L_n/(3P_n)`, `κ'_n = (51/121)/L_n` with the ideal `B = 22 ln2/(3π²)`, `κ' = κ/ln2`:
(i) `0 ≤ B − B_n ≤ 2^{-n}`; (ii) `0 ≤ κ'_n − κ' ≤ 0.9·2^{-n}/(n+1)`.

PROVED here (rational, for all `k, j`, `n = k+14`, `n' = n+j`):
* `lemmaF_i`:  `B_n ≤ B_{n'} ≤ B_n + 2^{-n}`;
* `lemmaF_ii`: `κ'_{n'} ≤ κ'_n ≤ κ'_{n'} + (9/10)·1/((n+1)2^n)`.

NAMED ASSUMPTION `SERIES_LIMITS_OPEN` (not formalised, unchanged): `ln2 = lim L_n`, `π²/18 = lim S_n`. Under it
`B_{n'} → B` and `κ'_{n'} → κ'` as `j → ∞`, which turns `lemmaF_i/ii` into Lemma F (i)/(ii).
NOT formalised: Lemma F (iii) (`η_C`, `η'`) and (iv) (propagation into (4a)–(4e)); see the audit (stop conditions).
-/

namespace YMGap.RG.Robust3LemmaF
open YMGap.Constructive
open YMGap.RG.Robust3UndershootAfSchedule
open YMGap.RG.Robust3SeriesBrackets
open YMGap.RG.Robust3StrictFloor
open YMGap.RG.Robust3EcompMonoBounds
open YMGap.RG.Robust3EcompMono

/-! ## Division helpers -/

theorem div_le {X P : NQ} (hX : 0 < X.d) (hP : 0 < P.d) (hPn : 0 < P.n) (y : Q')
    (h : NQ.toQ X ≤ y * NQ.toQ P) : NQ.toQ (NQ.div X P) ≤ y := by
  have b : 0 < X.d * P.n := Nat.mul_pos hX hPn
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_red _ _ b)) ?_
  have h' : (X.n : Int) * ((y * NQ.toQ P).den : Int) ≤ (y.num * (P.n : Int)) * ((NQ.toQ X).den : Int) := h
  rw [Q'.mul_den_cast, toQ_den _ hP, toQ_den _ hX] at h'
  show ((X.n * P.d : Nat) : Int) * (y.den : Int) ≤ y.num * ((Q'.mkPos _ (X.d * P.n) b).den : Int)
  rw [Q'.mkPos_den]
  have e1 : ((X.n * P.d : Nat) : Int) * (y.den : Int) = (X.n : Int) * ((y.den : Int) * (P.d : Int)) := by
    push_cast; ac_rfl
  have e2 : y.num * ((X.d * P.n : Nat) : Int) = (y.num * (P.n : Int)) * (X.d : Int) := by
    push_cast; ac_rfl
  rw [e1, e2]; exact h'

theorem le_div {X P : NQ} (hX : 0 < X.d) (hP : 0 < P.d) (hPn : 0 < P.n) (y : Q')
    (h : y * NQ.toQ P ≤ NQ.toQ X) : y ≤ NQ.toQ (NQ.div X P) := by
  have b : 0 < X.d * P.n := Nat.mul_pos hX hPn
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (toQ_red _ _ b))
  have h' : (y.num * (P.n : Int)) * ((NQ.toQ X).den : Int) ≤ (X.n : Int) * ((y * NQ.toQ P).den : Int) := h
  rw [Q'.mul_den_cast, toQ_den _ hP, toQ_den _ hX] at h'
  show y.num * ((Q'.mkPos _ (X.d * P.n) b).den : Int) ≤ ((X.n * P.d : Nat) : Int) * (y.den : Int)
  rw [Q'.mkPos_den]
  have e1 : ((X.n * P.d : Nat) : Int) * (y.den : Int) = (X.n : Int) * ((y.den : Int) * (P.d : Int)) := by
    push_cast; ac_rfl
  have e2 : y.num * ((X.d * P.n : Nat) : Int) = (y.num * (P.n : Int)) * (X.d : Int) := by
    push_cast; ac_rfl
  rw [e1, e2]; exact h'

theorem divmul_eqv {X P : NQ} (hX : 0 < X.d) (hP : 0 < P.d) (hPn : 0 < P.n) :
    (NQ.toQ (NQ.div X P) * NQ.toQ P).eqv (NQ.toQ X) := by
  have b : 0 < X.d * P.n := Nat.mul_pos hX hPn
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (toQ_red _ _ b)) ?_
  unfold Q'.eqv
  rw [Q'.mul_den_cast, Q'.mkPos_den, toQ_den _ hP, toQ_den _ hX]
  show ((X.n * P.d : Nat) : Int) * (P.n : Int) * (X.d : Int)
    = (X.n : Int) * (((X.d * P.n : Nat) : Int) * (P.d : Int))
  push_cast; ac_rfl

/-! ## Index bookkeeping and basic bounds (`n = k+14`) -/

theorem ix (k j : Nat) : k + j + 14 = k + 14 + j := Nat.add_right_comm k j 14

theorem P9 (k j : Nat) : Q'.mkPos 9 1 (by decide) ≤ NQ.toQ (pUp (k + 14 + j)) := by
  have h := P_nine (k + j); rw [ix] at h; exact h

theorem Pn_pos (k j : Nat) : 0 < (pUp (k + 14 + j)).n :=
  n_pos_of_lower (pUp_d_pos _) (by decide) (by decide) (P9 k j)

theorem Lh (k j : Nat) : Q'.mkPos 1 2 (by decide) ≤ LQ (k + 14 + j) := by
  have h := L_half (k + j); rw [ix] at h; exact h

theorem L69 (k j : Nat) : Q'.mkPos 69 100 (by decide) ≤ LQ (k + 14 + j) := by
  have h := L_069 (k + j); rw [ix] at h; exact h

theorem Ln_pos' (k j : Nat) : 0 < (lnS (k + 14 + j)).n :=
  n_pos_of_lower (lnS_d_pos _) (by decide) (by decide) (Lh k j)

theorem L34 (k : Nat) : LQ (k + 14) ≤ Q'.mkPos 3 4 (by decide) := by
  have h := (ln2_partial_bracket 1 (k + 13)).2
  rw [idx] at h
  exact Q'.le_trans' _ _ _ h (by decide)

/-- `P_n ≤ P_{n+j} + 6·t_{n+1}`. -/
theorem P_drop (n j : Nat) :
    NQ.toQ (pUp n) ≤ NQ.toQ (pUp (n + j)) + Q'.mkPos 6 1 (by decide) * TQ n := by
  have h1 := pUp_upper n j
  have h2 := (pi2_partial_bracket (n + j) 1).1
  rw [show n + j + 1 = n + 1 + j from Nat.add_right_comm n j 1] at h2
  refine Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.add_le_add_right _ _ _ h2) (by decide)) (Q'.le_of_eqv ?_))
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) (add_eqv2 (Q'.eqv_symm (pUp_eqv _)) ?_)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ _ (by decide))
where
  add_eqv2 {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') : (a + b).eqv (a' + b') :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ha) (Q'.add_eqv_congr_left _ _ _ hb)


/-! ## Lemma F (i): `B_n` -/

/-- `B_n` as a `Q'`. -/
def Bn (n : Nat) : Q' := NQ.toQ (NQ.div (NQ.mul ⟨22, 3⟩ (lnS n)) (pUp n))

theorem Xd (n : Nat) : 0 < (NQ.mul ⟨22, 3⟩ (lnS n)).d := mul_d_pos (by decide) (lnS_d_pos _)

theorem Xn_eqv (n : Nat) : (NQ.toQ (NQ.mul ⟨22, 3⟩ (lnS n))).eqv (Q'.mkPos 22 3 (by decide) * LQ n) :=
  Q'.eqv_trans _ _ _ (toQ_mul _ _ (by decide) (lnS_d_pos _))
    (Q'.mul_eqv_congr_right _ _ _ (toQ_lit 22 3 (by decide)))

theorem four_pow (k : Nat) : 4 ^ (k + 15) = 4 * (2 ^ (k + 14) * 2 ^ (k + 14)) := by
  rw [Nat.pow_succ, Nat.mul_comm, show (4 : Nat) = 2 * 2 from rfl, Nat.mul_pow]

theorem atomF (k : Nat) :
    Q'.mkPos 6 1 (by decide) * Q'.mkPos 1 (4 ^ (k + 15)) (pow4_pos _)
      + Q'.mkPos 22 3 (by decide) * lcap (k + 14)
    ≤ Q'.mkPos 1 (2 ^ (k + 14)) (Nat.two_pow_pos _) * Q'.mkPos 9 1 (by decide) := by
  unfold lcap
  show ((6 * 1 : Int) * ((Q'.mkPos 22 3 _ * Q'.mkPos 1 ((k + 14 + 1) * 2 ^ (k + 14)) _).den : Int)
      + (22 * 1 : Int) * ((Q'.mkPos 6 1 _ * Q'.mkPos 1 (4 ^ (k + 15)) _).den : Int))
      * ((Q'.mkPos 1 (2 ^ (k + 14)) _ * Q'.mkPos 9 1 _).den : Int)
    ≤ (1 * 9 : Int) * ((Q'.mkPos 6 1 _ * Q'.mkPos 1 (4 ^ (k + 15)) _
        + Q'.mkPos 22 3 _ * Q'.mkPos 1 ((k + 14 + 1) * 2 ^ (k + 14)) _).den : Int)
  simp only [Q'.add_den_cast, Q'.mul_den_cast, Q'.mkPos_den]
  rw [four_pow]
  have ha : 1 ≤ 2 ^ (k + 14) := Nat.two_pow_pos _
  generalize 2 ^ (k + 14) = a at ha ⊢
  have hN : 1 ≤ k + 14 + 1 := Nat.succ_pos _
  generalize k + 14 + 1 = N at hN ⊢
  have key : (6 * 1 * (3 * (N * a)) + 22 * 1 * (1 * (4 * (a * a)))) * (a * 1)
      ≤ 1 * 9 * (1 * (4 * (a * a)) * (3 * (N * a))) := by
    have e1 : 6 * 1 * (3 * (N * a)) * (a * 1) = 18 * (N * (a * a)) := by
      rw [Nat.mul_one, Nat.mul_one]; show _ = (6 * 3) * (N * (a * a)); ac_rfl
    have e2 : 22 * 1 * (1 * (4 * (a * a))) * (a * 1) = 88 * (a * a * a) := by
      rw [Nat.mul_one, Nat.mul_one, Nat.one_mul]; show _ = (22 * 4) * (a * a * a); ac_rfl
    have e3 : 1 * 9 * (1 * (4 * (a * a)) * (3 * (N * a))) = 18 * (N * (a * a * a)) + 90 * (N * (a * a * a)) := by
      rw [← Nat.add_mul, Nat.one_mul, Nat.one_mul]; show _ = (9 * 4 * 3) * (N * (a * a * a)); ac_rfl
    rw [Nat.add_mul, e1, e2, e3]
    refine Nat.add_le_add (Nat.mul_le_mul_left 18 (Nat.mul_le_mul_left N
      (Nat.le_mul_of_pos_right _ ha))) ?_
    calc 88 * (a * a * a) ≤ 90 * (a * a * a) := Nat.mul_le_mul_right _ (by decide)
      _ ≤ 90 * (N * (a * a * a)) := Nat.mul_le_mul_left 90 (Nat.le_mul_of_pos_left _ hN)
  exact_mod_cast key


theorem B_le_one (k : Nat) : Bn (k + 14) ≤ 1 := by
  refine div_le (Xd _) (pUp_d_pos _) (Pn_pos k 0) 1 ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Xn_eqv _))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (L34 k) (by decide))
      (Q'.le_trans' _ _ _ (by decide : Q'.mkPos 22 3 (by decide) * Q'.mkPos 3 4 (by decide)
          ≤ (1 : Q') * Q'.mkPos 9 1 (by decide))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (P9 k 0) (by decide))))

/-- **Lemma F (i) on partial sums**: `B_n ≤ B_{n+j} ≤ B_n + 2^{-n}` (`n = k+14`, all `j`). -/
theorem lemmaF_i (k j : Nat) :
    Bn (k + 14) ≤ Bn (k + 14 + j) ∧
      Bn (k + 14 + j) ≤ Bn (k + 14) + Q'.mkPos 1 (2 ^ (k + 14)) (Nat.two_pow_pos _) := by
  have hB0 : (0 : Q') ≤ Bn (k + 14) := toQ_nonneg _
  have hdm := divmul_eqv (Xd (k + 14)) (pUp_d_pos (k + 14)) (Pn_pos k 0)
  have hPP : NQ.toQ (pUp (k + 14 + j)) ≤ NQ.toQ (pUp (k + 14)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (pUp_eqv _))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (S_chain (k + 14) j).2 (by decide))
        (Q'.ge_of_eqv (pUp_eqv _)))
  have hL := ln2_partial_bracket (k + 14) j
  refine ⟨le_div (Xd _) (pUp_d_pos _) (Pn_pos k j) _ ?_, div_le (Xd _) (pUp_d_pos _) (Pn_pos k j) _ ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hPP hB0)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hdm)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Xn_eqv _))
          (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hL.1 (by decide))
            (Q'.ge_of_eqv (Xn_eqv _)))))
  · -- X' ≤ (22/3)(L + c) ≃ X + (22/3)c ≤ B(P' + 6t) + (22/3)c ≤ BP' + δP'
    have h6t : Q'.mkPos 6 1 (by decide) * TQ (k + 14)
        ≤ Q'.mkPos 6 1 (by decide) * Q'.mkPos 1 (4 ^ (k + 15)) (pow4_pos _) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (t_le_pow4 (k + 13)) (by decide)
    have hnn : (0 : Q') ≤ Q'.mkPos 6 1 (by decide) * TQ (k + 14) :=
      Q'.mul_nonneg _ _ (by decide) (toQ_nonneg _)
    have aux : Bn (k + 14) * (Q'.mkPos 6 1 (by decide) * TQ (k + 14))
          + Q'.mkPos 22 3 (by decide) * lcap (k + 14)
        ≤ Q'.mkPos 1 (2 ^ (k + 14)) (Nat.two_pow_pos _) * NQ.toQ (pUp (k + 14 + j)) :=
      Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (B_le_one k) hnn)
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) h6t)))
        (Q'.le_trans' _ _ _ (atomF k)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (P9 k j)
            ((Q'.zero_le_iff_num_nonneg _).mpr (show (0 : Int) ≤ 1 by decide))))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Xn_eqv _)) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hL.2 (by decide)) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _)) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Xn_eqv _)) (Q'.ge_of_eqv hdm))) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (P_drop (k + 14) j) hB0)) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _)) ?_
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ aux) (Q'.ge_of_eqv (add_mul_eqv _ _ _))

/-! ## Lemma F (ii): `κ'_n` -/

/-- `κ'_n` as a `Q'`. -/
def kn (n : Nat) : Q' := NQ.toQ (NQ.div ⟨51, 121⟩ (lnS n))

/-- **Lemma F (ii) on partial sums**: `κ'_{n+j} ≤ κ'_n ≤ κ'_{n+j} + (9/10)/((n+1)2^n)` (`n = k+14`). -/
theorem lemmaF_ii (k j : Nat) :
    kn (k + 14 + j) ≤ kn (k + 14) ∧
      kn (k + 14) ≤ kn (k + 14 + j) + Q'.mkPos 9 10 (by decide) * lcap (k + 14) := by
  have d51 : 0 < (⟨51, 121⟩ : NQ).d := by decide
  have hL := ln2_partial_bracket (k + 14) j
  have hc : (0 : Q') ≤ lcap (k + 14) :=
    (Q'.zero_le_iff_num_nonneg _).mpr (show (0 : Int) ≤ 1 by decide)
  have hd := divmul_eqv d51 (lnS_d_pos (k + 14)) (Ln_pos' k 0)
  have hd' := divmul_eqv d51 (lnS_d_pos (k + 14 + j)) (Ln_pos' k j)
  refine ⟨div_le d51 (lnS_d_pos _) (Ln_pos' k j) _ ?_, div_le d51 (lnS_d_pos _) (Ln_pos' k 0) _ ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hd)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hL.1 (toQ_nonneg _))
  · have hk' : kn (k + 14 + j) ≤ Q'.mkPos 9 10 (by decide) * LQ (k + 14) := by
      have h := kQ_le (k + j)
      unfold kQ at h; rw [ix] at h
      exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
        (by decide : Q'.mkPos 62 100 (by decide) ≤ Q'.mkPos 9 10 (by decide) * Q'.mkPos 69 100 (by decide))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (L69 k 0) (by decide)))
    have hkc : kn (k + 14 + j) * lcap (k + 14) ≤ (Q'.mkPos 9 10 (by decide) * lcap (k + 14)) * LQ (k + 14) :=
      Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hk' hc)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hd')
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hL.2 (toQ_nonneg _))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
          (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hkc) (Q'.ge_of_eqv (add_mul_eqv _ _ _)))))

end YMGap.RG.Robust3LemmaF
