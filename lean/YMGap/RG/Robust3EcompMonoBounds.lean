import YMGap.RG.Robust3StrictFloor

/-!
# Robust3: per-step bounds for the monotonicity of `ecomp`

Ingredients for `Robust3EcompMono` (all structural, all `k`), with `m = k+4`, `n = k+14`:
* `kappa_step`: `κ'_n ≤ κ'_{n+1} + 2^{-(k+15)}` (from `L_{n+1} = L_n + 1/((n+1)2^{n+1})`, `L ≥ 1/2`);
* `T1_step`: `κ'_n·H_{m+3} ≤ κ'_{n+1}·H_{m+4} + 1/100`;
* `T2_le`: `κ'_n²·(H_m+1)/m ≤ 31/100` (uses `L_n ≥ 69/100`, `H_m + 1 ≤ 4m/5`);
* `Z_step`: `(16/17)·seg(m,17) ≤ 4/17 + (16/17)·seg(m+1,17)` (via `seg_shift`).
-/

namespace YMGap.RG.Robust3EcompMonoBounds
open YMGap.Constructive
open YMGap.RG.Robust3UndershootAfSchedule
open YMGap.RG.Robust3SeriesBrackets
open YMGap.RG.Robust3StrictFloor

/-! ## Generic helpers -/

theorem add_le_add2 {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h1) (Q'.add_le_add_left _ _ _ h2)

theorem swap_eqv (a b c : Q') : ((a + b) + c).eqv ((a + c) + b) :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))

theorem add_mul_eqv (a b c : Q') : ((a + b) * c).eqv (a * c + b * c) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))))

theorem lower_raw {x : NQ} (hd : 0 < x.d) {a b : Nat} (hb : 0 < b)
    (h : Q'.mkPos (a : Int) b hb ≤ NQ.toQ x) : a * x.d ≤ x.n * b := by
  have h' : (a : Int) * ((NQ.toQ x).den : Int) ≤ (x.n : Int) * ((Q'.mkPos (a : Int) b hb).den : Int) := h
  rw [Q'.mkPos_den, toQ_den x hd] at h'
  exact_mod_cast h'

theorem harm_le : ∀ m, NQ.toQ (harm m) ≤ Q'.mkPos (m : Int) 1 (by decide)
  | 0 => by decide
  | m + 1 => by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_add _ ⟨1, m + 1⟩ (harm_d_pos m) (Nat.succ_pos m))) ?_
    refine Q'.le_trans' _ _ _ (add_le_add2 (harm_le m) (Q'.le_of_eqv (toQ_lit 1 (m + 1) (Nat.succ_pos m)))) ?_
    show ((m : Int) * ((Q'.mkPos 1 (m + 1) _).den : Int) + 1 * ((Q'.mkPos (m : Int) 1 _).den : Int))
        * ((Q'.mkPos ((m + 1 : Nat) : Int) 1 _).den : Int)
      ≤ ((m + 1 : Nat) : Int) * ((Q'.mkPos (m : Int) 1 _ + Q'.mkPos 1 (m + 1) _).den : Int)
    rw [Q'.add_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
    have key : (m * (m + 1) + 1 * 1) * 1 ≤ (m + 1) * (1 * (m + 1)) := by
      rw [Nat.mul_one, Nat.one_mul, Nat.one_mul, Nat.add_mul m 1 (m + 1), Nat.one_mul]
      exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le m)) _
    exact_mod_cast key

/-! ## `κ'_n = (51/121)/L_n` -/

theorem idx14 (k : Nat) : 14 + k = k + 14 := Nat.add_comm 14 k

theorem L_069 (k : Nat) : Q'.mkPos 69 100 (by decide) ≤ LQ (k + 14) := by
  have h := (ln2_partial_bracket 14 k).1
  rw [idx14] at h
  exact Q'.le_trans' _ _ _ (by decide) h

theorem L_raw (k : Nat) :
    (lnS (k + 15)).n * ((lnS (k + 14)).d * ((k + 15) * 2 ^ (k + 15)))
      = ((lnS (k + 14)).n * ((k + 15) * 2 ^ (k + 15)) + 1 * (lnS (k + 14)).d) * (lnS (k + 15)).d := by
  have h : (NQ.toQ (lnS (k + 15))).num * ((NQ.toQ (lnS (k + 14)) + lterm (k + 14)).den : Int)
      = ((NQ.toQ (lnS (k + 14))).num * ((lterm (k + 14)).den : Int)
          + (lterm (k + 14)).num * ((NQ.toQ (lnS (k + 14))).den : Int))
        * ((NQ.toQ (lnS (k + 15))).den : Int) := LQ_succ (k + 14)
  rw [Q'.add_den_cast] at h
  unfold lterm at h
  rw [Q'.mkPos_den, Q'.mkPos_num, toQ_den _ (lnS_d_pos (k + 14)), toQ_den _ (lnS_d_pos (k + 15)),
    toQ_num, toQ_num] at h
  exact_mod_cast h

theorem kappa_nat (a b a' b' P K : Nat) (hK : 15 ≤ K) (hKP : 0 < K * P)
    (E : a' * (b * (K * P)) = (a * (K * P) + 1 * b) * b') (H1 : 1 * b ≤ a * 2) (H2 : 1 * b' ≤ a' * 2) :
    51 * b * (121 * a' * P) ≤ (51 * b' * P + 1 * (121 * a')) * (121 * a) := by
  rw [Nat.one_mul] at E H1 H2
  rw [Nat.one_mul]
  refine Nat.le_of_mul_le_mul_right ?_ hKP
  have hl : 51 * b * (121 * a' * P) * (K * P)
      = 51 * 121 * P * (a * (K * P)) * b' + 51 * 121 * P * (b * b') := by
    calc 51 * b * (121 * a' * P) * (K * P) = 51 * 121 * P * (a' * (b * (K * P))) := by ac_rfl
      _ = 51 * 121 * P * ((a * (K * P) + b) * b') := by rw [E]
      _ = _ := by rw [Nat.add_mul, Nat.mul_add]; ac_rfl
  have hr : (51 * b' * P + 121 * a') * (121 * a) * (K * P)
      = 51 * 121 * P * (a * (K * P)) * b' + (121 * 121 * K) * ((a * a') * P) := by
    rw [Nat.add_mul, Nat.add_mul]; ac_rfl
  rw [hl, hr]
  apply Nat.add_le_add_left
  calc 51 * 121 * P * (b * b') ≤ 51 * 121 * P * ((a * 2) * (a' * 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul H1 H2)
    _ = (51 * 2 * 2 * 121) * ((a * a') * P) := by ac_rfl
    _ ≤ (121 * 121 * K) * ((a * a') * P) :=
        Nat.mul_le_mul_right _ (Nat.le_trans (by decide) (Nat.mul_le_mul_left _ hK))

/-- `κ'_n` as a `Q'`, `n = k+14`. -/
def kQ (k : Nat) : Q' := NQ.toQ (NQ.div ⟨51, 121⟩ (lnS (k + 14)))

theorem Ln_pos (k : Nat) : 0 < (lnS (k + 14)).n :=
  n_pos_of_lower (lnS_d_pos _) (by decide) (by decide) (L_half k)

theorem kQ_eqv (k : Nat) : (kQ k).eqv (Q'.mkPos ((51 * (lnS (k + 14)).d : Nat) : Int)
    (121 * (lnS (k + 14)).n) (Nat.mul_pos (by decide) (Ln_pos k))) :=
  toQ_red _ _ _

theorem kappa_step (k : Nat) :
    kQ k ≤ kQ (k + 1) + Q'.mkPos 1 (2 ^ (k + 15)) (Nat.two_pow_pos _) := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (kQ_eqv k)) ?_
  refine Q'.le_trans' _ _ _ ?_ (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (kQ_eqv (k + 1))))
  have H1 := lower_raw (lnS_d_pos _) (by decide) (L_half k)
  have H2 := lower_raw (lnS_d_pos _) (by decide) (L_half (k + 1))
  have E := L_raw k
  show (((51 * (lnS (k + 14)).d : Nat) : Int))
      * ((Q'.mkPos ((51 * (lnS (k + 15)).d : Nat) : Int) (121 * (lnS (k + 15)).n) _
          + Q'.mkPos 1 (2 ^ (k + 15)) _).den : Int)
    ≤ ((((51 * (lnS (k + 15)).d : Nat) : Int)) * ((Q'.mkPos 1 (2 ^ (k + 15)) _).den : Int)
        + 1 * ((Q'.mkPos ((51 * (lnS (k + 15)).d : Nat) : Int) (121 * (lnS (k + 15)).n) _).den : Int))
      * ((Q'.mkPos ((51 * (lnS (k + 14)).d : Nat) : Int) (121 * (lnS (k + 14)).n) _).den : Int)
  rw [Q'.add_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
  have key := kappa_nat _ _ _ _ (2 ^ (k + 15)) (k + 15) (Nat.le_add_left _ _)
    (Nat.mul_pos (Nat.succ_pos _) (Nat.two_pow_pos _)) E H1 H2
  exact_mod_cast (show 51 * (lnS (k + 14)).d * (121 * (lnS (k + 15)).n * 2 ^ (k + 15))
      ≤ (51 * (lnS (k + 15)).d * 2 ^ (k + 15) + 1 * (121 * (lnS (k + 15)).n)) * (121 * (lnS (k + 14)).n)
    from key)


/-! ## `T1 = κ'_n·H_{m+3}` -/

/-- `T1 k = κ'_{k+14}·H_{k+7}` (the third summand of `D`). -/
def T1 (k : Nat) : Q' := NQ.toQ (NQ.mul (NQ.div ⟨51, 121⟩ (lnS (k + 14))) (harm (k + 7)))

theorem kp_d_pos (k : Nat) : 0 < (NQ.div ⟨51, 121⟩ (lnS (k + 14))).d :=
  div_d_pos (by decide) (Ln_pos k)

theorem pow_bound : ∀ k, 100 * (k + 7) ≤ 2 ^ (k + 15)
  | 0 => by decide
  | k + 1 => by
    calc 100 * (k + 1 + 7) = 100 * (k + 7) + 100 := by rw [Nat.add_right_comm k 1 7, Nat.mul_succ]
      _ ≤ 100 * (k + 7) + 100 * (k + 7) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 100 (Nat.le_add_left 1 (k + 6))) _
      _ = 2 * (100 * (k + 7)) := (Nat.two_mul _).symm
      _ ≤ 2 * 2 ^ (k + 15) := Nat.mul_le_mul_left 2 (pow_bound k)
      _ = 2 ^ (k + 1 + 15) := by rw [Nat.add_right_comm k 1 15, Nat.pow_succ 2 (k + 15), Nat.mul_comm]

theorem delta_H (k : Nat) :
    Q'.mkPos 1 (2 ^ (k + 15)) (Nat.two_pow_pos _) * NQ.toQ (harm (k + 7)) ≤ Q'.mkPos 1 100 (by decide) := by
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (harm_le (k + 7))
    ((Q'.zero_le_iff_num_nonneg _).mpr (show (0 : Int) ≤ 1 by decide))) ?_
  show (1 * ((k + 7 : Nat) : Int)) * ((Q'.mkPos 1 100 _).den : Int)
    ≤ 1 * ((Q'.mkPos 1 (2 ^ (k + 15)) _ * Q'.mkPos ((k + 7 : Nat) : Int) 1 _).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
  have key : 1 * (k + 7) * 100 ≤ 1 * (2 ^ (k + 15) * 1) := by
    rw [Nat.one_mul, Nat.one_mul, Nat.mul_one, Nat.mul_comm]; exact pow_bound k
  exact_mod_cast key

/-- `κ'_n·H_{m+3} ≤ κ'_{n+1}·H_{m+4} + 1/100`. -/
theorem T1_step (k : Nat) : T1 k ≤ T1 (k + 1) + Q'.mkPos 1 100 (by decide) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_mul _ _ (kp_d_pos k) (harm_d_pos _)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (kappa_step k) (toQ_nonneg _))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (add_mul_eqv _ _ _))
        (Q'.le_trans' _ _ _
          (add_le_add2 (Q'.mul_le_mul_of_nonneg_left _ _ _
              (le_add (harm_d_pos (k + 7)) (Nat.succ_pos (k + 7))) (toQ_nonneg _)) (delta_H k))
          (Q'.add_le_add_right _ _ _
            (Q'.ge_of_eqv (toQ_mul _ _ (kp_d_pos (k + 1)) (harm_d_pos _)))))))

/-! ## `T2 = κ'_n²·(H_m+1)/m ≤ 31/100` -/

theorem kQ_le (k : Nat) : kQ k ≤ Q'.mkPos 62 100 (by decide) := by
  have h := lower_raw (lnS_d_pos _) (by decide) (L_069 k)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (kQ_eqv k)) ?_
  show ((51 * (lnS (k + 14)).d : Nat) : Int) * ((Q'.mkPos 62 100 _).den : Int)
    ≤ 62 * ((Q'.mkPos ((51 * (lnS (k + 14)).d : Nat) : Int) (121 * (lnS (k + 14)).n) _).den : Int)
  rw [Q'.mkPos_den, Q'.mkPos_den]
  have key : 51 * (lnS (k + 14)).d * 100 ≤ 62 * (121 * (lnS (k + 14)).n) := by
    refine Nat.le_of_mul_le_mul_left (c := 69) ?_ (by decide)
    calc 69 * (51 * (lnS (k + 14)).d * 100) = (51 * 100) * (69 * (lnS (k + 14)).d) := by ac_rfl
      _ ≤ (51 * 100) * ((lnS (k + 14)).n * 100) := Nat.mul_le_mul_left _ h
      _ = (51 * 100 * 100) * (lnS (k + 14)).n := by ac_rfl
      _ ≤ (69 * 62 * 121) * (lnS (k + 14)).n := Nat.mul_le_mul_right _ (by decide)
      _ = 69 * (62 * (121 * (lnS (k + 14)).n)) := by ac_rfl
  exact_mod_cast key

theorem harm45 : ∀ j, NQ.toQ (harm (j + 4)) ≤ Q'.mkPos ((4 * j + 11 : Nat) : Int) 5 (by decide)
  | 0 => by decide
  | j + 1 => by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_add _ ⟨1, j + 4 + 1⟩ (harm_d_pos _) (Nat.succ_pos _))) ?_
    refine Q'.le_trans' _ _ _ (add_le_add2 (harm45 j)
      (Q'.le_of_eqv (toQ_lit 1 (j + 4 + 1) (Nat.succ_pos _)))) ?_
    show ((((4 * j + 11 : Nat) : Int)) * ((Q'.mkPos ((1 : Nat) : Int) (j + 4 + 1) _).den : Int)
        + ((1 : Nat) : Int) * ((Q'.mkPos ((4 * j + 11 : Nat) : Int) 5 _).den : Int))
        * ((Q'.mkPos ((4 * (j + 1) + 11 : Nat) : Int) 5 _).den : Int)
      ≤ ((4 * (j + 1) + 11 : Nat) : Int)
        * ((Q'.mkPos ((4 * j + 11 : Nat) : Int) 5 _ + Q'.mkPos ((1 : Nat) : Int) (j + 4 + 1) _).den : Int)
    rw [Q'.add_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
    have e : 4 * (j + 1) + 11 = (4 * j + 11) + 4 := by rw [Nat.mul_succ, Nat.add_right_comm]
    have key : ((4 * j + 11) * (j + 4 + 1) + 1 * 5) * 5 ≤ (4 * (j + 1) + 11) * (5 * (j + 4 + 1)) := by
      rw [e]
      calc ((4 * j + 11) * (j + 4 + 1) + 1 * 5) * 5
          = (4 * j + 11) * (5 * (j + 4 + 1)) + 1 * 5 * 5 := by rw [Nat.add_mul]; ac_rfl
        _ ≤ (4 * j + 11) * (5 * (j + 4 + 1)) + 4 * (5 * (j + 4 + 1)) :=
            Nat.add_le_add_left (Nat.le_trans (by decide : 1 * 5 * 5 ≤ 4 * (5 * 5))
              (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left 5 (Nat.le_add_left 5 j)))) _
        _ = ((4 * j + 11) + 4) * (5 * (j + 4 + 1)) := (Nat.add_mul _ _ _).symm
    exact_mod_cast key

theorem harm1_le (j : Nat) :
    NQ.toQ (NQ.add (harm (j + 4)) ⟨1, 1⟩) ≤ Q'.mkPos ((4 * (j + 4) : Nat) : Int) 5 (by decide) := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_add _ ⟨1, 1⟩ (harm_d_pos _) Nat.one_pos)) ?_
  refine Q'.le_trans' _ _ _ (add_le_add2 (harm45 j) (Q'.le_of_eqv (toQ_lit 1 1 Nat.one_pos))) ?_
  show ((((4 * j + 11 : Nat) : Int)) * ((Q'.mkPos ((1 : Nat) : Int) 1 _).den : Int)
      + ((1 : Nat) : Int) * ((Q'.mkPos ((4 * j + 11 : Nat) : Int) 5 _).den : Int))
      * ((Q'.mkPos ((4 * (j + 4) : Nat) : Int) 5 _).den : Int)
    ≤ ((4 * (j + 4) : Nat) : Int)
      * ((Q'.mkPos ((4 * j + 11 : Nat) : Int) 5 _ + Q'.mkPos ((1 : Nat) : Int) 1 _).den : Int)
  rw [Q'.add_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
  have key : ((4 * j + 11) * 1 + 1 * 5) * 5 ≤ (4 * (j + 4)) * (5 * 1) := by
    rw [Nat.mul_add 4 j 4, Nat.mul_one, Nat.one_mul, Nat.add_assoc]
    exact Nat.le_refl _
  exact_mod_cast key

/-- The NQ numerator `κ'²·(H_m+1)` of `T2`. -/
def X2 (k : Nat) : NQ :=
  NQ.mul (NQ.mul (NQ.div ⟨51, 121⟩ (lnS (k + 14))) (NQ.div ⟨51, 121⟩ (lnS (k + 14))))
    (NQ.add (harm (k + 4)) ⟨1, 1⟩)
/-- `T2 k = κ'²·(H_m+1)/m` (the fourth summand of `D`). -/
def T2 (k : Nat) : Q' := NQ.toQ (NQ.div (X2 k) ⟨k + 4, 1⟩)

theorem X2_d_pos (k : Nat) : 0 < (X2 k).d :=
  mul_d_pos (mul_d_pos (kp_d_pos k) (kp_d_pos k)) (add_d_pos (harm_d_pos _) Nat.one_pos)

theorem X2_le (k : Nat) : NQ.toQ (X2 k) ≤ Q'.mkPos ((15376 * (k + 4) : Nat) : Int) 50000 (by decide) := by
  have h0 : (0 : Q') ≤ Q'.mkPos 62 100 (by decide) := by decide
  have hkk : kQ k * kQ k ≤ Q'.mkPos 62 100 (by decide) * Q'.mkPos 62 100 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (kQ_le k) (toQ_nonneg _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (kQ_le k) h0)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (toQ_mul _ _ (mul_d_pos (kp_d_pos k) (kp_d_pos k)) (add_d_pos (harm_d_pos _) Nat.one_pos))
    (Q'.mul_eqv_congr_right _ _ _ (toQ_mul _ _ (kp_d_pos k) (kp_d_pos k))))) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hkk (toQ_nonneg _))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (harm1_le k) (Q'.mul_nonneg _ _ h0 h0))) (Q'.le_of_eqv ?_)
  unfold Q'.eqv
  simp only [Q'.mul_den_cast, Q'.mkPos_den]
  show (62 * 62 * ((4 * (k + 4) : Nat) : Int)) * ((50000 : Nat) : Int)
    = ((15376 * (k + 4) : Nat) : Int) * (((100 : Nat) : Int) * ((100 : Nat) : Int) * ((5 : Nat) : Int))
  have key : (62 * 62 * (4 * (k + 4))) * 50000 = (15376 * (k + 4)) * (100 * 100 * 5) := by
    rw [← Nat.mul_assoc (62 * 62) 4 (k + 4)]
  exact_mod_cast key

theorem T2_le (k : Nat) : T2 k ≤ Q'.mkPos 31 100 (by decide) := by
  have hX := X2_le k
  have hXd := X2_d_pos k
  have h' : ((X2 k).n : Int) * ((Q'.mkPos ((15376 * (k + 4) : Nat) : Int) 50000 (by decide)).den : Int)
      ≤ ((15376 * (k + 4) : Nat) : Int) * ((NQ.toQ (X2 k)).den : Int) := hX
  rw [Q'.mkPos_den, toQ_den _ hXd] at h'
  have hN : (X2 k).n * 50000 ≤ 15376 * (k + 4) * (X2 k).d := by exact_mod_cast h'
  have hb : 0 < (X2 k).d * (k + 4) := Nat.mul_pos hXd (Nat.succ_pos _)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_red ((X2 k).n * 1) ((X2 k).d * (k + 4)) hb)) ?_
  show (((X2 k).n * 1 : Nat) : Int) * ((Q'.mkPos 31 100 _).den : Int)
    ≤ 31 * ((Q'.mkPos (((X2 k).n * 1 : Nat) : Int) ((X2 k).d * (k + 4)) hb).den : Int)
  rw [Q'.mkPos_den, Q'.mkPos_den]
  have key : (X2 k).n * 1 * 100 ≤ 31 * ((X2 k).d * (k + 4)) := by
    refine Nat.le_of_mul_le_mul_left (c := 500) ?_ (by decide)
    calc 500 * ((X2 k).n * 1 * 100) = (X2 k).n * 50000 := by
          rw [Nat.mul_one]; show _ = (X2 k).n * (500 * 100); ac_rfl
      _ ≤ 15376 * (k + 4) * (X2 k).d := hN
      _ = 15376 * ((X2 k).d * (k + 4)) := by ac_rfl
      _ ≤ (500 * 31) * ((X2 k).d * (k + 4)) := Nat.mul_le_mul_right _ (by decide)
      _ = 500 * (31 * ((X2 k).d * (k + 4))) := Nat.mul_assoc _ _ _
  exact_mod_cast key

/-! ## `Z = (16/17)·seg(m,17)` -/

theorem seg_shift (m : Nat) (hm : 0 < m) :
    ∀ r, (NQ.toQ (seg m (r + 1))).eqv (Q'.mkPos 1 m hm + NQ.toQ (seg (m + 1) r))
  | 0 => by
    have h := toQ_add ⟨0, 1⟩ ⟨1, m⟩ Nat.one_pos hm
    rw [show NQ.toQ ⟨0, 1⟩ = 0 from rfl, Q'.zero_add'] at h
    show (NQ.toQ (NQ.add ⟨0, 1⟩ ⟨1, m⟩)).eqv (Q'.mkPos 1 m hm + 0)
    rw [Q'.add_zero']
    exact Q'.eqv_trans _ _ _ h (toQ_lit 1 m hm)
  | r + 1 => by
    have hpos : 0 < m + (r + 1) := Nat.lt_of_lt_of_le hm (Nat.le_add_right _ _)
    have e : m + 1 + r = m + (r + 1) := Nat.add_right_comm m 1 r
    have h3 : (NQ.toQ (seg (m + 1) (r + 1))).eqv (NQ.toQ (seg (m + 1) r) + NQ.toQ ⟨1, m + 1 + r⟩) :=
      toQ_add _ _ (seg_d_pos _ (Nat.succ_pos m) r)
        (Nat.lt_of_lt_of_le (Nat.succ_pos m) (Nat.le_add_right _ _))
    rw [e] at h3
    exact Q'.eqv_trans _ _ _ (toQ_add _ ⟨1, m + (r + 1)⟩ (seg_d_pos m hm (r + 1)) hpos)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (seg_shift m hm r))
        (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
          (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm h3))))

/-- `Z k = (16/17)·Σ_{c<17} 1/(k+4+c)`. -/
def Zq (k : Nat) : Q' := NQ.toQ (NQ.mul ⟨16, 17⟩ (seg (k + 4) 17))

theorem Zq_eqv (k : Nat) : (Zq k).eqv (Q'.mkPos 16 17 (by decide) * NQ.toQ (seg (k + 4) 17)) :=
  Q'.eqv_trans _ _ _ (toQ_mul _ _ (by decide) (seg_d_pos _ (Nat.succ_pos _) 17))
    (Q'.mul_eqv_congr_right _ _ _ (toQ_lit 16 17 (by decide)))

theorem Z_step (k : Nat) : Zq k ≤ Q'.mkPos 4 17 (by decide) + Zq (k + 1) := by
  have hm : 0 < k + 4 := Nat.succ_pos _
  have hs : (0 : Q') ≤ Q'.mkPos 16 17 (by decide) := by decide
  have hraw : Q'.mkPos 16 17 (by decide) * Q'.mkPos 1 (k + 4) hm ≤ Q'.mkPos 4 17 (by decide) := by
    show (16 * 1 : Int) * ((Q'.mkPos 4 17 _).den : Int)
      ≤ 4 * ((Q'.mkPos 16 17 _ * Q'.mkPos 1 (k + 4) hm).den : Int)
    rw [Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
    have key : 16 * 1 * 17 ≤ 4 * (17 * (k + 4)) :=
      Nat.le_trans (by decide : 16 * 1 * 17 ≤ 4 * (17 * 4))
        (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left 17 (Nat.le_add_left 4 k)))
    exact_mod_cast key
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Zq_eqv k)) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (seg_shift (k + 4) hm 16)) (Q'.mul_add_eqv _ _ _))) ?_
  exact Q'.le_trans' _ _ _ (add_le_add2 hraw (Q'.mul_le_mul_of_nonneg_left _ _ _
      (le_add (seg_d_pos _ (Nat.succ_pos _) 16) (Nat.succ_pos _)) hs))
    (Q'.add_le_add_left _ _ _ (Q'.ge_of_eqv (Zq_eqv (k + 1))))

end YMGap.RG.Robust3EcompMonoBounds
