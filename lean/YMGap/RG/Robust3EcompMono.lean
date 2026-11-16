import YMGap.RG.Robust3EcompMonoBounds

/-!
# Robust3: `ecomp` is monotone, so the running max never activates

`ecomp_mono k : ecomp k ≤ ecomp (k+1)` for every `k`, proved structurally from the per-step bounds of
`Robust3EcompMonoBounds`: `D_{k+1} − D_k ≥ 1 − 1/100 − 31/100 − 4/17 > 0` and `B_{k+1} ≥ B_k`
(`L_n ↑`, `P_n ↓`). Consequence: `r3E_eq k : r3E k = ecomp k` (equality in `Q'`), i.e. neither the running
max nor the `(k+1)/4` floor is ever active.
-/

namespace YMGap.RG.Robust3EcompMono
open YMGap.Constructive
open YMGap.RG.Robust3UndershootAfSchedule
open YMGap.RG.Robust3SeriesBrackets
open YMGap.RG.Robust3StrictFloor
open YMGap.RG.Robust3EcompMonoBounds

/-- `D` of `ecomp k` as an NQ term (definitionally the one inside `ecomp`). -/
def Dnq (k : Nat) : NQ :=
  NQ.add (NQ.add (NQ.add (NQ.add ⟨k + 4, 1⟩ ⟨9989, 2000⟩)
    (NQ.mul (NQ.div ⟨51, 121⟩ (lnS (k + 14))) (harm (k + 7)))) (NQ.div (X2 k) ⟨k + 4, 1⟩))
    (NQ.mul ⟨16, 17⟩ (seg (k + 4) 17))
/-- `B` of `ecomp k`. -/
def Bnq (k : Nat) : NQ := NQ.div (NQ.mul ⟨22, 3⟩ (lnS (k + 14))) (pUp (k + 14))

theorem ecomp_def (k : Nat) : ecomp k = NQ.mul (Dnq k) (Bnq k) := rfl

theorem Dnq_d_pos (k : Nat) : 0 < (Dnq k).d :=
  add_d_pos (add_d_pos (add_d_pos (add_d_pos Nat.one_pos (by decide))
    (mul_d_pos (kp_d_pos k) (harm_d_pos _))) (div_d_pos (X2_d_pos k) (Nat.succ_pos _)))
    (mul_d_pos (by decide) (seg_d_pos _ (Nat.succ_pos _) 17))

theorem Bnq_d_pos (k : Nat) : 0 < (Bnq k).d :=
  div_d_pos (mul_d_pos (by decide) (lnS_d_pos _))
    (n_pos_of_lower (pUp_d_pos _) (by decide) (by decide) (P_nine k))

theorem D_eqv (k : Nat) : (NQ.toQ (Dnq k)).eqv
    ((((NQ.toQ ⟨k + 4, 1⟩ + NQ.toQ ⟨9989, 2000⟩) + T1 k) + T2 k) + Zq k) := by
  have dC : 0 < (⟨9989, 2000⟩ : NQ).d := by decide
  have d1 := mul_d_pos (kp_d_pos k) (harm_d_pos (k + 7))
  have d2 := div_d_pos (y := ⟨k + 4, 1⟩) (X2_d_pos k) (Nat.succ_pos (k + 3))
  have dZ := mul_d_pos (x := ⟨16, 17⟩) (by decide) (seg_d_pos _ (Nat.succ_pos (k + 3)) 17)
  have h1 := toQ_add ⟨k + 4, 1⟩ ⟨9989, 2000⟩ Nat.one_pos dC
  have h2 := Q'.eqv_trans _ _ _ (toQ_add _ _ (add_d_pos Nat.one_pos dC) d1) (Q'.add_eqv_congr_right _ _ _ h1)
  have h3 := Q'.eqv_trans _ _ _ (toQ_add _ _ (add_d_pos (add_d_pos Nat.one_pos dC) d1) d2)
    (Q'.add_eqv_congr_right _ _ _ h2)
  exact Q'.eqv_trans _ _ _
    (toQ_add _ _ (add_d_pos (add_d_pos (add_d_pos Nat.one_pos dC) d1) d2) dZ)
    (Q'.add_eqv_congr_right _ _ _ h3)

theorem ac4' (a b c d : Q') : ((a + b) + (c + d)).eqv ((a + d) + (b + c)) :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (swap_eqv _ _ _)) (Q'.add_assoc_eqv _ _ _)))

/-- Linear combination step for `D_k ≤ D_{k+1}`. -/
theorem core (A A' C t1 t1' t2 t2' z z' e1 e2 e3 : Q') (hA : A'.eqv (A + 1))
    (h1 : t1 ≤ t1' + e1) (h2 : t2 ≤ e2) (h2' : (0 : Q') ≤ t2') (h3 : z ≤ e3 + z')
    (he : (e1 + e2) + e3 ≤ 1) :
    (((A + C) + t1) + t2) + z ≤ (((A' + C) + t1') + t2') + z' := by
  have s1 : (((A + C) + t1) + t2) + z ≤ (((A + C) + (t1' + e1)) + e2) + (e3 + z') :=
    add_le_add2 (add_le_add2 (add_le_add2 (Q'.le_refl' _) h1) h2) h3
  have s2 : ((((A + C) + (t1' + e1)) + e2) + (e3 + z')).eqv
      ((((A + C) + t1') + z') + ((e1 + e2) + e3)) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))
          (Q'.add_assoc_eqv _ _ _)))
      (ac4' _ _ _ _)
  have s4 : ((((A + C) + t1') + z') + 1).eqv (((A' + C) + t1') + z') :=
    Q'.eqv_trans _ _ _ (swap_eqv _ _ _) (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (swap_eqv _ _ _) (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (swap_eqv _ _ _) (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hA))))))
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv s2)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ he) (Q'.le_trans' _ _ _ (Q'.le_of_eqv s4)
      (Q'.add_le_add_right _ _ _ (Q'.add_le_self_of_nonneg _ _ h2')))))

theorem A_succ (k : Nat) : (NQ.toQ ⟨k + 1 + 4, 1⟩).eqv (NQ.toQ ⟨k + 4, 1⟩ + 1) := by
  show ((k + 1 + 4 : Nat) : Int) * ((1 : Nat) : Int)
    = (((k + 4 : Nat) : Int) * ((1 : Nat) : Int) + 1 * ((1 : Nat) : Int)) * ((1 : Nat) : Int)
  have key : (k + 1 + 4) * 1 = ((k + 4) * 1 + 1 * 1) * 1 := by
    rw [Nat.mul_one, Nat.mul_one, Nat.one_mul, Nat.mul_one, Nat.add_right_comm]
  exact_mod_cast key

/-- **`D_k ≤ D_{k+1}`** for every `k`. -/
theorem D_mono (k : Nat) : NQ.toQ (Dnq k) ≤ NQ.toQ (Dnq (k + 1)) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (D_eqv k))
    (Q'.le_trans' _ _ _
      (core _ _ _ _ _ _ _ _ _ _ _ _ (A_succ k) (T1_step k) (T2_le k) (toQ_nonneg _) (Z_step k)
        (by decide))
      (Q'.ge_of_eqv (D_eqv (k + 1))))

theorem le_raw {x y : NQ} (hx : 0 < x.d) (hy : 0 < y.d) (h : NQ.toQ x ≤ NQ.toQ y) :
    x.n * y.d ≤ y.n * x.d := by
  have h' : (x.n : Int) * ((NQ.toQ y).den : Int) ≤ (y.n : Int) * ((NQ.toQ x).den : Int) := h
  rw [toQ_den x hx, toQ_den y hy] at h'
  exact_mod_cast h'

theorem div_mono (X X' P P' : NQ) (hX : 0 < X.d) (hX' : 0 < X'.d) (hP : 0 < P.d) (hP' : 0 < P'.d)
    (hPn : 0 < P.n) (hPn' : 0 < P'.n) (hXX : NQ.toQ X ≤ NQ.toQ X') (hPP : NQ.toQ P' ≤ NQ.toQ P) :
    NQ.toQ (NQ.div X P) ≤ NQ.toQ (NQ.div X' P') := by
  have b1 : 0 < X.d * P.n := Nat.mul_pos hX hPn
  have b2 : 0 < X'.d * P'.n := Nat.mul_pos hX' hPn'
  have r1 := le_raw hX hX' hXX
  have r2 := le_raw hP' hP hPP
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_red _ _ b1))
    (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (toQ_red _ _ b2)))
  show ((X.n * P.d : Nat) : Int) * ((Q'.mkPos ((X'.n * P'.d : Nat) : Int) (X'.d * P'.n) b2).den : Int)
    ≤ ((X'.n * P'.d : Nat) : Int) * ((Q'.mkPos ((X.n * P.d : Nat) : Int) (X.d * P.n) b1).den : Int)
  rw [Q'.mkPos_den, Q'.mkPos_den]
  have key : X.n * P.d * (X'.d * P'.n) ≤ X'.n * P'.d * (X.d * P.n) :=
    calc X.n * P.d * (X'.d * P'.n) = (X.n * X'.d) * (P'.n * P.d) := by ac_rfl
      _ ≤ (X'.n * X.d) * (P.n * P'.d) := Nat.mul_le_mul r1 r2
      _ = X'.n * P'.d * (X.d * P.n) := by ac_rfl
  exact_mod_cast key

theorem X22_eqv (k : Nat) : (NQ.toQ (NQ.mul ⟨22, 3⟩ (lnS (k + 14)))).eqv
    (Q'.mkPos 22 3 (by decide) * LQ (k + 14)) :=
  Q'.eqv_trans _ _ _ (toQ_mul _ _ (by decide) (lnS_d_pos _))
    (Q'.mul_eqv_congr_right _ _ _ (toQ_lit 22 3 (by decide)))

/-- **`B_k ≤ B_{k+1}`** for every `k`. -/
theorem B_mono (k : Nat) : NQ.toQ (Bnq k) ≤ NQ.toQ (Bnq (k + 1)) :=
  div_mono _ _ _ _ (mul_d_pos (by decide) (lnS_d_pos _)) (mul_d_pos (by decide) (lnS_d_pos _))
    (pUp_d_pos _) (pUp_d_pos _)
    (n_pos_of_lower (pUp_d_pos _) (by decide) (by decide) (P_nine k))
    (n_pos_of_lower (pUp_d_pos _) (by decide) (by decide) (P_nine (k + 1)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (X22_eqv k))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (LQ_mono (k + 14)) (by decide))
        (Q'.ge_of_eqv (X22_eqv (k + 1)))))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (pUp_eqv _))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (VQ_anti (k + 14)) (by decide))
        (Q'.ge_of_eqv (pUp_eqv _))))

/-- **`ecomp` is monotone** (structural, all `k`). -/
theorem ecomp_mono (k : Nat) : NQ.toQ (ecomp k) ≤ NQ.toQ (ecomp (k + 1)) := by
  rw [ecomp_def, ecomp_def]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_mul _ _ (Dnq_d_pos k) (Bnq_d_pos k)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (D_mono k) (toQ_nonneg _))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (B_mono k) (toQ_nonneg _))
        (Q'.ge_of_eqv (toQ_mul _ _ (Dnq_d_pos (k + 1)) (Bnq_d_pos (k + 1))))))

/-- **The running max never activates**: `r3E k = ecomp k` (equality), for every `k`. -/
theorem r3E_eq : ∀ k, r3E k = NQ.toQ (ecomp k)
  | 0 => r3Raw_eq 0
  | k + 1 => by
    show Q'.max' (r3E k) (r3Raw (k + 1)) = _
    rw [r3E_eq k, r3Raw_eq (k + 1)]
    unfold Q'.max'
    rw [if_pos (ecomp_mono k)]

end YMGap.RG.Robust3EcompMono
