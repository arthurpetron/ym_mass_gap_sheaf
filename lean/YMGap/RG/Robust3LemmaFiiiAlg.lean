import YMGap.RG.Robust3LemmaF

/-!
# Robust3: algebra for Lemma F (iii) (decoupled `D(κ, m)`, `κ`-Lipschitz bound, `D ≤ 2m`)

`DQ c k` is the `D` of the schedule at `m = k+4` with the `κ'` slot replaced by an arbitrary `c : Q'`.
`D_eqv' k : toQ (Dnq k) ≃ DQ (kQ k) k`, i.e. the Lean `D_n(m)` is `DQ κ'_n k`.
-/

namespace YMGap.RG.Robust3LemmaFiii
open YMGap.Constructive
open YMGap.RG.Robust3UndershootAfSchedule
open YMGap.RG.Robust3SeriesBrackets
open YMGap.RG.Robust3StrictFloor
open YMGap.RG.Robust3EcompMonoBounds
open YMGap.RG.Robust3EcompMono
open YMGap.RG.Robust3LemmaF

theorem add_num' (a b : Q') : (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl
theorem mul_num' (a b : Q') : (a * b).num = a.num * b.num := rfl

/-- Pure rearrangement `((X + (a+b)) + (p+q)) + Z ≃ (((X+a)+p)+Z) + (b+q)`. -/
theorem rearr (X a b p q Z : Q') :
    (((X + (a + b)) + (p + q)) + Z).eqv ((((X + a) + p) + Z) + (b + q)) := by
  have h1 : ((X + (a + b)) + (p + q)).eqv (((X + a) + p) + (b + q)) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)) (ac4' _ _ _ _))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h1) (swap_eqv _ _ _)

/-- `(c'+δ)·x ≃ c'x + δx` as an upper bound for `c·x`. -/
theorem mul_up {c c' δ x : Q'} (hx : (0 : Q') ≤ x) (h : c ≤ c' + δ) : c * x ≤ c' * x + δ * x :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h hx) (Q'.le_of_eqv (add_mul_eqv _ _ _))

/-- `c² ≤ c'² + δ·(c'+c)`-type bound with `c, c' ≤ u`, `2u ≤ v`. -/
theorem sq_up {c c' δ u v : Q'} (hc' : (0 : Q') ≤ c') (hc0 : (0 : Q') ≤ c) (hδ : (0 : Q') ≤ δ)
    (h : c ≤ c' + δ) (hcu : c ≤ u) (hc'u : c' ≤ u) (huv : u + u ≤ v) :
    c * c ≤ c' * c' + δ * v := by
  have h1 : c * c ≤ c' * c + δ * c := mul_up hc0 h
  have h2 : c' * c ≤ c' * c' + c' * δ :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h hc') (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
  have h3 : c' * δ + δ * c ≤ δ * v :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_trans' _ _ _ (add_le_add2 hc'u hcu) huv) hδ))
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h2)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _)) (Q'.add_le_add_left _ _ _ h3)))

/-- Generic `κ`-Lipschitz bound for `D(c) = ((A + c·h) + c²·W) + Z`. -/
theorem dD_gen (A h W Z c c' δ u v : Q') (hc' : (0 : Q') ≤ c') (hδ : (0 : Q') ≤ δ)
    (hh : (0 : Q') ≤ h) (hW : (0 : Q') ≤ W) (hle : c' ≤ c) (hup : c ≤ c' + δ)
    (hcu : c ≤ u) (hc'u : c' ≤ u) (huv : u + u ≤ v) :
    ((A + c' * h) + (c' * c') * W) + Z ≤ ((A + c * h) + (c * c) * W) + Z ∧
    ((A + c * h) + (c * c) * W) + Z ≤ (((A + c' * h) + (c' * c') * W) + Z) + (δ * h + (δ * v) * W) := by
  have hc0 : (0 : Q') ≤ c := Q'.le_trans' _ _ _ hc' hle
  have hsq : c' * c' ≤ c * c :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hle hc')
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hle hc0)
  refine ⟨add_le_add2 (add_le_add2 (add_le_add2 (Q'.le_refl' A)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hle hh)) (Q'.mul_le_mul_of_nonneg_right _ _ _ hsq hW))
    (Q'.le_refl' Z), ?_⟩
  refine Q'.le_trans' _ _ _ (add_le_add2 (add_le_add2 (add_le_add2 (Q'.le_refl' A) (mul_up hh hup))
    (mul_up hW (sq_up hc' hc0 hδ hup hcu hc'u huv))) (Q'.le_refl' Z)) (Q'.le_of_eqv ?_)
  exact rearr _ _ _ _ _ _

/-! ## Decoupled `D(c, m)` -/

def Ak (k : Nat) : Q' := NQ.toQ ⟨k + 4, 1⟩ + NQ.toQ ⟨9989, 2000⟩
def hk (k : Nat) : Q' := NQ.toQ (harm (k + 7))
def hm1 (k : Nat) : Q' := NQ.toQ (NQ.add (harm (k + 4)) ⟨1, 1⟩)
def im (k : Nat) : Q' := Q'.mkPos 1 (k + 4) (Nat.succ_pos _)
/-- `W = (H_m + 1)/m`. -/
def W (k : Nat) : Q' := hm1 k * im k
/-- `D(c, m) = m + 9989/2000 + c·H_{m+3} + c²·(H_m+1)/m + (16/17)·seg(m,17)`, `m = k+4`. -/
def DQ (c : Q') (k : Nat) : Q' := ((Ak k + c * hk k) + (c * c) * W k) + Zq k

theorem divk_eqv (x : NQ) (hx : 0 < x.d) (m : Nat) (hm : 0 < m) :
    (NQ.toQ (NQ.div x ⟨m, 1⟩)).eqv (NQ.toQ x * Q'.mkPos 1 m hm) := by
  refine Q'.eqv_trans _ _ _ (toQ_red (x.n * 1) (x.d * m) (Nat.mul_pos hx hm)) ?_
  unfold Q'.eqv
  simp only [mul_num', Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_num, toQ_num, toQ_den _ hx]
  push_cast; ac_rfl

theorem D_eqv' (k : Nat) : (NQ.toQ (Dnq k)).eqv (DQ (kQ k) k) := by
  have hX : (NQ.toQ (X2 k)).eqv ((kQ k * kQ k) * hm1 k) :=
    Q'.eqv_trans _ _ _ (toQ_mul _ _ (mul_d_pos (kp_d_pos k) (kp_d_pos k)) (add_d_pos (harm_d_pos _) Nat.one_pos))
      (Q'.mul_eqv_congr_right _ _ _ (toQ_mul _ _ (kp_d_pos k) (kp_d_pos k)))
  have h2 : (T2 k).eqv ((kQ k * kQ k) * W k) :=
    Q'.eqv_trans _ _ _ (divk_eqv _ (X2_d_pos k) (k + 4) (Nat.succ_pos _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hX) (Q'.mul_assoc_eqv _ _ _))
  have h1 : (T1 k).eqv (kQ k * hk k) := toQ_mul _ _ (kp_d_pos k) (harm_d_pos _)
  exact Q'.eqv_trans _ _ _ (D_eqv k) (Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ h1))
      (Q'.add_eqv_congr_left _ _ _ h2)))

/-- The Lean `E^L_C = ecomp k` is `D(κ'_n, m)·B_n`. -/
theorem ecomp_eqv (k : Nat) : (NQ.toQ (ecomp k)).eqv (DQ (kQ k) k * Bn (k + 14)) :=
  Q'.eqv_trans _ _ _ (toQ_mul _ _ (Dnq_d_pos k) (Bnq_d_pos k)) (Q'.mul_eqv_congr_right _ _ _ (D_eqv' k))

theorem im_nonneg (k : Nat) : (0 : Q') ≤ im k :=
  (Q'.zero_le_iff_num_nonneg _).mpr (show (0 : Int) ≤ 1 by decide)
theorem W_nonneg (k : Nat) : (0 : Q') ≤ W k := Q'.mul_nonneg _ _ (toQ_nonneg _) (im_nonneg k)

theorem W_le (k : Nat) : W k ≤ Q'.mkPos 4 5 (by decide) := by
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (harm1_le k) (im_nonneg k)) ?_
  unfold im
  show ((((4 * (k + 4) : Nat) : Int)) * 1) * ((Q'.mkPos 4 5 _).den : Int)
    ≤ 4 * ((Q'.mkPos ((4 * (k + 4) : Nat) : Int) 5 _ * Q'.mkPos 1 (k + 4) _).den : Int)
  simp only [Q'.mul_den_cast, Q'.mkPos_den]
  have key : 4 * (k + 4) * 1 * 5 ≤ 4 * (5 * (k + 4)) := by simp +arith
  exact_mod_cast key

theorem seg_le (m : Nat) (hm : 0 < m) : ∀ r, NQ.toQ (seg m r) ≤ Q'.mkPos (r : Int) 1 (by decide)
  | 0 => Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_lit 0 1 Nat.one_pos)) (by decide)
  | r + 1 => by
    have hd : 0 < m + r := Nat.lt_of_lt_of_le hm (Nat.le_add_right _ _)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_add _ ⟨1, m + r⟩ (seg_d_pos m hm r) hd)) ?_
    refine Q'.le_trans' _ _ _ (add_le_add2 (seg_le m hm r) (Q'.le_of_eqv (toQ_lit 1 (m + r) hd))) ?_
    show ((r : Int) * ((Q'.mkPos 1 (m + r) hd).den : Int) + 1 * ((Q'.mkPos (r : Int) 1 _).den : Int))
        * ((Q'.mkPos ((r + 1 : Nat) : Int) 1 _).den : Int)
      ≤ ((r + 1 : Nat) : Int) * ((Q'.mkPos (r : Int) 1 _ + Q'.mkPos 1 (m + r) hd).den : Int)
    rw [Q'.add_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
    have key : (r * (m + r) + 1 * 1) * 1 ≤ (r + 1) * (1 * (m + r)) := by
      rw [Nat.mul_one, Nat.one_mul, Nat.one_mul, Nat.add_mul r 1 (m + r), Nat.one_mul]
      exact Nat.add_le_add_left hd _
    exact_mod_cast key

theorem Zq_le (k : Nat) : Zq k ≤ Q'.mkPos 16 1 (by decide) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_mul _ _ (by decide) (seg_d_pos _ (Nat.succ_pos _) 17)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (seg_le (k + 4) (Nat.succ_pos _) 17)
      (toQ_nonneg _)) (by decide))

/-! ## `D(c, m) ≤ 2m` for `m ≥ 60`, `0 ≤ c ≤ 62/100` -/

theorem c62h5 (k : Nat) : Q'.mkPos 62 100 (by decide) * Q'.mkPos ((4 * (k + 3) + 11 : Nat) : Int) 5 (by decide)
    ≤ Q'.mkPos ((k + 6 : Nat) : Int) 2 (by decide) := by
  show Q'.le _ _
  unfold Q'.le
  simp only [mul_num', Q'.mkPos_num]
  simp only [Q'.mul_den_cast]
  simp only [Q'.mkPos_den]
  norm_cast
  simp +arith

theorem closedD (k : Nat) (h56 : 56 ≤ k) :
    (((Q'.mkPos ((k + 4 : Nat) : Int) 1 (by decide) + Q'.mkPos 5 1 (by decide))
      + Q'.mkPos ((k + 6 : Nat) : Int) 2 (by decide)) + Q'.mkPos 1 3 (by decide))
      + Q'.mkPos 16 1 (by decide) ≤ Q'.mkPos ((2 * (k + 4) : Nat) : Int) 1 (by decide) := by
  show Q'.le _ _
  unfold Q'.le
  simp only [add_num', Q'.mkPos_num]
  simp only [Q'.add_den_cast]
  simp only [Q'.mkPos_den]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h56
  norm_cast
  simp +arith

theorem D_le (c : Q') (k : Nat) (hk56 : 56 ≤ k) (hc0 : (0 : Q') ≤ c) (hc : c ≤ Q'.mkPos 62 100 (by decide)) :
    DQ c k ≤ Q'.mkPos ((2 * (k + 4) : Nat) : Int) 1 (by decide) := by
  have h62 : (0 : Q') ≤ Q'.mkPos 62 100 (by decide) := by decide
  have hcc : c * c ≤ Q'.mkPos 62 100 (by decide) * Q'.mkPos 62 100 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hc hc0) (Q'.mul_le_mul_of_nonneg_left _ _ _ hc h62)
  have hA : Ak k ≤ Q'.mkPos ((k + 4 : Nat) : Int) 1 (by decide) + Q'.mkPos 5 1 (by decide) :=
    add_le_add2 (Q'.le_of_eqv (toQ_lit _ 1 Nat.one_pos))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (toQ_lit 9989 2000 (by decide))) (by decide))
  have hh : hk k ≤ Q'.mkPos ((4 * (k + 3) + 11 : Nat) : Int) 5 (by decide) := harm45 (k + 3)
  refine Q'.le_trans' _ _ _ ?_ (closedD k hk56)
  exact add_le_add2 (add_le_add2 (add_le_add2 hA
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hh hc0)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hc
        ((Q'.zero_le_iff_num_nonneg _).mpr (Int.natCast_nonneg _))) (c62h5 k))))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (W_le k) (Q'.mul_nonneg _ _ hc0 hc0))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hcc (by decide)) (by decide)))) (Zq_le k)

/-! ## `κ`-Lipschitz bound at the Lean schedule: `D(κ'_n) − D(κ'_{n'}) ≤ 2^{-n}` -/

/-- `e_n = 2^{-n}` at `n = k+14`. -/
def eN (k : Nat) : Q' := Q'.mkPos 1 (2 ^ (k + 14)) (Nat.two_pow_pos _)

theorem eN_nonneg (k : Nat) : (0 : Q') ≤ eN k :=
  (Q'.zero_le_iff_num_nonneg _).mpr (show (0 : Int) ≤ 1 by decide)

theorem lcap_hb (k : Nat) :
    lcap (k + 14) * Q'.mkPos ((k + 8 : Nat) : Int) 1 (by decide) ≤ eN k := by
  unfold lcap eN
  show ((1 : Int) * ((k + 8 : Nat) : Int)) * ((Q'.mkPos 1 (2 ^ (k + 14)) _).den : Int)
    ≤ 1 * ((Q'.mkPos 1 ((k + 14 + 1) * 2 ^ (k + 14)) _ * Q'.mkPos ((k + 8 : Nat) : Int) 1 _).den : Int)
  simp only [Q'.mul_den_cast, Q'.mkPos_den]
  have key : 1 * (k + 8) * 2 ^ (k + 14) ≤ 1 * ((k + 14 + 1) * 2 ^ (k + 14) * 1) := by
    rw [Nat.one_mul, Nat.one_mul, Nat.mul_one]
    exact Nat.mul_le_mul_right _ (by simp +arith)
  exact_mod_cast key

theorem hb_one (k : Nat) : Q'.mkPos ((k + 7 : Nat) : Int) 1 (by decide) + Q'.mkPos 1 1 (by decide)
    ≤ Q'.mkPos ((k + 8 : Nat) : Int) 1 (by decide) := by
  show Q'.le _ _
  unfold Q'.le
  simp only [add_num', Q'.mkPos_num]
  simp only [Q'.add_den_cast]
  simp only [Q'.mkPos_den]
  norm_cast
  simp +arith

theorem c9_le (x : Q') (hx : (0 : Q') ≤ x) : Q'.mkPos 9 10 (by decide) * x ≤ x :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : Q'.mkPos 9 10 (by decide) ≤ 1) hx)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

theorem dD_tail (k : Nat) (δ : Q') (hδ : (0 : Q') ≤ δ) :
    δ * hk k + (δ * Q'.mkPos 31 25 (by decide)) * W k ≤ δ * Q'.mkPos ((k + 8 : Nat) : Int) 1 (by decide) := by
  have h1 : δ * hk k ≤ δ * Q'.mkPos ((k + 7 : Nat) : Int) 1 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (harm_le (k + 7)) hδ
  have h2 : (δ * Q'.mkPos 31 25 (by decide)) * W k ≤ δ * Q'.mkPos 1 1 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (W_le k) (Q'.mul_nonneg _ _ hδ (by decide)))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (by decide) hδ))
  exact Q'.le_trans' _ _ _ (add_le_add2 h1 h2) (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (hb_one k) hδ))

/-- `D(κ'_{n'}, m) ≤ D(κ'_n, m) ≤ D(κ'_{n'}, m) + 2^{-n}` (all `k, j`; `n = k+14`, `n' = n+j`). -/
theorem dD_lean (k j : Nat) :
    DQ (kn (k + 14 + j)) k ≤ DQ (kQ k) k ∧ DQ (kQ k) k ≤ DQ (kn (k + 14 + j)) k + eN k := by
  have hF := lemmaF_ii k j
  have hku : kn (k + 14 + j) ≤ Q'.mkPos 62 100 (by decide) := by
    have h := kQ_le (k + j); unfold kQ at h; rw [ix] at h; exact h
  have hc : (0 : Q') ≤ lcap (k + 14) := (Q'.zero_le_iff_num_nonneg _).mpr (show (0 : Int) ≤ 1 by decide)
  have hδ : (0 : Q') ≤ Q'.mkPos 9 10 (by decide) * lcap (k + 14) := Q'.mul_nonneg _ _ (by decide) hc
  have hG := dD_gen (Ak k) (hk k) (W k) (Zq k) (kQ k) (kn (k + 14 + j)) _ _ (Q'.mkPos 31 25 (by decide))
    (toQ_nonneg _) hδ (toQ_nonneg _) (W_nonneg k) hF.1 hF.2 (kQ_le k) hku (by decide)
  refine ⟨hG.1, Q'.le_trans' _ _ _ hG.2 (Q'.add_le_add_left _ _ _
    (Q'.le_trans' _ _ _ (dD_tail k _ hδ) ?_))⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (lcap_hb k) (by decide)) (c9_le _ (eN_nonneg k)))

end YMGap.RG.Robust3LemmaFiii
