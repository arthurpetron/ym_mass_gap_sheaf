import YMGap.RG.Robust3UndershootAfSchedule

/-!
# Robust3: series brackets on the exact partial sums `L_n`, `S_n`, `P_n`

Rational-interval lemmas on the exact Robust3 partial sums (`lnS`, `piST`, `pUp` from
`Robust3UndershootAfSchedule`, used verbatim), via a semantic bridge `NQ.toQ (NQ.red a b) ≃ a/b`.

* `ln2_partial_bracket n m`: `L_n ≤ L_{n+m} ≤ L_n + 1/((n+1)·2^n)`.
* `pi2_partial_bracket n m`: `S_{n+m} ≤ V_n`, `S_n + t_{n+1} ≤ S_{n+1+m}`,
  `V_n ≤ (S_n + t_{n+1}) + t_{n+1}/3`, where `V_n = S_n + (4/3)t_{n+1}` and `P_n ≃ 18·V_n` (`pUp_eqv`).
* `t_le_pow4 n`: `t_{n+2} ≤ 4^{-(n+2)}` (i.e. `t_{n+1} ≤ 4^{-n-1}` for `n ≥ 1`).

NAMED ASSUMPTION (NOT formalised; classical identities, not proved here and not connected to the
repo's `CReal` `log2`/`pi`): `SERIES_LIMITS_OPEN` — `ln 2 = lim_m L_m` and `π²/18 = lim_m S_m`.
Under it, letting `m → ∞` gives `0 ≤ ln2 − L_n ≤ 2^{-n}/(n+1)` and `0 ≤ P_n − π² ≤ 6·t_{n+1} ≤ 6·4^{-n-1}`
(`n ≥ 1`). Only the rational partial-sum statements below are proved.
-/

namespace YMGap.RG.Robust3SeriesBrackets
open YMGap.Constructive
open YMGap.RG.Robust3UndershootAfSchedule

/-! ## Semantics of `NQ` -/

theorem red_spec (a b : Nat) : (NQ.red a b).n * b = a * (NQ.red a b).d := by
  show a / Nat.gcd a b * b = a * (b / Nat.gcd a b)
  rcases Nat.eq_zero_or_pos (Nat.gcd a b) with h0 | hpos
  · rw [h0, Nat.div_zero, Nat.div_zero, Nat.zero_mul, Nat.mul_zero]
  · obtain ⟨a', ha⟩ := Nat.gcd_dvd_left a b
    obtain ⟨b', hb⟩ := Nat.gcd_dvd_right a b
    generalize Nat.gcd a b = g at ha hb hpos ⊢
    subst ha; subst hb
    rw [Nat.mul_div_cancel_left a' hpos, Nat.mul_div_cancel_left b' hpos, Nat.mul_left_comm,
      Nat.mul_assoc]

theorem red_d_pos (a : Nat) {b : Nat} (hb : 0 < b) : 0 < (NQ.red a b).d :=
  Nat.div_pos (Nat.gcd_le_right a hb) (Nat.gcd_pos_of_pos_right a hb)

theorem toQ_den (x : NQ) (h : 0 < x.d) : (NQ.toQ x).den = x.d := Nat.sub_add_cancel h

theorem toQ_num (x : NQ) : (NQ.toQ x).num = (x.n : Int) := rfl

theorem toQ_nonneg (x : NQ) : (0 : Q') ≤ NQ.toQ x :=
  (Q'.zero_le_iff_num_nonneg _).mpr (Int.natCast_nonneg x.n)

theorem toQ_red (a b : Nat) (hb : 0 < b) :
    (NQ.toQ (NQ.red a b)).eqv (Q'.mkPos (a : Int) b hb) := by
  unfold Q'.eqv
  rw [Q'.mkPos_den, Q'.mkPos_num, toQ_den _ (red_d_pos a hb), toQ_num]
  exact_mod_cast red_spec a b

theorem toQ_lit (a b : Nat) (hb : 0 < b) : (NQ.toQ ⟨a, b⟩).eqv (Q'.mkPos (a : Int) b hb) := by
  unfold Q'.eqv
  rw [Q'.mkPos_den, Q'.mkPos_num, toQ_den ⟨a, b⟩ hb, toQ_num]

theorem toQ_add (x y : NQ) (hx : 0 < x.d) (hy : 0 < y.d) :
    (NQ.toQ (NQ.add x y)).eqv (NQ.toQ x + NQ.toQ y) := by
  have hb : 0 < x.d * y.d := Nat.mul_pos hx hy
  refine Q'.eqv_trans _ _ _ (toQ_red (x.n * y.d + y.n * x.d) (x.d * y.d) hb) ?_
  unfold Q'.eqv
  rw [Q'.add_den_cast, Q'.mkPos_den, Q'.mkPos_num]
  show _ = ((NQ.toQ x).num * ((NQ.toQ y).den : Int) + (NQ.toQ y).num * ((NQ.toQ x).den : Int)) * _
  rw [toQ_den x hx, toQ_den y hy, toQ_num, toQ_num]
  norm_cast

theorem toQ_mul (x y : NQ) (hx : 0 < x.d) (hy : 0 < y.d) :
    (NQ.toQ (NQ.mul x y)).eqv (NQ.toQ x * NQ.toQ y) := by
  have hb : 0 < x.d * y.d := Nat.mul_pos hx hy
  refine Q'.eqv_trans _ _ _ (toQ_red (x.n * y.n) (x.d * y.d) hb) ?_
  unfold Q'.eqv
  rw [Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_num]
  show _ = ((NQ.toQ x).num * (NQ.toQ y).num) * _
  rw [toQ_den x hx, toQ_den y hy, toQ_num, toQ_num]
  norm_cast

/-! ## `L_n = Σ_{k=1}^n 1/(k·2^k)` -/

theorem pow_pos' (n : Nat) : 0 < (n + 1) * 2 ^ n := Nat.mul_pos (Nat.succ_pos n) (Nat.two_pow_pos n)

theorem lnS_d_pos : ∀ n, 0 < (lnS n).d
  | 0 => by decide
  | k + 1 => by
    show 0 < (NQ.red _ ((lnS k).d * ((k + 1) * 2 ^ (k + 1)))).d
    exact red_d_pos _ (Nat.mul_pos (lnS_d_pos k)
      (Nat.mul_pos (Nat.succ_pos k) (Nat.two_pow_pos (k + 1))))

/-- `L_n` as a `Q'`. -/
def LQ (n : Nat) : Q' := NQ.toQ (lnS n)
/-- The term `1/((n+1)·2^(n+1))`. -/
def lterm (n : Nat) : Q' :=
  Q'.mkPos 1 ((n + 1) * 2 ^ (n + 1)) (Nat.mul_pos (Nat.succ_pos n) (Nat.two_pow_pos (n + 1)))
/-- Tail cap `1/((n+1)·2^n)`. -/
def lcap (n : Nat) : Q' := Q'.mkPos 1 ((n + 1) * 2 ^ n) (pow_pos' n)
/-- Upper sequence `U_n = L_n + 1/((n+1)·2^n)`. -/
def LU (n : Nat) : Q' := LQ n + lcap n

theorem LQ_succ (k : Nat) : (LQ (k + 1)).eqv (LQ k + lterm k) := by
  have hp : 0 < (k + 1) * 2 ^ (k + 1) := Nat.mul_pos (Nat.succ_pos k) (Nat.two_pow_pos (k + 1))
  exact Q'.eqv_trans _ _ _ (toQ_add (lnS k) ⟨1, (k + 1) * 2 ^ (k + 1)⟩ (lnS_d_pos k) hp)
    (Q'.add_eqv_congr_left _ _ _ (toQ_lit 1 _ hp))

theorem LQ_mono (k : Nat) : LQ k ≤ LQ (k + 1) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (LQ k) (lterm k) ((Q'.zero_le_iff_num_nonneg _).mpr (show (0 : Int) ≤ 1 by decide)))
    (Q'.ge_of_eqv (LQ_succ k))

theorem lcap_step (n : Nat) : lterm n + lcap (n + 1) ≤ lcap n := by
  unfold lterm lcap
  show (1 * ((Q'.mkPos 1 ((n + 1 + 1) * 2 ^ (n + 1)) (pow_pos' (n + 1))).den : Int)
      + 1 * ((Q'.mkPos 1 ((n + 1) * 2 ^ (n + 1)) _).den : Int))
      * ((Q'.mkPos 1 ((n + 1) * 2 ^ n) (pow_pos' n)).den : Int)
    ≤ 1 * ((Q'.mkPos 1 ((n + 1) * 2 ^ (n + 1)) _ + Q'.mkPos 1 ((n + 1 + 1) * 2 ^ (n + 1))
      (pow_pos' (n + 1))).den : Int)
  rw [Q'.add_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den, Int.one_mul, Int.one_mul,
    Int.one_mul]
  have key : ((n + 1 + 1) * 2 ^ (n + 1) + (n + 1) * 2 ^ (n + 1)) * ((n + 1) * 2 ^ n)
      ≤ ((n + 1) * 2 ^ (n + 1)) * ((n + 1 + 1) * 2 ^ (n + 1)) := by
    rw [Nat.pow_succ]
    generalize 2 ^ n = P
    calc ((n + 1 + 1) * (P * 2) + (n + 1) * (P * 2)) * ((n + 1) * P)
        = ((n + 1 + 1) + (n + 1)) * ((P * 2) * ((n + 1) * P)) := by rw [← Nat.add_mul, Nat.mul_assoc]
      _ ≤ ((n + 1 + 1) + (n + 1 + 1)) * ((P * 2) * ((n + 1) * P)) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.le_succ _) _)
      _ = ((n + 1) * (P * 2)) * ((n + 1 + 1) * (P * 2)) := by rw [← Nat.mul_two]; ac_rfl
  exact_mod_cast key

theorem LU_anti (n : Nat) : LU (n + 1) ≤ LU n :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (LQ_succ n))
      (Q'.add_assoc_eqv _ _ _)))
    (Q'.add_le_add_left _ _ _ (lcap_step n))

theorem LQ_le_LU (n : Nat) : LQ n ≤ LU n :=
  Q'.add_le_self_of_nonneg _ _ ((Q'.zero_le_iff_num_nonneg _).mpr (show (0 : Int) ≤ 1 by decide))

theorem L_chain (n : Nat) : ∀ m, LQ n ≤ LQ (n + m) ∧ LU (n + m) ≤ LU n
  | 0 => ⟨Q'.le_refl' _, Q'.le_refl' _⟩
  | m + 1 => ⟨Q'.le_trans' _ _ _ (L_chain n m).1 (LQ_mono (n + m)),
      Q'.le_trans' _ _ _ (LU_anti (n + m)) (L_chain n m).2⟩

/-- **ln 2 bracket on partial sums**: `L_n ≤ L_{n+m} ≤ L_n + 1/((n+1)·2^n)` for all `n, m`. -/
theorem ln2_partial_bracket (n m : Nat) : LQ n ≤ LQ (n + m) ∧ LQ (n + m) ≤ LQ n + lcap n :=
  ⟨(L_chain n m).1, Q'.le_trans' _ _ _ (LQ_le_LU (n + m)) (L_chain n m).2⟩

/-! ## `S_n = Σ_{k≤n} t_k`, `t_{n+1}`, `P_n = 18·(S_n + (4/3)t_{n+1})` -/

theorem piST_d_pos : ∀ n, 0 < (piST n).1.d ∧ 0 < (piST n).2.d
  | 0 => ⟨by decide, by decide⟩
  | k + 1 => by
    have ih := piST_d_pos k
    refine ⟨?_, ?_⟩
    · show 0 < (NQ.red _ ((piST k).1.d * (piST k).2.d)).d
      exact red_d_pos _ (Nat.mul_pos ih.1 ih.2)
    · show 0 < (NQ.red _ ((piST k).2.d * ((2 * k + 3) * (2 * k + 4)))).d
      exact red_d_pos _ (Nat.mul_pos ih.2 (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)))

/-- `S_n`. -/
def SQ (n : Nat) : Q' := NQ.toQ (piST n).1
/-- `t_{n+1}`. -/
def TQ (n : Nat) : Q' := NQ.toQ (piST n).2
/-- Ratio `t_{n+2}/t_{n+1} = (n+1)²/((2n+3)(2n+4))`. -/
def RQ (n : Nat) : Q' := NQ.toQ ⟨(n + 1) * (n + 1), (2 * n + 3) * (2 * n + 4)⟩
/-- `V_n = S_n + (4/3)·t_{n+1} = P_n/18`. -/
def VQ (n : Nat) : Q' := SQ n + Q'.mkPos 4 3 (by decide) * TQ n

theorem SQ_succ (k : Nat) : (SQ (k + 1)).eqv (SQ k + TQ k) :=
  toQ_add _ _ (piST_d_pos k).1 (piST_d_pos k).2

theorem TQ_succ (k : Nat) : (TQ (k + 1)).eqv (TQ k * RQ k) :=
  toQ_mul _ ⟨(k + 1) * (k + 1), (2 * k + 3) * (2 * k + 4)⟩ (piST_d_pos k).2
    (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))

theorem RQ_le (k : Nat) : RQ k ≤ Q'.mkPos 1 4 (by decide) := by
  unfold RQ
  show ((((k + 1) * (k + 1) : Nat) : Int)) * ((Q'.mkPos 1 4 _).den : Int)
    ≤ 1 * ((NQ.toQ ⟨(k + 1) * (k + 1), (2 * k + 3) * (2 * k + 4)⟩).den : Int)
  rw [Q'.mkPos_den, toQ_den _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)), Int.one_mul]
  have e : (k + 1) * 2 = 2 * k + 2 := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  have key : (k + 1) * (k + 1) * 4 ≤ (2 * k + 3) * (2 * k + 4) :=
    calc (k + 1) * (k + 1) * 4 = ((k + 1) * 2) * ((k + 1) * 2) := by
          show (k + 1) * (k + 1) * (2 * 2) = _; ac_rfl
      _ ≤ (2 * k + 3) * (2 * k + 4) := by
          rw [e]; exact Nat.mul_le_mul (Nat.le_succ _) (Nat.add_le_add_left (by decide) _)
  exact_mod_cast key

/-- Core algebra: `t + (4/3)(t·r) ≤ (4/3)t` for `t ≥ 0`, `r ≤ 1/4`. -/
theorem key_V (t r : Q') (ht : (0 : Q') ≤ t) (hr : r ≤ Q'.mkPos 1 4 (by decide)) :
    t + Q'.mkPos 4 3 (by decide) * (t * r) ≤ Q'.mkPos 4 3 (by decide) * t := by
  have hp : (0 : Int) ≤ t.num := (Q'.zero_le_iff_num_nonneg _).mp ht
  have hr' : r.num * 4 ≤ 1 * (r.den : Int) := by
    have h : r.num * ((Q'.mkPos 1 4 (by decide)).den : Int)
        ≤ (Q'.mkPos 1 4 (by decide)).num * (r.den : Int) := hr
    rw [Q'.mkPos_den] at h; exact h
  show (t.num * ((Q'.mkPos 4 3 _ * (t * r)).den : Int) + (4 * (t.num * r.num)) * (t.den : Int))
      * ((Q'.mkPos 4 3 _ * t).den : Int)
    ≤ (4 * t.num) * ((t + Q'.mkPos 4 3 _ * (t * r)).den : Int)
  simp only [Q'.add_den_cast, Q'.mul_den_cast, Q'.mkPos_den]
  generalize t.num = p at hp ⊢
  have hq0 : (0 : Int) ≤ (t.den : Int) := Int.natCast_nonneg _
  generalize (t.den : Int) = q at hq0 ⊢
  generalize r.num = u at hr' ⊢
  generalize (r.den : Int) = v at hr' ⊢
  show (p * (3 * (q * v)) + 4 * (p * u) * q) * (3 * q) ≤ 4 * p * (q * (3 * (q * v)))
  have e1 : (p * (3 * (q * v)) + 4 * (p * u) * q) * (3 * q) = (3 * p * q * q) * (3 * v + 4 * u) := by
    simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e2 : 4 * p * (q * (3 * (q * v))) = (3 * p * q * q) * (4 * v) := by ac_rfl
  have hpq : (0 : Int) ≤ 3 * p * q * q :=
    Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by decide) hp) hq0) hq0
  rw [e1, e2]
  apply Int.mul_le_mul_of_nonneg_left _ hpq
  have e3 : (4 : Int) * v = 3 * v + v := by
    rw [show (4 : Int) = 3 + 1 by decide, Int.add_mul, Int.one_mul]
  rw [e3]
  apply Int.add_le_add_left
  rw [Int.mul_comm]; rw [Int.one_mul] at hr'; exact hr'

theorem four_thirds (t : Q') :
    (Q'.mkPos 4 3 (by decide) * t).eqv (t + Q'.mkPos 1 3 (by decide) * t) := by
  unfold Q'.eqv
  show (4 * t.num) * ((t + Q'.mkPos 1 3 _ * t).den : Int)
    = (t.num * ((Q'.mkPos 1 3 _ * t).den : Int) + (1 * t.num) * (t.den : Int))
      * ((Q'.mkPos 4 3 _ * t).den : Int)
  simp only [Q'.add_den_cast, Q'.mul_den_cast, Q'.mkPos_den]
  generalize t.num = p
  generalize (t.den : Int) = q
  show 4 * p * (q * (3 * q)) = (p * (3 * q) + 1 * p * q) * (3 * q)
  have e4 : (4 : Int) * p = 3 * p + p := by
    rw [show (4 : Int) = 3 + 1 by decide, Int.add_mul, Int.one_mul]
  rw [Int.one_mul, Int.add_mul, e4, Int.add_mul]
  congr 1 <;> ac_rfl

theorem pUp_eqv (n : Nat) : (NQ.toQ (pUp n)).eqv (Q'.mkPos 18 1 (by decide) * VQ n) := by
  have h1 := (piST_d_pos n).1
  have h2 := (piST_d_pos n).2
  have h43 : 0 < (NQ.mul ⟨4, 3⟩ (piST n).2).d := red_d_pos _ (Nat.mul_pos (by decide) h2)
  have hY : 0 < (NQ.add (piST n).1 (NQ.mul ⟨4, 3⟩ (piST n).2)).d :=
    red_d_pos _ (Nat.mul_pos h1 h43)
  show (NQ.toQ (NQ.mul ⟨18, 1⟩ (NQ.add (piST n).1 (NQ.mul ⟨4, 3⟩ (piST n).2)))).eqv _
  refine Q'.eqv_trans _ _ _ (toQ_mul ⟨18, 1⟩ _ (by decide) hY) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (toQ_lit 18 1 (by decide))) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ (toQ_add _ _ h1 h43) ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  exact Q'.eqv_trans _ _ _ (toQ_mul ⟨4, 3⟩ _ (by decide) h2)
    (Q'.mul_eqv_congr_right _ _ _ (toQ_lit 4 3 (by decide)))

theorem VQ_anti (n : Nat) : VQ (n + 1) ≤ VQ n :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (SQ_succ n))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ (TQ_succ n))))
      (Q'.add_assoc_eqv _ _ _)))
    (Q'.add_le_add_left _ _ _ (key_V _ _ (toQ_nonneg _) (RQ_le n)))

theorem SQ_le_VQ (n : Nat) : SQ n ≤ VQ n :=
  Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) (toQ_nonneg _))

theorem SQ_mono (k : Nat) : SQ k ≤ SQ (k + 1) :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (toQ_nonneg _)) (Q'.ge_of_eqv (SQ_succ k))

theorem S_chain (n : Nat) : ∀ m, SQ n ≤ SQ (n + m) ∧ VQ (n + m) ≤ VQ n
  | 0 => ⟨Q'.le_refl' _, Q'.le_refl' _⟩
  | m + 1 => ⟨Q'.le_trans' _ _ _ (S_chain n m).1 (SQ_mono (n + m)),
      Q'.le_trans' _ _ _ (VQ_anti (n + m)) (S_chain n m).2⟩

/-- **π²/18 bracket on partial sums** (`V_n = P_n/18`): for all `n, m`,
`S_{n+m} ≤ V_n`, `S_n + t_{n+1} ≤ S_{n+1+m}`, and `V_n ≤ (S_n + t_{n+1}) + t_{n+1}/3`. -/
theorem pi2_partial_bracket (n m : Nat) :
    SQ (n + m) ≤ VQ n ∧ SQ n + TQ n ≤ SQ (n + 1 + m)
      ∧ VQ n ≤ (SQ n + TQ n) + Q'.mkPos 1 3 (by decide) * TQ n :=
  ⟨Q'.le_trans' _ _ _ (SQ_le_VQ (n + m)) (S_chain n m).2,
   Q'.le_trans' _ _ _ (Q'.ge_of_eqv (SQ_succ n)) (S_chain (n + 1) m).1,
   Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (four_thirds _))
     (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))⟩

/-- `18·S_{n+m} ≤ P_n` (all `n, m`). -/
theorem pUp_lower (n m : Nat) : Q'.mkPos 18 1 (by decide) * SQ (n + m) ≤ NQ.toQ (pUp n) :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (pi2_partial_bracket n m).1 (by decide))
    (Q'.ge_of_eqv (pUp_eqv n))

/-- `P_n ≤ 18·(S_{n+1+m} + t_{n+1}/3)` (all `n, m`). -/
theorem pUp_upper (n m : Nat) :
    NQ.toQ (pUp n) ≤ Q'.mkPos 18 1 (by decide) * (SQ (n + 1 + m) + Q'.mkPos 1 3 (by decide) * TQ n) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (pUp_eqv n))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ (pi2_partial_bracket n m).2.2
        (Q'.add_le_add_right _ _ _ (pi2_partial_bracket n m).2.1)) (by decide))

theorem pow4_pos (n : Nat) : 0 < 4 ^ n := Nat.pow_pos (by decide)

theorem pow4_eqv (k : Nat) :
    (Q'.mkPos 1 (4 ^ (k + 2)) (pow4_pos _) * Q'.mkPos 1 4 (by decide)).eqv
      (Q'.mkPos 1 (4 ^ (k + 3)) (pow4_pos _)) := by
  unfold Q'.eqv
  rw [Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
  show (1 * 1 : Int) * ((4 ^ (k + 3) : Nat) : Int) = 1 * (((4 ^ (k + 2) : Nat) : Int) * ((4 : Nat) : Int))
  rw [← Int.natCast_mul, ← Nat.pow_succ]
  simp only [Int.one_mul]

/-- `t_{n+2} ≤ 4^{-(n+2)}` (i.e. `t_{n+1} ≤ 4^{-n-1}` for `n ≥ 1`; false at `n = 0`, `t_1 = 1/2`). -/
theorem t_le_pow4 : ∀ n, TQ (n + 1) ≤ Q'.mkPos 1 (4 ^ (n + 2)) (pow4_pos _)
  | 0 => by decide
  | k + 1 =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (TQ_succ (k + 1)))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (RQ_le (k + 1)) (toQ_nonneg _))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (t_le_pow4 k) (by decide))
          (Q'.le_of_eqv (pow4_eqv k))))

end YMGap.RG.Robust3SeriesBrackets
