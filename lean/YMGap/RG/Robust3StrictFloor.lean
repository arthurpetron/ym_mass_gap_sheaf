import YMGap.RG.Robust3SeriesBrackets

/-!
# Robust3: strict floor `E_k > (k+1)/4` for the exact closed form, all `k`

Structural proof (no numerics beyond closed `decide` checks at `n = 1`) that the exact Robust3 closed form
`ecomp k = D·B` satisfies `(k+1)/4 < ecomp k` for every `k`, hence the floor in `r3Raw` is never active
(`r3Raw_eq`) and the envelope satisfies `(k+1)/4 < r3E k` (`r3Floor_lt_r3E`).

Route: `L_{k+14} ≥ L_1 = 1/2`, `P_{k+14} ≤ P_1 = 10` (from `Robust3SeriesBrackets`), so
`B = (22/3)L/P ≥ 11/30`; `D ≥ m = k+4` (all other summands are nonnegative); and
`(k+4)·11/30 > (k+1)/4`.

Not proved here: monotonicity of `ecomp` itself (the running-max envelope `r3E` is still what makes
`r3E_mono` structural); that remains analysis/numerics (task2h (E) + arb), as recorded in the audits.
-/

namespace YMGap.RG.Robust3StrictFloor
open YMGap.Constructive
open YMGap.RG.Robust3UndershootAfSchedule
open YMGap.RG.Robust3SeriesBrackets

theorem lt_of_lt_of_le' {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hb : (0 : Int) < (b.den : Int) := by exact_mod_cast Q'.den_pos b
  have hc : (0 : Int) < (c.den : Int) := by exact_mod_cast Q'.den_pos c
  have ha : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  refine Int.lt_of_mul_lt_mul_right (a := (b.den : Int)) ?_ (Int.le_of_lt hb)
  calc a.num * (c.den : Int) * (b.den : Int) = (a.num * b.den) * c.den := by ac_rfl
    _ < (b.num * a.den) * c.den := Int.mul_lt_mul_of_pos_right e1 hc
    _ = (b.num * c.den) * a.den := by ac_rfl
    _ ≤ (c.num * b.den) * a.den := Int.mul_le_mul_of_nonneg_right e2 ha
    _ = c.num * (a.den : Int) * (b.den : Int) := by ac_rfl

theorem add_d_pos {x y : NQ} (hx : 0 < x.d) (hy : 0 < y.d) : 0 < (NQ.add x y).d :=
  red_d_pos _ (Nat.mul_pos hx hy)
theorem mul_d_pos {x y : NQ} (hx : 0 < x.d) (hy : 0 < y.d) : 0 < (NQ.mul x y).d :=
  red_d_pos _ (Nat.mul_pos hx hy)
theorem div_d_pos {x y : NQ} (hx : 0 < x.d) (hy : 0 < y.n) : 0 < (NQ.div x y).d :=
  red_d_pos _ (Nat.mul_pos hx hy)

theorem harm_d_pos : ∀ m, 0 < (harm m).d
  | 0 => by decide
  | m + 1 => add_d_pos (harm_d_pos m) (Nat.succ_pos m)

theorem seg_d_pos (m : Nat) (hm : 0 < m) : ∀ r, 0 < (seg m r).d
  | 0 => Nat.one_pos
  | r + 1 => add_d_pos (seg_d_pos m hm r) (Nat.lt_of_lt_of_le hm (Nat.le_add_right m r))

theorem le_add {x y : NQ} (hx : 0 < x.d) (hy : 0 < y.d) : NQ.toQ x ≤ NQ.toQ (NQ.add x y) :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (toQ_nonneg y)) (Q'.ge_of_eqv (toQ_add x y hx hy))

theorem n_pos_of_lower {x : NQ} (hd : 0 < x.d) {a : Nat} {b : Nat} (hb : 0 < b) (ha : 0 < a)
    (h : Q'.mkPos (a : Int) b hb ≤ NQ.toQ x) : 0 < x.n := by
  have h' : (a : Int) * ((NQ.toQ x).den : Int) ≤ (x.n : Int) * ((Q'.mkPos (a : Int) b hb).den : Int) := h
  rw [Q'.mkPos_den, toQ_den x hd] at h'
  have hN : a * x.d ≤ x.n * b := by exact_mod_cast h'
  refine Nat.pos_of_ne_zero (fun h0 => ?_)
  rw [h0, Nat.zero_mul] at hN
  exact Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le (Nat.mul_pos ha hd) hN)

/-- `B = X/P ≥ 11/30` from `X ≥ 11/3`, `P ≤ 10`. -/
theorem div_lower (X P : NQ) (hXd : 0 < X.d) (hPd : 0 < P.d) (hPn : 0 < P.n)
    (hX : Q'.mkPos 11 3 (by decide) ≤ NQ.toQ X) (hP : NQ.toQ P ≤ Q'.mkPos 10 1 (by decide)) :
    Q'.mkPos 11 30 (by decide) ≤ NQ.toQ (NQ.div X P) := by
  have hb : 0 < X.d * P.n := Nat.mul_pos hXd hPn
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (toQ_red (X.n * P.d) (X.d * P.n) hb))
  have hX' : (11 : Int) * ((NQ.toQ X).den : Int) ≤ (X.n : Int) * ((Q'.mkPos 11 3 (by decide)).den : Int) := hX
  have hP' : (P.n : Int) * ((Q'.mkPos 10 1 (by decide)).den : Int) ≤ 10 * ((NQ.toQ P).den : Int) := hP
  rw [Q'.mkPos_den, toQ_den X hXd] at hX'
  rw [Q'.mkPos_den, toQ_den P hPd] at hP'
  have hXN : 11 * X.d ≤ X.n * 3 := by exact_mod_cast hX'
  have hPN : P.n * 1 ≤ 10 * P.d := by exact_mod_cast hP'
  show (11 : Int) * ((Q'.mkPos ((X.n * P.d : Nat) : Int) (X.d * P.n) hb).den : Int)
    ≤ ((X.n * P.d : Nat) : Int) * ((Q'.mkPos 11 30 (by decide)).den : Int)
  rw [Q'.mkPos_den, Q'.mkPos_den]
  have key : 11 * (X.d * P.n) ≤ (X.n * P.d) * 30 :=
    calc 11 * (X.d * P.n) = (11 * X.d) * P.n := (Nat.mul_assoc _ _ _).symm
      _ ≤ (X.n * 3) * P.n := Nat.mul_le_mul_right _ hXN
      _ = (X.n * 3) * (P.n * 1) := by rw [Nat.mul_one]
      _ ≤ (X.n * 3) * (10 * P.d) := Nat.mul_le_mul_left _ hPN
      _ = (X.n * P.d) * 30 := by show _ = (X.n * P.d) * (3 * 10); ac_rfl
  exact_mod_cast key

theorem D_lower (A c X1 X2 Z : NQ) (hA : 0 < A.d) (hc : 0 < c.d) (h1 : 0 < X1.d) (h2 : 0 < X2.d)
    (hZ : 0 < Z.d) :
    NQ.toQ A ≤ NQ.toQ (NQ.add (NQ.add (NQ.add (NQ.add A c) X1) X2) Z) :=
  Q'.le_trans' _ _ _ (le_add hA hc) (Q'.le_trans' _ _ _ (le_add (add_d_pos hA hc) h1)
    (Q'.le_trans' _ _ _ (le_add (add_d_pos (add_d_pos hA hc) h1) h2)
      (le_add (add_d_pos (add_d_pos (add_d_pos hA hc) h1) h2) hZ)))

theorem idx (k : Nat) : 1 + (k + 13) = k + 14 := Nat.add_comm 1 (k + 13)

theorem L_half (k : Nat) : Q'.mkPos 1 2 (by decide) ≤ LQ (k + 14) := by
  have h := (ln2_partial_bracket 1 (k + 13)).1
  rw [idx] at h
  exact Q'.le_trans' _ _ _ (by decide) h

theorem P_ten (k : Nat) : NQ.toQ (pUp (k + 14)) ≤ Q'.mkPos 10 1 (by decide) := by
  have h := (S_chain 1 (k + 13)).2
  rw [idx] at h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (pUp_eqv _))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h (by decide)) (by decide))

theorem P_nine (k : Nat) : Q'.mkPos 9 1 (by decide) ≤ NQ.toQ (pUp (k + 14)) := by
  have h := (S_chain 1 (k + 13)).1
  rw [idx] at h
  exact Q'.le_trans' _ _ _ (by decide)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h (by decide)) (pUp_lower (k + 14) 0))

theorem pUp_d_pos (n : Nat) : 0 < (pUp n).d :=
  mul_d_pos (by decide) (add_d_pos (piST_d_pos n).1 (mul_d_pos (by decide) (piST_d_pos n).2))

/-- **Strict floor for the exact closed form**: `(k+1)/4 < E_k = ecomp k`, all `k`. -/
theorem r3Floor_lt_ecomp (k : Nat) : r3Floor k < NQ.toQ (ecomp k) := by
  have hLd := lnS_d_pos (k + 14)
  have hLn : 0 < (lnS (k + 14)).n := n_pos_of_lower hLd (by decide) (by decide) (L_half k)
  have hPd := pUp_d_pos (k + 14)
  have hPn : 0 < (pUp (k + 14)).n := n_pos_of_lower hPd (by decide) (by decide) (P_nine k)
  have hkp : 0 < (NQ.div ⟨51, 121⟩ (lnS (k + 14))).d := div_d_pos (by decide) hLn
  have hm : 0 < k + 4 := Nat.succ_pos _
  have hXd : 0 < (NQ.mul ⟨22, 3⟩ (lnS (k + 14))).d := mul_d_pos (by decide) hLd
  have hX : Q'.mkPos 11 3 (by decide) ≤ NQ.toQ (NQ.mul ⟨22, 3⟩ (lnS (k + 14))) :=
    Q'.le_trans' _ _ _
      (show Q'.mkPos 11 3 (by decide) ≤ Q'.mkPos 22 3 (by decide) * Q'.mkPos 1 2 (by decide) by decide)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (L_half k)
        (show (0 : Q') ≤ Q'.mkPos 22 3 (by decide) by decide))
        (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (toQ_mul ⟨22, 3⟩ _ (by decide) hLd)
          (Q'.mul_eqv_congr_right _ _ _ (toQ_lit 22 3 (by decide))))))
  have hB := div_lower _ _ hXd hPd hPn hX (P_ten k)
  have hBd : 0 < (NQ.div (NQ.mul ⟨22, 3⟩ (lnS (k + 14))) (pUp (k + 14))).d := div_d_pos hXd hPn
  have hD := D_lower ⟨k + 4, 1⟩ ⟨9989, 2000⟩
    (NQ.mul (NQ.div ⟨51, 121⟩ (lnS (k + 14))) (harm (k + 7)))
    (NQ.div (NQ.mul (NQ.mul (NQ.div ⟨51, 121⟩ (lnS (k + 14))) (NQ.div ⟨51, 121⟩ (lnS (k + 14))))
      (NQ.add (harm (k + 4)) ⟨1, 1⟩)) ⟨k + 4, 1⟩)
    (NQ.mul ⟨16, 17⟩ (seg (k + 4) 17)) Nat.one_pos (by decide)
    (mul_d_pos hkp (harm_d_pos _))
    (div_d_pos (mul_d_pos (mul_d_pos hkp hkp) (add_d_pos (harm_d_pos _) (by decide))) hm)
    (mul_d_pos (by decide) (seg_d_pos _ hm 17))
  have hDd : 0 < (NQ.add (NQ.add (NQ.add (NQ.add ⟨k + 4, 1⟩ ⟨9989, 2000⟩)
      (NQ.mul (NQ.div ⟨51, 121⟩ (lnS (k + 14))) (harm (k + 7))))
      (NQ.div (NQ.mul (NQ.mul (NQ.div ⟨51, 121⟩ (lnS (k + 14))) (NQ.div ⟨51, 121⟩ (lnS (k + 14))))
      (NQ.add (harm (k + 4)) ⟨1, 1⟩)) ⟨k + 4, 1⟩)) (NQ.mul ⟨16, 17⟩ (seg (k + 4) 17))).d :=
    add_d_pos (add_d_pos (add_d_pos (add_d_pos Nat.one_pos (by decide))
      (mul_d_pos hkp (harm_d_pos _)))
      (div_d_pos (mul_d_pos (mul_d_pos hkp hkp) (add_d_pos (harm_d_pos _) (by decide))) hm))
      (mul_d_pos (by decide) (seg_d_pos _ hm 17))
  have hE := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hD (by decide))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hB (toQ_nonneg _))
  refine lt_of_lt_of_le' ?_ (Q'.le_trans' _ _ _ hE (Q'.ge_of_eqv (toQ_mul _ _ hDd hBd)))
  show (((k + 1 : Nat) : Int)) * ((NQ.toQ ⟨k + 4, 1⟩ * Q'.mkPos 11 30 (by decide)).den : Int)
    < (((k + 4 : Nat) : Int) * 11) * ((Q'.mkPos ((k + 1 : Nat) : Int) 4 (by decide)).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den, toQ_den _ Nat.one_pos]
  have key : (k + 1) * (1 * 30) < (k + 4) * 11 * 4 :=
    calc (k + 1) * (1 * 30) ≤ (k + 1) * 44 := Nat.mul_le_mul_left _ (by decide)
      _ < (k + 4) * 44 := Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_left (by decide) k) (by decide)
      _ = (k + 4) * 11 * 4 := (Nat.mul_assoc (k + 4) 11 4).symm
  exact_mod_cast key

/-- The floor in `r3Raw` is never active: `r3Raw k = ecomp k` exactly. -/
theorem r3Raw_eq (k : Nat) : r3Raw k = NQ.toQ (ecomp k) := by
  have h := r3Floor_lt_ecomp k
  unfold r3Raw Q'.max'
  have hn : ¬ (NQ.toQ (ecomp k) ≤ r3Floor k) := Int.not_le.mpr h
  rw [if_neg hn]

/-- **Strict floor for the envelope**: `(k+1)/4 < r3E k`, all `k` (strengthens `r3Floor_le`). -/
theorem r3Floor_lt_r3E (k : Nat) : r3Floor k < r3E k :=
  lt_of_lt_of_le' (r3Floor_lt_ecomp k) (Q'.le_trans' _ _ _ (Q'.le_max'_left _ _) (r3Raw_le k))

end YMGap.RG.Robust3StrictFloor
