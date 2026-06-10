/-
Folding the moments of the SU(2) heat-kernel 3×3 Gram into powers of the
single base `a = e^{−t/4}`.

`apow t k = e^{−t·k/4}` is the `k`-th power of `a`.  The exponential addition
law `expNeg_add_equiv` (+ the exponent-`.eqv` transport `expNeg_eqv_congr`)
gives the one-step fold `a · a^k ≃ a^{k+1}`, hence by induction

    rawPowC a k ≃ a^k          (`apow_eq_rawPow`),

where `rawPowC a k` is the nested constructive-real product `a·(a·(…·1))`.
Each moment `m_k = (k+1)·a^{k(k+2)}` is then `≃ (k+1)·rawPowC a (k(k+2))`, and
all six Gram entries become explicit polynomials in `a = base` — the form in
which the polynomial SOS-factorization identity (sibling `Pivot3Identity`) is
discharged pointwise.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.Pivot3Defs
import YMGap.Constructive.ExpNegCongr
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.Pivot3

open YMGap.Constructive

/-! ## `CReal.Equiv` congruences (add / mul / refl / trans)

Re-derived here exactly as in the 2×2 development; none live in the substrate.
We reuse the proofs already established for the 2×2 pivot by importing nothing
new — they are short pointwise/bounded arguments. -/

/-- Transitivity of `CReal.Equiv`. -/
theorem equiv_trans {A B D : CReal} (h1 : CReal.Equiv A B) (h2 : CReal.Equiv B D) :
    CReal.Equiv A D := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N1, hN1⟩ := h1 (HalfPow.half * ε) hhε
  obtain ⟨N2, hN2⟩ := h2 (HalfPow.half * ε) hhε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨h1a, h1b⟩ := hN1 n hn1
  obtain ⟨h2a, h2b⟩ := hN2 n hn2
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ h1a ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) h2a) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (D.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (D.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)
  · refine Q'.le_trans' _ _ _ h2b ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) h1b) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (A.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (A.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)

/-- Reflexivity of `CReal.Equiv`. -/
theorem equiv_refl (A : CReal) : CReal.Equiv A A :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_refl (A.approx n))

/-- `add` is `Equiv`-congruent (pointwise, splitting `ε`). -/
theorem add_congr {A A' B B' : CReal} (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.add A B) (CReal.add A' B') := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N1, hN1⟩ := hA (HalfPow.half * ε) hhε
  obtain ⟨N2, hN2⟩ := hB (HalfPow.half * ε) hhε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨h1a, h1b⟩ := hN1 n hn1
  obtain ⟨h2a, h2b⟩ := hN2 n hn2
  refine ⟨?_, ?_⟩
  · show A.approx n + B.approx n ≤ (A'.approx n + B'.approx n) + ε
    have hsum : A.approx n + B.approx n
        ≤ (A'.approx n + HalfPow.half * ε) + (B'.approx n + HalfPow.half * ε) :=
      Q'.add_le_add h1a h2a
    refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _ (Q'.regroup (A'.approx n) (B'.approx n) (HalfPow.half * ε)) ?_
    exact Q'.add_eqv_congr_left (A'.approx n + B'.approx n)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε)
  · show A'.approx n + B'.approx n ≤ (A.approx n + B.approx n) + ε
    have hsum : A'.approx n + B'.approx n
        ≤ (A.approx n + HalfPow.half * ε) + (B.approx n + HalfPow.half * ε) :=
      Q'.add_le_add h1b h2b
    refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _ (Q'.regroup (A.approx n) (B.approx n) (HalfPow.half * ε)) ?_
    exact Q'.add_eqv_congr_left (A.approx n + B.approx n)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε)

/-- From `a + −b ≤ c`, conclude `a ≤ b + c`. -/
theorem le_add_of_diff_le {a b c : Q'} (h : a + -b ≤ c) : a ≤ b + c := by
  have h1 : (a + -b) + b ≤ c + b := Q'.add_le_add_right _ _ b h
  have e1 : ((a + -b) + b).eqv (a + (-b + b)) := Q'.add_assoc_eqv a (-b) b
  have e2 : (a + (-b + b)).eqv (a + 0) :=
    Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b)
  have e3 : (a + (0 : Q')) = a := Q'.add_zero' a
  have e2' : (a + (-b + b)).eqv a := by rw [e3] at e2; exact e2
  have ha : a ≤ c + b :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 e2'))) h1
  exact Q'.le_trans' _ _ _ ha (Q'.le_of_eqv (Q'.add_comm_eqv c b))

/-- `a·(b + −c) ≃ a·b + −(a·c)`. -/
theorem mul_diff_eqv (a b c : Q') : (a * (b + -c)).eqv (a * b + -(a * c)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_add_eqv a b (-c))
    (Q'.add_eqv_congr_left (a * b) (a * (-c)) (-(a * c)) (Q'.mul_neg_eqv a c))

/-- `mul` right-congruence: a bounded left factor times an `Equiv` pair. -/
theorem mul_congr_right {A B B' : CReal} (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') := by
  obtain ⟨NA, Bd, hBd, hAbound⟩ := CReal.localBound A
  intro ε hε
  obtain ⟨δ, hδpos, hδle⟩ := CReal.exists_mul_le hBd hε
  obtain ⟨NB, hNB⟩ := hB δ hδpos
  refine ⟨max NA NB, fun n hn => ?_⟩
  have hnA : NA ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnB : NB ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hAlb, hAub⟩ := hAbound n hnA
  obtain ⟨hBa, hBb⟩ := hNB n hnB
  refine ⟨?_, ?_⟩
  · show A.approx n * B.approx n ≤ A.approx n * B'.approx n + ε
    have hv2 : B.approx n + -(B'.approx n) ≤ δ := Q'.sub_le_of_le_add hBa
    have hv1 : -δ ≤ B.approx n + -(B'.approx n) := Q'.neg_le_sub_of_le_add hBb
    have hprod : A.approx n * (B.approx n + -(B'.approx n)) ≤ Bd * δ :=
      Q'.mul_le_of_bounds hBd (Q'.le_of_lt hδpos) hAlb hAub hv1 hv2
    have hbig : A.approx n * (B.approx n + -(B'.approx n)) ≤ ε :=
      Q'.le_trans' _ _ _ hprod hδle
    have heqv : (A.approx n * (B.approx n + -(B'.approx n))).eqv
        (A.approx n * B.approx n + -(A.approx n * B'.approx n)) :=
      mul_diff_eqv (A.approx n) (B.approx n) (B'.approx n)
    have hdiff : A.approx n * B.approx n + -(A.approx n * B'.approx n) ≤ ε :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv) hbig
    exact le_add_of_diff_le hdiff
  · show A.approx n * B'.approx n ≤ A.approx n * B.approx n + ε
    have hv2 : B'.approx n + -(B.approx n) ≤ δ := Q'.sub_le_of_le_add hBb
    have hv1 : -δ ≤ B'.approx n + -(B.approx n) := Q'.neg_le_sub_of_le_add hBa
    have hprod : A.approx n * (B'.approx n + -(B.approx n)) ≤ Bd * δ :=
      Q'.mul_le_of_bounds hBd (Q'.le_of_lt hδpos) hAlb hAub hv1 hv2
    have hbig : A.approx n * (B'.approx n + -(B.approx n)) ≤ ε :=
      Q'.le_trans' _ _ _ hprod hδle
    have heqv : (A.approx n * (B'.approx n + -(B.approx n))).eqv
        (A.approx n * B'.approx n + -(A.approx n * B.approx n)) :=
      mul_diff_eqv (A.approx n) (B'.approx n) (B.approx n)
    have hdiff : A.approx n * B'.approx n + -(A.approx n * B.approx n) ≤ ε :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv) hbig
    exact le_add_of_diff_le hdiff

/-- `mul` is `Equiv`-symmetric in its arguments (`A·B ≃ B·A`). -/
theorem mul_comm_equiv (A B : CReal) : CReal.Equiv (CReal.mul A B) (CReal.mul B A) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_comm_eqv (A.approx n) (B.approx n))

/-- `mul` left-congruence. -/
theorem mul_congr_left {A A' B : CReal} (hA : CReal.Equiv A A') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B) :=
  equiv_trans (mul_comm_equiv A B)
    (equiv_trans (mul_congr_right (A := B) hA) (mul_comm_equiv B A'))

/-- `mul` is a two-sided `Equiv`-congruence. -/
theorem mul_congr {A A' B B' : CReal} (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B') :=
  equiv_trans (mul_congr_right (A := A) hB) (mul_congr_left hA)

/-! ## The nested-product power and its fold to `apow` -/

/-- Nested constructive-real power `a·(a·(…·1))` (`k` factors of `a`). -/
def rawPowC (x : CReal) : Nat → CReal
  | 0 => C 1
  | (k + 1) => CReal.mul x (rawPowC x k)

/-- One-step exponent fold: `t·(1/4) + t·(k/4) ≃ t·((k+1)/4)`. -/
theorem quarter_exp_succ (t : Q') (k : Nat) :
    (t * Q'.mkPos (Int.ofNat 1) 4 (by decide)
      + t * Q'.mkPos (Int.ofNat k) 4 (by decide)).eqv
    (t * Q'.mkPos (Int.ofNat (k + 1)) 4 (by decide)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv t _ _)) ?_
  refine Q'.mul_eqv_congr_left t _ _ ?_
  -- (1/4 + k/4) ≃ (k+1)/4 : cross-multiply.
  -- mkPos n 4 = ⟨n,3⟩ : .num = n, .den = 4.  Sum: .num = 1*4 + k*4, .den = 16.
  show ((Int.ofNat 1) * ((Q'.mkPos (Int.ofNat k) 4 (by decide)).den : Int)
          + (Int.ofNat k) * ((Q'.mkPos (Int.ofNat 1) 4 (by decide)).den : Int))
        * ((Q'.mkPos (Int.ofNat (k + 1)) 4 (by decide)).den : Int)
      = Int.ofNat (k + 1)
        * (((Q'.mkPos (Int.ofNat 1) 4 (by decide)
              + Q'.mkPos (Int.ofNat k) 4 (by decide)).den) : Int)
  rw [Q'.add_den_cast (Q'.mkPos (Int.ofNat 1) 4 (by decide)) (Q'.mkPos (Int.ofNat k) 4 (by decide))]
  rw [Q'.mkPos_den (Int.ofNat 1) 4 (by decide), Q'.mkPos_den (Int.ofNat k) 4 (by decide),
      Q'.mkPos_den (Int.ofNat (k + 1)) 4 (by decide)]
  simp only [Int.ofNat_eq_natCast]
  push_cast
  omega

/-- `term 0 (k+1) ≃ 0` — every term beyond the constant vanishes at `x = 0`. -/
theorem term_zero_succ_eqv (k : Nat) : (ExpNeg.term (0 : Q') (k + 1)).eqv 0 := by
  have hterm : ExpNeg.term (0 : Q') (k + 1)
      = ExpNeg.term (0 : Q') k * ((-(0 : Q')) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)) :=
    ExpNeg.term_succ 0 k
  rw [hterm]
  -- (-0)*m ≃ 0, so the product ≃ term * 0 ≃ 0
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (ExpNeg.term 0 k)
      ((-(0 : Q')) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)) 0 ?_) ?_
  · -- (-0)*m ≃ 0 :  -(0) ≃ 0, then 0*m ≃ 0
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (-(0 : Q')) 0 (Q'.mkPos 1 (k + 1) (Nat.succ_pos _)) ?_)
      (QPoly.q_zero_mul (Q'.mkPos 1 (k + 1) (Nat.succ_pos _)))
    show ((-(0 : Q')).num * ((0 : Q').den : Int)) = (0 : Q').num * ((-(0 : Q')).den : Int)
    decide
  · -- term * 0 ≃ 0
    exact QPoly.q_mul_zero (ExpNeg.term 0 k)

/-- `partialSum 0 (n+1) ≃ 1`. -/
theorem partialSum_zero_succ_eqv (n : Nat) : (ExpNeg.partialSum 0 (n + 1)).eqv 1 := by
  induction n with
  | zero => rw [ExpNeg.partialSum_one 0]; exact Q'.eqv_refl 1
  | succ n ih =>
    rw [ExpNeg.partialSum_succ]
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (ExpNeg.partialSum 0 (n + 1)) 1 (ExpNeg.term 0 (n + 1)) ih) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 (ExpNeg.term 0 (n + 1)) 0 (term_zero_succ_eqv n)) ?_
    show ((1 : Q') + 0).eqv 1
    rw [Q'.add_zero']; exact Q'.eqv_refl 1

/-- `expNeg 0 ≃ C 1`. -/
theorem expNeg_zero_equiv_one (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (apow t ht 0) (C 1) := by
  -- apow 0 = expNeg (t * mkPos 0 4); the exponent ≃ 0, so apow 0 ≃ expNeg 0.
  have hexp : CReal.Equiv (apow t ht 0) (ExpNeg.expNeg (0 : Q') (by decide)) := by
    refine expNeg_eqv_congr (quarter_nonneg t ht 0) (by decide) ?_
    -- t * (0/4) ≃ t * 0 ≃ 0
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left t (Q'.mkPos (Int.ofNat 0) 4 (by decide)) 0 ?_)
      (QPoly.q_mul_zero t)
    show ((Q'.mkPos (Int.ofNat 0) 4 (by decide)).num * ((0 : Q').den : Int))
        = (0 : Q').num * ((Q'.mkPos (Int.ofNat 0) 4 (by decide)).den : Int)
    decide
  -- expNeg 0 ≃ C 1, eventually (n ≥ 1): partialSum 0 (1+m) ≃ 1 ≃ (C 1).approx n.
  have hone : CReal.Equiv (ExpNeg.expNeg (0 : Q') (by decide)) (C 1) := by
    intro ε hε
    refine ⟨1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    -- (expNeg 0).approx (1+m) = partialSum 0 (1+m) ≃ 1; (C 1).approx _ = Q'.ofNat 1 ≃ 1.
    have hps : (ExpNeg.partialSum 0 (1 + m)).eqv 1 := by
      rw [Nat.add_comm]; exact partialSum_zero_succ_eqv m
    have h1eqv : ((C 1).approx (1 + m)).eqv (1 : Q') := by
      show (Q'.ofNat 1).eqv (1 : Q'); decide
    refine ⟨?_, ?_⟩
    · -- partialSum 0 (1+m) ≤ (C 1).approx + ε
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hps) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm h1eqv)) ?_
      exact Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)
    · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv h1eqv) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hps)) ?_
      exact Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)
  exact equiv_trans hexp hone

/-- **`rawPowC a k ≃ a^k`** — the nested product folds to the single power. -/
theorem apow_eq_rawPow (t : Q') (ht : (0 : Q') ≤ t) :
    ∀ k, CReal.Equiv (rawPowC (base t ht) k) (apow t ht k)
  | 0 => (expNeg_zero_equiv_one t ht).symm
  | (k + 1) => by
      -- rawPowC a (k+1) = a · rawPowC a k ≃ a · a^k ≃ a^{k+1}
      refine equiv_trans (mul_congr_right (A := base t ht) (apow_eq_rawPow t ht k)) ?_
      -- base · apow k ≃ apow (k+1)
      have hb : (0 : Q') ≤ t * Q'.mkPos (Int.ofNat 1) 4 (by decide) := quarter_nonneg t ht 1
      have hk : (0 : Q') ≤ t * Q'.mkPos (Int.ofNat k) 4 (by decide) := quarter_nonneg t ht k
      refine equiv_trans (expNeg_add_equiv _ _ hb hk) ?_
      exact expNeg_eqv_congr (Q'.zero_le_add _ _ hb hk) (quarter_nonneg t ht (k + 1))
        (quarter_exp_succ t k)

end YMGap.Continuum.Pivot3
