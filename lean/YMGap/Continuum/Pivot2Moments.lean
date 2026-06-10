/-
The 2×2 heat-kernel pivot equals its degree-4 polynomial in `r = e^{−t/2}`.

`pivotGram t = 1 + m₂ − m₁²` with `m₁ = 2·e^{−3t/4}`, `m₂ = 3·e^{−2t}`, and
`pivotPoly r = 1 + 3·r⁴ − 4·r³`.  Writing every moment as a power of
`r = e^{−t/2}` and folding the products with the exponential addition law
`expNeg_add_equiv` (and the exponent-`.eqv` transport `expNeg_eqv_congr`)
gives the two key identities

    m₂ ≃ 3·r⁴      (`e^{−2t} ≃ r⁴`),
    m₁² ≃ 4·r³      ((2·e^{−3t/4})² ≃ 4·r³),

which assemble (through `CReal.Equiv` congruence under `add`, `neg`, `mul`)
to `pivotGram t ≃ pivotPoly r`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]`, plus `Quot.sound` where `Nat`/`Int` enter.  No `Classical.*`,
no `sorryAx`.
-/

import YMGap.Continuum.Pivot2Defs
import YMGap.Constructive.ExpNegCongr

namespace YMGap.Continuum.Pivot2

open YMGap.Constructive

/-! ## `CReal.Equiv` is a congruence for `add`, `neg`, `mul`

These are proved pointwise (`add`, `neg`) or via the local-bound product
estimate (`mul`); none exist in the substrate yet, so we build them here. -/

/-- Transitivity of `CReal.Equiv` (split `ε` evenly). -/
theorem equiv_trans {A B C : CReal} (h1 : CReal.Equiv A B) (h2 : CReal.Equiv B C) :
    CReal.Equiv A C := by
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
  · -- A_n ≤ B_n + ½ε ≤ (C_n + ½ε) + ½ε ≃ C_n + ε
    refine Q'.le_trans' _ _ _ h1a ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) h2a) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (C.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (C.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)
  · refine Q'.le_trans' _ _ _ h2b ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) h1b) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (A.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (A.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)

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

/-- From `-a + -ε ≤ b`, conclude `-a ≤ b + ε`. -/
theorem neg_le_add_aux {a b ε : Q'} (h : -a + -ε ≤ b) : -a ≤ b + ε := by
  have h1 : (-a + -ε) + ε ≤ b + ε := Q'.add_le_add_right _ _ ε h
  have e1 : ((-a + -ε) + ε).eqv (-a + (-ε + ε)) := Q'.add_assoc_eqv (-a) (-ε) ε
  have e2 : (-a + (-ε + ε)).eqv (-a + 0) :=
    Q'.add_eqv_congr_left (-a) (-ε + ε) 0 (Q'.neg_add_self_eqv ε)
  have e3 : (-a + (0 : Q')) = -a := Q'.add_zero' (-a)
  have e2' : (-a + (-ε + ε)).eqv (-a) := by rw [e3] at e2; exact e2
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 e2'))) h1

/-- `neg` is `Equiv`-congruent. -/
theorem neg_congr {A A' : CReal} (hA : CReal.Equiv A A') :
    CReal.Equiv (CReal.neg A) (CReal.neg A') := by
  intro ε hε
  obtain ⟨N, hN⟩ := hA ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨ha, hb⟩ := hN n hn
  refine ⟨?_, ?_⟩
  · show -(A.approx n) ≤ -(A'.approx n) + ε
    -- A'_n ≤ A_n + ε  ⇒  -(A_n+ε) ≤ -A'_n  ⇒  -A_n + -ε ≤ -A'_n
    have hn1 : -(A.approx n + ε) ≤ -(A'.approx n) := Q'.neg_le_neg hb
    have hn2 : -(A.approx n) + -ε ≤ -(A'.approx n) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_add_eqv (A.approx n) ε)) hn1
    exact neg_le_add_aux hn2
  · show -(A'.approx n) ≤ -(A.approx n) + ε
    have hn1 : -(A'.approx n + ε) ≤ -(A.approx n) := Q'.neg_le_neg ha
    have hn2 : -(A'.approx n) + -ε ≤ -(A.approx n) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_add_eqv (A'.approx n) ε)) hn1
    exact neg_le_add_aux hn2

/-- From `a + −b ≤ c`, conclude `a ≤ b + c` (converse of `sub_le_of_le_add`). -/
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

/-- **`mul` right-congruence.**  A bounded left factor `A` times an `Equiv`
pair `B ≃ B'` is `Equiv`.  `|A_n·B_n − A_n·B'_n| = |A_n|·|B_n − B'_n| ≤ Bound·δ ≤ ε`. -/
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
  obtain ⟨hBa, hBb⟩ := hNB n hnB   -- B_n ≤ B'_n + δ,  B'_n ≤ B_n + δ
  refine ⟨?_, ?_⟩
  · -- A_n·B_n ≤ A_n·B'_n + ε
    show A.approx n * B.approx n ≤ A.approx n * B'.approx n + ε
    -- v = B_n + -B'_n : -δ ≤ v ≤ δ
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
  · -- A_n·B'_n ≤ A_n·B_n + ε
    show A.approx n * B'.approx n ≤ A.approx n * B.approx n + ε
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

/-- `mul` is `Equiv`-symmetric in its arguments (`A·B ≃ B·A`), pointwise. -/
theorem mul_comm_equiv (A B : CReal) : CReal.Equiv (CReal.mul A B) (CReal.mul B A) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.mul_comm_eqv (A.approx n) (B.approx n)

/-- **`mul` left-congruence**, from right-congruence and commutativity. -/
theorem mul_congr_left {A A' B : CReal} (hA : CReal.Equiv A A') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B) :=
  equiv_trans (mul_comm_equiv A B)
    (equiv_trans (mul_congr_right (A := B) hA) (mul_comm_equiv B A'))

/-- **`mul` is a two-sided `Equiv`-congruence.** -/
theorem mul_congr {A A' B B' : CReal} (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B') :=
  equiv_trans (mul_congr_right (A := A) hB) (mul_congr_left hA)

/-! ## Folding products of `expNeg`s -/

open YMGap.Constructive.ExpNeg

/-- `r = expNeg (t · ½)`.  Abbreviation of the exponent's nonnegativity. -/
theorem half_exp_nonneg (t : Q') (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ t * Q'.mkPos 1 2 (by decide) :=
  Q'.mul_nonneg t _ ht (by decide)

theorem r_eq (t : Q') (ht : (0 : Q') ≤ t) :
    r t ht = ExpNeg.expNeg (t * Q'.mkPos 1 2 (by decide)) (half_exp_nonneg t ht) := rfl

/-- `(c·a)·(d·b) ≃ (c·d)·(a·b)` — a four-factor commutation. -/
theorem swap_mul4 (c a d b : Q') : ((c * a) * (d * b)).eqv ((c * d) * (a * b)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c a (d * b)) ?_
  -- c·(a·(d·b)) ≃ c·(d·(a·b)) ≃ (c·d)·(a·b)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c (a * (d * b)) (d * (a * b)) ?_) ?_
  · -- a·(d·b) ≃ d·(a·b)
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a d b)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (a * d) (d * a) b (Q'.mul_comm_eqv a d)) ?_
    exact Q'.mul_assoc_eqv d a b
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv c d (a * b))

/-! ### Route (a): `m₂ ≃ 3·r⁴` -/

/-- `r⁴ ≃ e^{−2t}` (`quart r ≃ expNeg (t·2)`).  Folds `r·(r·(r·r))` through the
addition law and rewrites the exponent `½t+½t+½t+½t ≃ 2t`. -/
theorem quart_r_equiv (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (quart (r t ht))
      (ExpNeg.expNeg (t * Q'.mkPos 2 1 (by decide))
        (Q'.mul_nonneg t _ ht (by decide))) := by
  have hsnn : (0 : Q') ≤ t * Q'.mkPos 1 2 (by decide) := half_exp_nonneg t ht
  -- r·r ≃ expNeg (s+s)
  have e2 : CReal.Equiv (CReal.mul (r t ht) (r t ht))
      (ExpNeg.expNeg (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide))
        (Q'.zero_le_add _ _ hsnn hsnn)) :=
    expNeg_add_equiv _ _ hsnn hsnn
  -- r·(r·r) ≃ expNeg (s+(s+s))
  have e3 : CReal.Equiv (CReal.mul (r t ht) (CReal.mul (r t ht) (r t ht)))
      (ExpNeg.expNeg
        (t * Q'.mkPos 1 2 (by decide)
          + (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide)))
        (Q'.zero_le_add _ _ hsnn (Q'.zero_le_add _ _ hsnn hsnn))) := by
    refine equiv_trans (mul_congr_right (A := r t ht) e2) ?_
    exact expNeg_add_equiv _ _ hsnn (Q'.zero_le_add _ _ hsnn hsnn)
  -- r·(r·(r·r)) ≃ expNeg (s+(s+(s+s)))
  have e4 : CReal.Equiv (quart (r t ht))
      (ExpNeg.expNeg
        (t * Q'.mkPos 1 2 (by decide)
          + (t * Q'.mkPos 1 2 (by decide)
            + (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide))))
        (Q'.zero_le_add _ _ hsnn
          (Q'.zero_le_add _ _ hsnn (Q'.zero_le_add _ _ hsnn hsnn)))) := by
    refine equiv_trans (mul_congr_right (A := r t ht) e3) ?_
    exact expNeg_add_equiv _ _ hsnn
      (Q'.zero_le_add _ _ hsnn (Q'.zero_le_add _ _ hsnn hsnn))
  refine equiv_trans e4 ?_
  -- exponent identity: s+(s+(s+s)) ≃ t·(mkPos 2 1)
  refine expNeg_eqv_congr _ _ ?_
  -- factor t out, then concrete bracket eqv
  have hfac :
      (t * Q'.mkPos 1 2 (by decide)
        + (t * Q'.mkPos 1 2 (by decide)
          + (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide)))).eqv
      (t * (Q'.mkPos 1 2 (by decide)
        + (Q'.mkPos 1 2 (by decide)
          + (Q'.mkPos 1 2 (by decide) + Q'.mkPos 1 2 (by decide))))) := by
    have b1 :
        (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide)).eqv
        (t * (Q'.mkPos 1 2 (by decide) + Q'.mkPos 1 2 (by decide))) :=
      Q'.eqv_symm (Q'.mul_add_eqv t _ _)
    have b2 :
        (t * Q'.mkPos 1 2 (by decide)
          + (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide))).eqv
        (t * (Q'.mkPos 1 2 (by decide)
          + (Q'.mkPos 1 2 (by decide) + Q'.mkPos 1 2 (by decide)))) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ b1) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv t _ _)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ b2) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv t _ _)
  refine Q'.eqv_trans _ _ _ hfac ?_
  exact Q'.mul_eqv_congr_left t _ (Q'.mkPos 2 1 (by decide)) (by decide)

/-! ### Route (b): `m₁² ≃ 4·r³` -/

/-- `r³ ≃ e^{−3t/2}` (`cube r ≃ expNeg (t·(3/2))`). -/
theorem cube_r_equiv (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (cube (r t ht))
      (ExpNeg.expNeg (t * Q'.mkPos 3 2 (by decide))
        (Q'.mul_nonneg t _ ht (by decide))) := by
  have hsnn : (0 : Q') ≤ t * Q'.mkPos 1 2 (by decide) := half_exp_nonneg t ht
  have e2 : CReal.Equiv (CReal.mul (r t ht) (r t ht))
      (ExpNeg.expNeg (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide))
        (Q'.zero_le_add _ _ hsnn hsnn)) :=
    expNeg_add_equiv _ _ hsnn hsnn
  have e3 : CReal.Equiv (cube (r t ht))
      (ExpNeg.expNeg
        (t * Q'.mkPos 1 2 (by decide)
          + (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide)))
        (Q'.zero_le_add _ _ hsnn (Q'.zero_le_add _ _ hsnn hsnn))) := by
    refine equiv_trans (mul_congr_right (A := r t ht) e2) ?_
    exact expNeg_add_equiv _ _ hsnn (Q'.zero_le_add _ _ hsnn hsnn)
  refine equiv_trans e3 ?_
  refine expNeg_eqv_congr _ _ ?_
  have hfac :
      (t * Q'.mkPos 1 2 (by decide)
        + (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide))).eqv
      (t * (Q'.mkPos 1 2 (by decide)
        + (Q'.mkPos 1 2 (by decide) + Q'.mkPos 1 2 (by decide)))) := by
    have b1 :
        (t * Q'.mkPos 1 2 (by decide) + t * Q'.mkPos 1 2 (by decide)).eqv
        (t * (Q'.mkPos 1 2 (by decide) + Q'.mkPos 1 2 (by decide))) :=
      Q'.eqv_symm (Q'.mul_add_eqv t _ _)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ b1) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv t _ _)
  refine Q'.eqv_trans _ _ _ hfac ?_
  exact Q'.mul_eqv_congr_left t _ (Q'.mkPos 3 2 (by decide)) (by decide)

/-- The single exponential factor of `m₁`. -/
theorem m1exp_equiv (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv
      (CReal.mul (expo t ht (Q'.mkPos 3 4 (by decide)) (by decide))
                 (expo t ht (Q'.mkPos 3 4 (by decide)) (by decide)))
      (ExpNeg.expNeg (t * Q'.mkPos 3 2 (by decide))
        (Q'.mul_nonneg t _ ht (by decide))) := by
  have hunn : (0 : Q') ≤ t * Q'.mkPos 3 4 (by decide) := Q'.mul_nonneg t _ ht (by decide)
  have e1 : CReal.Equiv
      (CReal.mul (expo t ht (Q'.mkPos 3 4 (by decide)) (by decide))
                 (expo t ht (Q'.mkPos 3 4 (by decide)) (by decide)))
      (ExpNeg.expNeg (t * Q'.mkPos 3 4 (by decide) + t * Q'.mkPos 3 4 (by decide))
        (Q'.zero_le_add _ _ hunn hunn)) :=
    expNeg_add_equiv _ _ hunn hunn
  refine equiv_trans e1 ?_
  refine expNeg_eqv_congr _ _ ?_
  -- u+u ≃ t·(q+q) ≃ t·(mkPos 3 2)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv t _ _)) ?_
  exact Q'.mul_eqv_congr_left t _ (Q'.mkPos 3 2 (by decide)) (by decide)

/-! ## Assembly: `pivotGram ≃ pivotPoly r` -/

/-- Reflexivity of `CReal.Equiv`. -/
theorem equiv_refl (A : CReal) : CReal.Equiv A A :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_refl (A.approx n))

/-- `m₂ ≃ 3·r⁴`. -/
theorem m2_equiv (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (m2 t ht) (smul 3 (quart (r t ht))) :=
  (mul_congr_right (A := C 3) (quart_r_equiv t ht)).symm

/-- `m₁² ≃ 4·r³`. -/
theorem m1sq_equiv (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (CReal.mul (m1 t ht) (m1 t ht)) (smul 4 (cube (r t ht))) := by
  -- (2·E)·(2·E) ≃ (2·2)·(E·E)
  have hswap : CReal.Equiv
      (CReal.mul (m1 t ht) (m1 t ht))
      (CReal.mul (CReal.mul (C 2) (C 2))
        (CReal.mul (expo t ht (Q'.mkPos 3 4 (by decide)) (by decide))
                   (expo t ht (Q'.mkPos 3 4 (by decide)) (by decide)))) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact swap_mul4 ((C 2).approx n)
      ((expo t ht (Q'.mkPos 3 4 (by decide)) (by decide)).approx n)
      ((C 2).approx n)
      ((expo t ht (Q'.mkPos 3 4 (by decide)) (by decide)).approx n)
  -- 2·2 ≃ 4
  have hconst : CReal.Equiv (CReal.mul (C 2) (C 2)) (C 4) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    show (Q'.ofNat 2 * Q'.ofNat 2).eqv (Q'.ofNat 4)
    decide
  -- E·E ≃ r³
  have hEE : CReal.Equiv
      (CReal.mul (expo t ht (Q'.mkPos 3 4 (by decide)) (by decide))
                 (expo t ht (Q'.mkPos 3 4 (by decide)) (by decide)))
      (cube (r t ht)) :=
    equiv_trans (m1exp_equiv t ht) (cube_r_equiv t ht).symm
  exact equiv_trans hswap (mul_congr hconst hEE)

/-- **The 2×2 heat-kernel pivot equals its degree-4 polynomial in `r = e^{−t/2}`.** -/
theorem pivotGram_eqv_poly (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (pivotGram t ht) (pivotPoly (r t ht)) :=
  add_congr
    (add_congr (equiv_refl (C 1)) (m2_equiv t ht))
    (neg_congr (m1sq_equiv t ht))

end YMGap.Continuum.Pivot2

/-! ## Axiom-dependency gate (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Pivot2.pivotGram_eqv_poly
