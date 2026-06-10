/-
Track B / E1 — the **full SU(2) heat-kernel 3×3 positive-semidefiniteness**
(degree-≤2 observables `a = c₀χ₀ + c₁χ₁ + c₂χ₂`).

The normalized 3×3 Gram matrix of the heat kernel is

    G = [[1, m₁, m₂], [m₁, 1+m₂, m₁+m₃], [m₂, m₁+m₃, 1+m₂+m₄]],
    m_k = (k+1)·e^{−t·k(k+2)/4},

and `form3 = Σ_{i,j<3} c_i c_j G_{ij}` is the energy `E((c₀χ₀+c₁χ₁+c₂χ₂)²)`.
Writing `a = e^{−t/4}` and `P = 3a⁴+2a²+1 ≥ 1`, the scaled energy is a manifest
nonnegatively-weighted sum of three squares (`pform3_eq_sos`):

    P·form3 = P·M₀² + 1·M₁² + big·M₂²,

with all weights `P, 1, big ≥ 0` (and `M₀,M₁,M₂` linear in `c`).  Hence
`P·form3 ≥ 0`, and since `P ≥ 1 > 0`, `form3 ≥ 0` — the full 3×3
positive-semidefiniteness, the degree-2 extension of `Pivot2.form2_nonneg`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.Pivot3Form
import YMGap.Constructive.Soundness
import YMGap.Constructive.SU3CharFactor

namespace YMGap.Continuum.Pivot3

open YMGap.Constructive

/-! ## Nonnegativity of the base and the polynomial weights -/

/-- The base `a = e^{−t/4} ≥ 0`. -/
theorem base_nonneg (t : Q') (ht : (0 : Q') ≤ t) : ExpPos.geRat (base t ht) 0 := by
  unfold base apow
  exact expNeg_geRat_zero _ _

/-- Every coefficient of a `Poly` is `≥ 0` (a `Bool` test). -/
def allNonnegB : QPoly.Poly → Bool
  | [] => true
  | (c :: cs) => decide ((0 : Q') ≤ c) && allNonnegB cs

/-- **`evalC p ≥ 0`** when all coefficients of `p` are `≥ 0` (Horner of
nonnegatives at the nonnegative base). -/
theorem evalC_nonneg (t : Q') (ht : (0 : Q') ≤ t) :
    ∀ (p : QPoly.Poly), allNonnegB p = true → ExpPos.geRat (evalC t ht p) 0
  | [], _ => SumOfSquares.geRat_ofQ'_nonneg (by decide)
  | (c :: cs), h => by
      have hb : decide ((0 : Q') ≤ c) = true ∧ allNonnegB cs = true := by
        rw [allNonnegB, Bool.and_eq_true] at h; exact h
      have hc : (0 : Q') ≤ c := of_decide_eq_true hb.1
      -- evalC (c::cs) = ofQ' c + base·(evalC cs)
      show ExpPos.geRat (CReal.add (CReal.ofQ' c) (CReal.mul (base t ht) (evalC t ht cs))) 0
      have h1 : ExpPos.geRat (CReal.ofQ' c) 0 := SumOfSquares.geRat_ofQ'_nonneg hc
      have h2 : ExpPos.geRat (CReal.mul (base t ht) (evalC t ht cs)) 0 :=
        CReal.mul_nonneg (base_nonneg t ht) (evalC_nonneg t ht cs hb.2)
      exact ExpPos.geRat_mono (SumOfSquares.geRat_add h1 h2) (by decide)

/-- `P = evalC lP ≥ 0`. -/
theorem Pp_nonneg (t : Q') (ht : (0 : Q') ≤ t) : ExpPos.geRat (Pp t ht) 0 :=
  evalC_nonneg t ht lP (by decide)

/-- `big = evalC lbig ≥ 0`. -/
theorem bigp_nonneg (t : Q') (ht : (0 : Q') ≤ t) : ExpPos.geRat (bigp t ht) 0 :=
  evalC_nonneg t ht lbig (by decide)

/-! ## `sos3 ≥ 0` -/

/-- **The sum-of-squares value is nonnegative:** `P·M₀² + M₁² + big·M₂² ≥ 0`.
Each term is `(≥0 weight)·(square) ≥ 0`. -/
theorem sos3_nonneg (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') :
    ExpPos.geRat (sos3 t ht c0 c1 c2) 0 := by
  unfold sos3
  -- P·M0² ≥ 0
  have h0 : ExpPos.geRat
      (CReal.mul (Pp t ht) (CReal.mul (M0 t ht c0 c1 c2) (M0 t ht c0 c1 c2))) 0 :=
    CReal.mul_nonneg (Pp_nonneg t ht) (SumOfSquares.geRat_sq_nonneg (M0 t ht c0 c1 c2))
  -- M1² ≥ 0
  have h1 : ExpPos.geRat (CReal.mul (M1 t ht c1 c2) (M1 t ht c1 c2)) 0 :=
    SumOfSquares.geRat_sq_nonneg (M1 t ht c1 c2)
  -- big·M2² ≥ 0
  have h2 : ExpPos.geRat
      (CReal.mul (bigp t ht) (CReal.mul (M2 t ht c2) (M2 t ht c2))) 0 :=
    CReal.mul_nonneg (bigp_nonneg t ht) (SumOfSquares.geRat_sq_nonneg (M2 t ht c2))
  exact ExpPos.geRat_mono
    (SumOfSquares.geRat_add h0 (SumOfSquares.geRat_add h1 h2)) (by decide)

/-! ## `P ≥ 1` and the division step -/

/-- `evalC p ≥ c₀` when the constant coefficient is `c₀` and every higher
coefficient is `≥ 0`: `evalC (c₀::cs) = c₀ + base·(evalC cs) ≥ c₀ + 0`. -/
theorem evalC_ge_head (t : Q') (ht : (0 : Q') ≤ t) (c0 : Q') (cs : QPoly.Poly)
    (hcs : allNonnegB cs = true) :
    ExpPos.geRat (evalC t ht (c0 :: cs)) c0 := by
  show ExpPos.geRat (CReal.add (CReal.ofQ' c0) (CReal.mul (base t ht) (evalC t ht cs))) c0
  have h1 : ExpPos.geRat (CReal.ofQ' c0) c0 :=
    ExpPos.geRat_of_eventually ⟨0, fun _ _ => Q'.le_refl' c0⟩
  have h2 : ExpPos.geRat (CReal.mul (base t ht) (evalC t ht cs)) 0 :=
    CReal.mul_nonneg (base_nonneg t ht) (evalC_nonneg t ht cs hcs)
  refine ExpPos.geRat_mono (SumOfSquares.geRat_add h1 h2) ?_
  -- c0 ≤ c0 + 0
  have : (c0 + (0:Q')) = c0 := Q'.add_zero' c0
  rw [this]; exact Q'.le_refl' c0

/-- **`P ≥ 1` pointwise.** `(Pp).approx n = 1 + base_n²·(2 + 3·base_n²) ≥ 1`. -/
theorem Pp_approx_ge_one (t : Q') (ht : (0 : Q') ≤ t) (n : Nat) :
    (1 : Q') ≤ (Pp t ht).approx n := by
  -- (Pp).approx n = eval lP (base_n) = 1 + base_n·(0 + base_n·(2 + base_n·(0 + base_n·(3 + base_n·0))))
  rw [Pp, evalC_approx t ht lP n]
  generalize hq : (base t ht).approx n = q
  -- eval [1,0,2,0,3] q = 1 + q·(0 + q·(2 + q·(0 + q·(3 + q·0))))  ; show ≥ 1.
  show (1 : Q') ≤ 1 + q * (0 + q * (Q'.ofNat 2 + q * (0 + q * (Q'.ofNat 3 + q * 0))))
  -- The tail `q·(…)` is `≥ 0`: it equals q²·(2 + 3q²) with q²≥0, 2+3q²>0.  We bound
  -- `1 ≤ 1 + tail` by `0 ≤ tail`.
  -- `tail ≃ (q·q)·(2 + (q·q)·3)`, an even-power form that is `≥ 0` regardless of
  -- the sign of the rational `q = base_n`.
  have htail_eqv :
      (q * (0 + q * (Q'.ofNat 2 + q * (0 + q * (Q'.ofNat 3 + q * 0))))).eqv
      ((q * q) * (Q'.ofNat 2 + (q * q) * Q'.ofNat 3)) := by
    -- innermost: 3 + q*0 ≃ 3
    have e0 : (Q'.ofNat 3 + q * 0).eqv (Q'.ofNat 3) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (QPoly.q_mul_zero q))
        (QPoly.q_add_zero_eqv _)
    -- 0 + q*(3+q*0) ≃ q*3
    have e1 : (0 + q * (Q'.ofNat 3 + q * 0)).eqv (q * Q'.ofNat 3) :=
      Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) (Q'.mul_eqv_congr_left q _ _ e0)
    -- 2 + q*(0+q*(3+q*0)) ≃ 2 + q*(q*3) ≃ 2 + (q*q)*3
    have e2 : (Q'.ofNat 2 + q * (0 + q * (Q'.ofNat 3 + q * 0))).eqv
        (Q'.ofNat 2 + (q * q) * Q'.ofNat 3) :=
      Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ e1)
          (Q'.mul_assoc_eqv q q (Q'.ofNat 3)).symm)
    -- 0 + q*(2+…) ≃ q*(2 + (q*q)*3)
    have e3 : (0 + q * (Q'.ofNat 2 + q * (0 + q * (Q'.ofNat 3 + q * 0)))).eqv
        (q * (Q'.ofNat 2 + (q * q) * Q'.ofNat 3)) :=
      Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) (Q'.mul_eqv_congr_left q _ _ e2)
    -- q*(0+q*(2+…)) ≃ q*(q*(2+(qq)3)) ≃ (q*q)*(2+(qq)3)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ e3)
      (Q'.mul_assoc_eqv q q (Q'.ofNat 2 + (q * q) * Q'.ofNat 3)).symm
  have hqsq : (0 : Q') ≤ q * q := SumOfSquares.q_mul_self_nonneg q
  have hinner : (0 : Q') ≤ Q'.ofNat 2 + (q * q) * Q'.ofNat 3 :=
    Q'.le_trans' _ _ _ (by decide : (0:Q') ≤ Q'.ofNat 2)
      (Q'.add_le_self_of_nonneg (Q'.ofNat 2) _
        (Q'.mul_nonneg (q * q) (Q'.ofNat 3) hqsq (by decide)))
  have htail : (0 : Q') ≤ q * (0 + q * (Q'.ofNat 2 + q * (0 + q * (Q'.ofNat 3 + q * 0)))) :=
    Q'.le_trans' _ _ _ (Q'.mul_nonneg (q * q) _ hqsq hinner) (Q'.ge_of_eqv htail_eqv)
  have := Q'.add_le_add_left 1 0 _ htail
  rw [Q'.add_zero'] at this
  exact this

/-! ## The division step `P·form3 ≥ 0 ∧ P ≥ 1 ⟹ form3 ≥ 0` -/

/-- `p.den ≤ p.num` is the unfolding of `1 ≤ p`. -/
theorem one_le_num (p : Q') (hp : (1 : Q') ≤ p) : ((p.den : Int)) ≤ p.num := by
  have h : (1 : Q').num * (p.den : Int) ≤ p.num * ((1 : Q').den : Int) := hp
  -- (1:Q') = ⟨1,0⟩ : num 1, den 1
  show (p.den : Int) ≤ p.num
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : (((1 : Q').den : Int)) = 1 := by decide
  rw [h1n, h1d, Int.one_mul, Int.mul_one] at h
  exact h

/-- `f.num ≤ 0` is the unfolding of `f ≤ 0`. -/
theorem nonpos_num (f : Q') (hf : f ≤ 0) : f.num ≤ 0 := by
  have h : f.num * ((0 : Q').den : Int) ≤ (0 : Q').num * (f.den : Int) := hf
  have h0n : (0 : Q').num = 0 := rfl
  have h0d : (((0 : Q').den : Int)) = 1 := by decide
  rw [h0n, h0d, Int.mul_one, Int.zero_mul] at h
  exact h

/-- `p·f ≤ f` when `1 ≤ p` and `f ≤ 0`. -/
theorem mul_le_self_of_nonpos {p f : Q'} (hp : (1 : Q') ≤ p) (hf : f ≤ 0) :
    p * f ≤ f := by
  -- goal (Q'.le): (p*f).num · f.den ≤ f.num · (p*f).den, i.e.
  --   (p.num·f.num)·f.den ≤ f.num·(p.den·f.den)
  show (p.num * f.num) * ((f.den : Int)) ≤ f.num * (((p * f).den : Int))
  rw [Q'.mul_den_cast p f]
  have hpd : ((p.den : Int)) ≤ p.num := one_le_num p hp
  have hfn : f.num ≤ 0 := nonpos_num f hf
  have hden_nn : (0 : Int) ≤ (f.den : Int) := Int.natCast_nonneg f.den
  -- p.den·f.den ≤ p.num·f.den
  have hstep : (p.den : Int) * (f.den : Int) ≤ p.num * (f.den : Int) :=
    Int.mul_le_mul_of_nonneg_right hpd hden_nn
  -- multiply by f.num ≤ 0 on the left (flips):  f.num·(p.num·f.den) ≤ f.num·(p.den·f.den)
  have hmul : f.num * (p.num * (f.den : Int)) ≤ f.num * ((p.den : Int) * (f.den : Int)) :=
    Int.mul_le_mul_of_nonpos_left hfn hstep
  have lhs_eq : (p.num * f.num) * (f.den : Int) = f.num * (p.num * (f.den : Int)) := by
    rw [Int.mul_comm p.num f.num, Int.mul_assoc]
  rw [lhs_eq]
  exact hmul

/-- **The key Q' division inequality:** `1 ≤ p`, `0 ≤ e`, `0 ≤ p·f + e` ⟹ `0 ≤ f + e`. -/
theorem div_ineq {p f e : Q'} (hp : (1 : Q') ≤ p) (he : (0 : Q') ≤ e)
    (h : (0 : Q') ≤ p * f + e) : (0 : Q') ≤ f + e := by
  rcases Int.le_total 0 f.num with hf | hf
  · -- 0 ≤ f
    have hf' : (0 : Q') ≤ f := (Q'.zero_le_iff_num_nonneg f).mpr hf
    exact Q'.zero_le_add f e hf' he
  · -- f ≤ 0
    have hf' : f ≤ 0 := by
      show f.num * ((0:Q').den : Int) ≤ (0:Q').num * (f.den : Int)
      have h0n : (0 : Q').num = 0 := rfl
      have h0d : (((0 : Q').den : Int)) = 1 := by decide
      rw [h0n, h0d, Int.mul_one, Int.zero_mul]; exact hf
    have hle : p * f + e ≤ f + e :=
      Q'.add_le_add_right (p * f) f e (mul_le_self_of_nonpos hp hf')
    exact Q'.le_trans' _ _ _ h hle

/-- **The CReal division step:** `geRat (Pp·y) 0` and `Pp ≥ 1` pointwise give
`geRat y 0`. -/
theorem geRat_of_mul_Pp (t : Q') (ht : (0 : Q') ≤ t) {y : CReal}
    (h : ExpPos.geRat (CReal.mul (Pp t ht) y) 0) : ExpPos.geRat y 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hge : (0 : Q') ≤ (Pp t ht).approx n * y.approx n + ε := hN n hn
  exact div_ineq (Pp_approx_ge_one t ht n) (Q'.le_of_lt hε) hge

/-! ## The 3×3 PSD theorem -/

/-- **Full SU(2) heat-kernel 3×3 positive-semidefiniteness:** the quadratic
form `form3 = Σ_{i,j<3} c_i c_j G_{ij}` is nonnegative for every
`c₀, c₁, c₂`.  The scaled energy `P·form3 = P·M₀² + M₁² + big·M₂²` is a
nonnegatively-weighted sum of squares (so `≥ 0`), and `P ≥ 1 > 0` divides
back to `form3 ≥ 0`. -/
theorem form3_nonneg (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') :
    ExpPos.geRat (form3 t ht c0 c1 c2) 0 :=
  geRat_of_mul_Pp t ht
    (SU3CharFactor.geRat_of_equiv (pform3_eq_sos t ht c0 c1 c2) (sos3_nonneg t ht c0 c1 c2))

end YMGap.Continuum.Pivot3

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Pivot3.pform3_eq_sos
#print axioms YMGap.Continuum.Pivot3.form3_nonneg
