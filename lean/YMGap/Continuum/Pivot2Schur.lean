/-
Track B / E1 — the **full SU(2) heat-kernel 2×2 PSD** (completing the square).

The normalized 2×2 Gram matrix of the heat kernel on degree-≤1 observables is
`G = [[1, m₁], [m₁, 1+m₂]]` with moments `m₁ = 2·e^{−3t/4}`, `m₂ = 3·e^{−2t}`.
For `a = c0·χ₀ + c1·χ₁` the energy is the quadratic form

    E(a²) = c0²·G₀₀ + 2c0c1·G₀₁ + c1²·G₁₁
          = c0²·1 + 2c0c1·m₁ + c1²·(1+m₂).

Completing the square (the LDLᵀ / Schur decomposition of `G`) writes this as the
nonnegatively-weighted sum of squares

    E(a²) = 1·(c0 + c1·m₁)² + D₁·c1²,     D₁ = 1 + m₂ − m₁²,

with both pivots `≥ 0` (`1 ≥ 0` and the Schur complement `D₁ ≥ 0`, the latter
established in `Pivot2.pivotGram_nonneg`).  Feeding this certificate to the
CReal-weighted SOS consumer `geRat_sos_creal` gives `E(a²) ≥ 0` — the full 2×2
positive-semidefiniteness, the analytic content of E1 beyond the
nonnegative-cone result.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.Pivot2
import YMGap.Continuum.Pivot2Defs
import YMGap.Constructive.QPoly
import YMGap.Constructive.SU3CharFactor

namespace YMGap.Continuum.Pivot2

open YMGap.Constructive

/-- The heat-kernel 2×2 energy `E(a²)` for `a = c0·χ₀ + c1·χ₁`:
`c0²·G₀₀ + 2c0c1·G₀₁ + c1²·G₁₁` with `G₀₀ = 1`, `G₀₁ = m₁`, `G₁₁ = 1 + m₂`. -/
def form2 (t : Q') (ht : (0:Q') ≤ t) (c0 c1 : Q') : CReal :=
  CReal.add (CReal.add (CReal.mul (CReal.ofQ' (c0*c0)) (Pivot2.C 1))
                       (CReal.mul (CReal.ofQ' (2*(c0*c1))) (Pivot2.m1 t ht)))
            (CReal.mul (CReal.ofQ' (c1*c1)) (CReal.add (Pivot2.C 1) (Pivot2.m2 t ht)))

/-- `a + a ≃ 2·a` for rationals (`2 = (2:Q')` the numeric literal). -/
theorem twoMul (a : Q') : ((a + a)).eqv (2 * a) := by
  show ((a + a)).num * ((2 * a).den : Int) = ((2 * a)).num * ((a + a).den : Int)
  have hnum2 : ((2 : Q') * a).num = 2 * a.num := rfl
  have hnumaa : ((a + a)).num = a.num * (a.den : Int) + a.num * (a.den : Int) := rfl
  have hden2a : (((2 : Q') * a).den : Int) = a.den := by
    rw [Q'.mul_den_cast (2 : Q') a]
    show ((1 : Int)) * (a.den : Int) = (a.den : Int)
    rw [Int.one_mul]
  rw [hnum2, hnumaa, hden2a, Q'.add_den_cast a a]
  -- (a.num*a.den + a.num*a.den) * a.den = (2*a.num) * (a.den*a.den)
  calc (a.num * (a.den : Int) + a.num * (a.den : Int)) * (a.den : Int)
      = (2 * (a.num * (a.den : Int))) * (a.den : Int) := by
        rw [← Int.two_mul]
    _ = 2 * a.num * ((a.den : Int) * (a.den : Int)) := by
        rw [Int.mul_assoc 2 (a.num * (a.den : Int)) (a.den : Int),
            Int.mul_assoc a.num (a.den : Int) (a.den : Int),
            Int.mul_assoc 2 a.num ((a.den : Int) * (a.den : Int))]

/-! ## The pointwise Schur identity at the level of rationals

For each approximation index `n` the two CReal expressions reduce
*definitionally* to a raw `Q'` identity in `u = (C 1).approx n = Q'.ofNat 1`,
`g = m₁.approx n`, `m = m₂.approx n`, `c0`, `c1`.  This lemma proves that
identity for any `u ≃ 1`. -/
theorem schur_q (u c0 c1 g m : Q') (hu : u.eqv 1) :
    (((c0*c0)*u + (2*(c0*c1))*g) + (c1*c1)*(u+m)).eqv
      ((0 + u*((c0+c1*g)*(c0+c1*g))) + (((u+m) + -(g*g))*(c1*c1))) := by
  -- ---- LHS → NF ---------------------------------------------------------
  -- (c0*c0)*u ≃ c0*c0
  have lA : ((c0*c0)*u).eqv (c0*c0) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (c0*c0) u 1 hu)
      (Q'.mul_one_eqv (c0*c0))
  -- (c1*c1)*(u+m) ≃ (c1*c1)*(1+m) ≃ (c1*c1)*1 + (c1*c1)*m ≃ c1*c1 + (c1*c1)*m
  have lC : ((c1*c1)*(u+m)).eqv ((c1*c1) + (c1*c1)*m) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (c1*c1) (u+m) (1+m)
        (Q'.add_eqv_congr_right u 1 m hu)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (c1*c1) 1 m) ?_
    exact Q'.add_eqv_congr_right ((c1*c1)*1) (c1*c1) ((c1*c1)*m)
      (Q'.mul_one_eqv (c1*c1))
  -- LHS ≃ (c0*c0 + (2*(c0*c1))*g) + (c1*c1 + (c1*c1)*m)
  have lhs : (((c0*c0)*u + (2*(c0*c1))*g) + (c1*c1)*(u+m)).eqv
      (((c0*c0) + (2*(c0*c1))*g) + ((c1*c1) + (c1*c1)*m)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ ((c1*c1)*(u+m))
        (Q'.add_eqv_congr_right ((c0*c0)*u) (c0*c0) ((2*(c0*c1))*g) lA))
      (Q'.add_eqv_congr_left ((c0*c0) + (2*(c0*c1))*g) _ _ lC)
  -- ---- RHS → NF ---------------------------------------------------------
  -- 0 + u*X ≃ u*X ≃ 1*X ≃ X,  X = (c0+c1*g)*(c0+c1*g)
  have rA0 : ((0 : Q') + u*((c0+c1*g)*(c0+c1*g))).eqv ((c0+c1*g)*(c0+c1*g)) := by
    refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv (u*((c0+c1*g)*(c0+c1*g)))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right u 1 ((c0+c1*g)*(c0+c1*g)) hu) ?_
    exact Q'.one_mul_eqv ((c0+c1*g)*(c0+c1*g))
  -- Expand X = (c0+c1*g)*(c0+c1*g)
  --   = (c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + (c1*g)*(c1*g))
  have rX : ((c0+c1*g)*(c0+c1*g)).eqv
      ((c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + (c1*g)*(c1*g))) := by
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul c0 (c1*g) (c0+c1*g)) ?_
    exact QPoly.q_add_congr
      (Q'.mul_add_eqv c0 c0 (c1*g))
      (Q'.mul_add_eqv (c1*g) c0 (c1*g))
  -- (((u+m) + -(g*g))*(c1*c1)) ≃ (((1+m) + -(g*g))*(c1*c1))
  --   ≃ ((1+m)*(c1*c1) + (-(g*g))*(c1*c1))
  --   ≃ ((1*(c1*c1) + m*(c1*c1)) + -((g*g)*(c1*c1)))
  --   ≃ ((c1*c1 + m*(c1*c1)) + -((g*g)*(c1*c1)))
  have rB : (((u+m) + -(g*g))*(c1*c1)).eqv
      (((c1*c1) + m*(c1*c1)) + -((g*g)*(c1*c1))) := by
    -- replace u by 1
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right ((u+m) + -(g*g)) ((1+m) + -(g*g)) (c1*c1)
        (Q'.add_eqv_congr_right (u+m) (1+m) (-(g*g))
          (Q'.add_eqv_congr_right u 1 m hu))) ?_
    -- distribute (a+b)*c
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul (1+m) (-(g*g)) (c1*c1)) ?_
    refine QPoly.q_add_congr ?_ ?_
    · -- (1+m)*(c1*c1) ≃ 1*(c1*c1) + m*(c1*c1) ≃ c1*c1 + m*(c1*c1)
      refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul 1 m (c1*c1)) ?_
      exact Q'.add_eqv_congr_right (1*(c1*c1)) (c1*c1) (m*(c1*c1))
        (Q'.one_mul_eqv (c1*c1))
    · -- (-(g*g))*(c1*c1) ≃ -((g*g)*(c1*c1))
      exact Q'.neg_mul_eqv (g*g) (c1*c1)
  -- RHS ≃ X' + B',  with X' the expansion above and B' the expansion above
  have rhs : ((0 + u*((c0+c1*g)*(c0+c1*g))) + (((u+m) + -(g*g))*(c1*c1))).eqv
      (((c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + (c1*g)*(c1*g)))
        + (((c1*c1) + m*(c1*c1)) + -((g*g)*(c1*c1)))) :=
    QPoly.q_add_congr (Q'.eqv_trans _ _ _ rA0 rX) rB
  -- ---- Now: show NF_LHS ≃ NF_RHS ---------------------------------------
  -- NF_LHS = (c0*c0 + (2*(c0*c1))*g) + (c1*c1 + (c1*c1)*m)
  -- NF_RHS = ((c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + (c1*g)*(c1*g)))
  --           + ((c1*c1 + m*(c1*c1)) + -((g*g)*(c1*c1)))
  --
  -- Key cancellations:
  --   (c1*g)*(c1*g) ≃ (g*g)*(c1*c1)   so  ... + X  and  ... + -X cancel.
  --   c0*(c1*g) + (c1*g)*c0 ≃ (2*(c0*c1))*g.
  --   (c1*c1)*m ≃ m*(c1*c1).
  -- We prove NF_RHS ≃ NF_LHS (then symm).
  -- First: (c1*g)*(c1*g) ≃ (g*g)*(c1*c1).
  have hsq : ((c1*g)*(c1*g)).eqv ((g*g)*(c1*c1)) := by
    -- (c1*g)*(c1*g) ≃ (c1*c1)*(g*g) ≃ (g*g)*(c1*c1)
    have e1 : ((c1*g)*(c1*g)).eqv ((c1*c1)*(g*g)) := by
      -- (c1*g)*(c1*g) ≃ c1*(g*(c1*g))   [assoc]
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c1 g (c1*g)) ?_
      -- g*(c1*g) ≃ c1*(g*g) :  g*(c1*g) ≃ (g*c1)*g ≃ (c1*g)*g ≃ c1*(g*g)
      have inner : (g*(c1*g)).eqv (c1*(g*g)) :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv g c1 g))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right (g*c1) (c1*g) g (Q'.mul_comm_eqv g c1))
            (Q'.mul_assoc_eqv c1 g g))
      -- c1*(g*(c1*g)) ≃ c1*(c1*(g*g)) ≃ (c1*c1)*(g*g)
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left c1 (g*(c1*g)) (c1*(g*g)) inner)
        (Q'.eqv_symm (Q'.mul_assoc_eqv c1 c1 (g*g)))
    exact Q'.eqv_trans _ _ _ e1 (Q'.mul_comm_eqv (c1*c1) (g*g))
  -- Cross-term: c0*(c1*g) + (c1*g)*c0 ≃ (2*(c0*c1))*g.
  -- c0*(c1*g) ≃ (c0*c1)*g  [symm assoc]
  have hcross1 : (c0*(c1*g)).eqv ((c0*c1)*g) := Q'.eqv_symm (Q'.mul_assoc_eqv c0 c1 g)
  -- (c1*g)*c0 ≃ (c0*c1)*g :  (c1*g)*c0 ≃ c0*(c1*g) ≃ (c0*c1)*g
  have hcross2 : ((c1*g)*c0).eqv ((c0*c1)*g) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (c1*g) c0) hcross1
  -- (2*(c0*c1))*g ≃ (c0*c1)*g + (c0*c1)*g  [since 2*x ≃ x+x is NOT a lemma;
  -- instead expand: (2*(c0*c1))*g = ((c0*c1 + c0*c1))*g? No — 2 is a literal.
  -- We instead show c0*(c1*g) + (c1*g)*c0 ≃ (2*(c0*c1))*g directly.]
  have hcross : (c0*(c1*g) + (c1*g)*c0).eqv ((2*(c0*c1))*g) := by
    -- LHS ≃ (c0*c1)*g + (c0*c1)*g
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr hcross1 hcross2) ?_
    -- (c0*c1)*g + (c0*c1)*g ≃ ((c0*c1)+(c0*c1))*g ≃ (2*(c0*c1))*g
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (QPoly.q_add_mul (c0*c1) (c0*c1) g)) ?_
    exact Q'.mul_eqv_congr_right ((c0*c1)+(c0*c1)) (2*(c0*c1)) g (twoMul (c0*c1))
  -- m*(c1*c1) ≃ (c1*c1)*m
  have hm : (m*(c1*c1)).eqv ((c1*c1)*m) := Q'.mul_comm_eqv m (c1*c1)
  -- ---- NF_RHS ≃ NF_LHS --------------------------------------------------
  -- abbreviations
  -- S := (g*g)*(c1*c1)
  -- P := c0*c0 + c0*(c1*g);  W := (c1*g)*c0;  Q := c1*c1 + (c1*c1)*m
  -- Step A: replace (c1*g)*(c1*g) by S and m*(c1*c1) by (c1*c1)*m in NF_RHS.
  have stepA : (((c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + (c1*g)*(c1*g)))
        + ((c1*c1 + m*(c1*c1)) + -((g*g)*(c1*c1)))).eqv
      (((c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + ((g*g)*(c1*c1))))
        + ((c1*c1 + (c1*c1)*m) + -((g*g)*(c1*c1)))) :=
    QPoly.q_add_congr
      (Q'.add_eqv_congr_left (c0*c0 + c0*(c1*g)) _ _
        (Q'.add_eqv_congr_left ((c1*g)*c0) _ _ hsq))
      (Q'.add_eqv_congr_right _ _ (-((g*g)*(c1*c1)))
        (Q'.add_eqv_congr_left (c1*c1) _ _ hm))
  -- Step B: regroup  (P+(W+S)) + (Q'+(-S))  ≃  P + (W+Q')   (cancel S, -S)
  have stepB : (((c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + ((g*g)*(c1*c1))))
        + ((c1*c1 + (c1*c1)*m) + -((g*g)*(c1*c1)))).eqv
      ((c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + (c1*c1 + (c1*c1)*m))) := by
    -- (P+(W+S)) + (Q'+(-S)) ≃ P + ((W+S)+(Q'+(-S)))  [assoc]
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (c0*c0 + c0*(c1*g))
        ((c1*g)*c0 + ((g*g)*(c1*c1)))
        ((c1*c1 + (c1*c1)*m) + -((g*g)*(c1*c1)))) ?_
    -- inner: (W+S)+(Q'+(-S)) ≃ (W+Q') + (S+(-S)) ≃ (W+Q')+0 ≃ W+Q'
    refine Q'.add_eqv_congr_left (c0*c0 + c0*(c1*g)) _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_swap_inner ((c1*g)*c0) ((g*g)*(c1*c1))
        (c1*c1 + (c1*c1)*m) (-((g*g)*(c1*c1)))) ?_
    -- ((W)+(Q')) + (S + -S) ≃ (W+Q') + 0 ≃ W+Q'
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left ((c1*g)*c0 + (c1*c1 + (c1*c1)*m)) _ 0
        (Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv ((g*g)*(c1*c1)) (-((g*g)*(c1*c1))))
          (Q'.neg_add_self_eqv ((g*g)*(c1*c1))))) ?_
    exact QPoly.q_add_zero_eqv ((c1*g)*c0 + (c1*c1 + (c1*c1)*m))
  -- Step C:  P + (W + Q')  ≃  (c0*c0 + (2*(c0*c1))*g) + Q'
  have stepC : ((c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + (c1*c1 + (c1*c1)*m))).eqv
      ((c0*c0 + (2*(c0*c1))*g) + (c1*c1 + (c1*c1)*m)) := by
    -- (c0*c0 + c0*(c1*g)) + (W + Q') ≃ c0*c0 + (c0*(c1*g) + (W + Q'))  [assoc]
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (c0*c0) (c0*(c1*g))
        ((c1*g)*c0 + (c1*c1 + (c1*c1)*m))) ?_
    -- inner: c0*(c1*g) + ((c1*g)*c0 + Q') ≃ (c0*(c1*g)+(c1*g)*c0) + Q' ≃ (2*(c0*c1))*g + Q'
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c0*c0) _ _
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (c0*(c1*g)) ((c1*g)*c0)
            (c1*c1 + (c1*c1)*m)))
          (Q'.add_eqv_congr_right _ _ (c1*c1 + (c1*c1)*m) hcross))) ?_
    -- c0*c0 + ((2*(c0*c1))*g + Q') ≃ (c0*c0 + (2*(c0*c1))*g) + Q'  [symm assoc]
    exact Q'.eqv_symm (Q'.add_assoc_eqv (c0*c0) ((2*(c0*c1))*g) (c1*c1 + (c1*c1)*m))
  -- Combine: NF_RHS ≃ NF_LHS
  have nf : (((c0*c0 + c0*(c1*g)) + ((c1*g)*c0 + (c1*g)*(c1*g)))
        + ((c1*c1 + m*(c1*c1)) + -((g*g)*(c1*c1)))).eqv
      ((c0*c0 + (2*(c0*c1))*g) + (c1*c1 + (c1*c1)*m)) :=
    Q'.eqv_trans _ _ _ stepA (Q'.eqv_trans _ _ _ stepB stepC)
  -- Final: LHS ≃ NF_LHS ≃ NF_RHS ≃ RHS
  exact Q'.eqv_trans _ _ _ lhs (Q'.eqv_trans _ _ _ (Q'.eqv_symm nf) (Q'.eqv_symm rhs))

/-! ## The SOS certificate and the Schur identity -/

/-- The two CReal pivots of the LDLᵀ decomposition: `P 0 = 1`, `P 1 = D₁`. -/
def Pcert (t : Q') (ht : (0:Q') ≤ t) : Nat → CReal :=
  fun k => match k with
  | 0 => Pivot2.C 1
  | _ => Pivot2.pivotGram t ht

/-- The two linear functionals: `L 0 = c0 + c1·m₁`, `L 1 = c1`. -/
def Lcert (t : Q') (ht : (0:Q') ≤ t) (c0 c1 : Q') : Nat → CReal :=
  fun k => match k with
  | 0 => CReal.add (CReal.ofQ' c0) (CReal.mul (CReal.ofQ' c1) (Pivot2.m1 t ht))
  | _ => CReal.ofQ' c1

/-- Both pivots are nonnegative. -/
theorem Pcert_nonneg (t : Q') (ht : (0:Q') ≤ t) :
    ∀ k, ExpPos.geRat (Pcert t ht k) 0
  | 0 => show ExpPos.geRat (CReal.ofQ' (Q'.ofNat 1)) 0 from
      SumOfSquares.geRat_ofQ'_nonneg (by decide)
  | (_ + 1) => Pivot2.pivotGram_nonneg t ht

/-- **The Schur (completing-the-square) identity:** `E(a²)` equals the
nonnegatively-weighted sum of squares `Σ_{k<2} P_k · L_k²`. -/
theorem schur_identity (t : Q') (ht : (0:Q') ≤ t) (c0 c1 : Q') :
    CReal.Equiv (form2 t ht c0 c1)
      (CReal.csum (fun k => CReal.mul (Pcert t ht k)
        (CReal.mul (Lcert t ht c0 c1 k) (Lcert t ht c0 c1 k))) 2) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  -- Both sides reduce definitionally to the raw Q' identity proved in schur_q,
  -- with u = (C 1).approx n = Q'.ofNat 1, g = m₁.approx n, m = m₂.approx n.
  exact schur_q (Q'.ofNat 1) c0 c1 ((Pivot2.m1 t ht).approx n)
    ((Pivot2.m2 t ht).approx n) (by decide)

/-- **Full SU(2) heat-kernel 2×2 positive-semidefiniteness:** the quadratic
form `E(a²) = c0²·1 + 2c0c1·m₁ + c1²·(1+m₂)` is nonnegative for every
`c0, c1`.  Completing the square `E(a²) = (c0+c1·m₁)² + D₁·c1²` with both
pivots `≥ 0` (the constant `1` and the Schur complement `D₁`) certifies it. -/
theorem form2_nonneg (t : Q') (ht : (0:Q') ≤ t) (c0 c1 : Q') :
    ExpPos.geRat (form2 t ht c0 c1) 0 :=
  SU3CharFactor.geRat_of_equiv (schur_identity t ht c0 c1)
    (SumOfSquares.geRat_sos_creal (Pcert t ht) (Lcert t ht c0 c1)
      (Pcert_nonneg t ht) 2)

end YMGap.Continuum.Pivot2

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Pivot2.form2_nonneg
