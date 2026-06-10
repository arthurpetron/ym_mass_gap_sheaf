/-
The polynomial identity `1 + 3x⁴ − 4x³ ≃ (1−x)²(3x²+2x+1)` at the `CReal`
level, for any `CReal x`.

`CReal.Equiv` reduces (via `SumOfSquares.Equiv_of_approx_eqv`) to a
pointwise `Q'` identity in `q := x.approx n`.  Both raw approx expressions
are reified to the reflective `QPoly.eval`-Horner forms, and the middle is
discharged by `QPoly.pivot2_factor` (a `decide` on coefficient lists).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.Pivot2Defs
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.Pivot2

open YMGap.Constructive

/-! ## Atoms for reifying raw `Q'` products into Horner `eval` forms

The systematic engine: a raw monomial `q*(q*(…))` is the `eval` of the
list `[0,1]` raised to a `pmul` power.  Rather than chase Horner nests by
hand, we build each raw side from the `eval`-homomorphism lemmas
(`eval_pmul`, `eval_padd`, `eval_pscale`, `eval_pneg`) run *backwards*. -/

/-- Congruence for `*` on both arguments. -/
theorem q_mul_congr {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- `eval [0,1] q ≃ q`. -/
theorem evalX (q : Q') : (QPoly.eval [0, 1] q).eqv q := by
  show ((0 : Q') + q * (1 + q * 0)).eqv q
  refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv (q * (1 + q * 0))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left q (1 + q * 0) 1
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 (q * 0) 0 (QPoly.q_mul_zero q))
        (QPoly.q_add_zero_eqv 1))) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q 1) (Q'.one_mul_eqv q)

/-- `powList (k+1)` = the coefficient list of `q^(k+1)` (`[0,1]` to the
`pmul`-power `k+1`), with `powList 0 = [0,1]` (so index `k` is `q^(k+1)`). -/
def powList : Nat → QPoly.Poly
  | 0 => [0, 1]
  | (k + 1) => QPoly.pmul [0, 1] (powList k)

/-- Raw monomial `q^(k+1)` with the right-nested association `q*(q*(…*q))`. -/
def rawPow (q : Q') : Nat → Q'
  | 0 => q
  | (k + 1) => q * rawPow q k

/-- `eval (powList k) q ≃ rawPow q k` — the monomial reification. -/
theorem eval_powList (q : Q') : ∀ k, (QPoly.eval (powList k) q).eqv (rawPow q k)
  | 0 => evalX q
  | (k + 1) =>
      Q'.eqv_trans _ _ _ (QPoly.eval_pmul [0, 1] (powList k) q)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (evalX q))
          (Q'.mul_eqv_congr_left q _ _ (eval_powList q k)))

/-! ## LHS reification -/

/-- LHS combinator list: `1 + 3·q⁴ − 4·q³`. -/
def Plhs : QPoly.Poly :=
  QPoly.padd (QPoly.padd [Q'.ofNat 1] (QPoly.pscale (Q'.ofNat 3) (powList 3)))
    (QPoly.pneg (QPoly.pscale (Q'.ofNat 4) (powList 2)))

/-- `eval Plhs q` reduces to the raw `pivotPoly` approx form. -/
theorem eval_Plhs (q : Q') :
    (QPoly.eval Plhs q).eqv
      ((Q'.ofNat 1 + Q'.ofNat 3 * (q * (q * (q * q))))
        + -(Q'.ofNat 4 * (q * (q * q)))) := by
  refine Q'.eqv_trans _ _ _
    (QPoly.eval_padd (QPoly.padd [Q'.ofNat 1] (QPoly.pscale (Q'.ofNat 3) (powList 3)))
      (QPoly.pneg (QPoly.pscale (Q'.ofNat 4) (powList 2))) q) ?_
  refine QPoly.q_add_congr ?_ ?_
  · -- `eval (padd [1] (pscale 3 (powList 3))) q ≃ 1 + 3*q⁴`
    refine Q'.eqv_trans _ _ _
      (QPoly.eval_padd [Q'.ofNat 1] (QPoly.pscale (Q'.ofNat 3) (powList 3)) q) ?_
    refine QPoly.q_add_congr ?_ ?_
    · -- `eval [1] q ≃ 1`
      show (Q'.ofNat 1 + q * 0).eqv (Q'.ofNat 1)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (QPoly.q_mul_zero q)) (QPoly.q_add_zero_eqv _)
    · -- `eval (pscale 3 (powList 3)) q ≃ 3*q⁴`
      refine Q'.eqv_trans _ _ _ (QPoly.eval_pscale (Q'.ofNat 3) (powList 3) q) ?_
      exact Q'.mul_eqv_congr_left _ _ _ (eval_powList q 3)
  · -- `eval (pneg (pscale 4 (powList 2))) q ≃ -(4*q³)`
    refine Q'.eqv_trans _ _ _ (QPoly.eval_pneg (QPoly.pscale (Q'.ofNat 4) (powList 2)) q) ?_
    refine Q'.neg_eqv_congr _ _ ?_
    refine Q'.eqv_trans _ _ _ (QPoly.eval_pscale (Q'.ofNat 4) (powList 2) q) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (eval_powList q 2)

/-- `Plhs` and the canonical list `[1,0,0,-4,3]` evaluate equally. -/
theorem Plhs_eq_canon (q : Q') :
    (QPoly.eval Plhs q).eqv (QPoly.eval [1, 0, 0, -(Q'.ofNat 4), Q'.ofNat 3] q) :=
  QPoly.poly_eqv _ _ q (by decide)

/-! ## RHS reification -/

/-- `eval [1,-1] q ≃ 1 + -q` — the linear factor `(1 − q)`. -/
theorem eval_oneSub (q : Q') : (QPoly.eval [1, -(1 : Q')] q).eqv (Q'.ofNat 1 + -q) := by
  show ((1 : Q') + q * (-(1 : Q') + q * 0)).eqv (Q'.ofNat 1 + -q)
  refine QPoly.q_add_congr (Q'.eqv_refl (1 : Q')) ?_
  -- `q * (-1 + q*0) ≃ q*(-1) ≃ -(q*1) ≃ -q`
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left q (-(1 : Q') + q * 0) (-(1 : Q'))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (-(1 : Q')) (q * 0) 0 (QPoly.q_mul_zero q))
        (QPoly.q_add_zero_eqv (-(1 : Q'))))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv q 1) ?_
  exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv q)

/-- `eval [1,2,3] q ≃ (3·q² + 2·q) + 1` — the quadratic factor `3q²+2q+1`. -/
theorem eval_quad (q : Q') :
    (QPoly.eval [1, Q'.ofNat 2, Q'.ofNat 3] q).eqv
      ((Q'.ofNat 3 * (q * q) + Q'.ofNat 2 * q) + Q'.ofNat 1) := by
  -- LHS Horner: `1 + q*(2 + q*(3 + q*0))`
  show ((1 : Q') + q * (Q'.ofNat 2 + q * (Q'.ofNat 3 + q * 0))).eqv
      ((Q'.ofNat 3 * (q * q) + Q'.ofNat 2 * q) + Q'.ofNat 1)
  -- Reduce inner `3 + q*0 ≃ 3`, then expand.
  have hi : (Q'.ofNat 3 + q * 0).eqv (Q'.ofNat 3) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (QPoly.q_mul_zero q))
      (QPoly.q_add_zero_eqv _)
  -- `q*(2 + q*(3 + q*0)) ≃ q*(2 + q*3) ≃ q*2 + q*(q*3) ≃ 2*q + 3*(q*q)`
  have hmul : (q * (Q'.ofNat 2 + q * (Q'.ofNat 3 + q * 0))).eqv
      (Q'.ofNat 2 * q + Q'.ofNat 3 * (q * q)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q _ (Q'.ofNat 2 + q * Q'.ofNat 3)
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left q _ _ hi))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv q (Q'.ofNat 2) (q * Q'.ofNat 3)) ?_
    refine QPoly.q_add_congr (Q'.mul_comm_eqv q (Q'.ofNat 2)) ?_
    -- `q*(q*3) ≃ (q*q)*3 ≃ 3*(q*q)`
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q q (Q'.ofNat 3))) ?_
    exact Q'.mul_comm_eqv (q * q) (Q'.ofNat 3)
  -- Now `1 + (2*q + 3*(q*q)) ≃ (3*(q*q) + 2*q) + 1`.
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ hmul) ?_
  -- `1 + (2*q + 3*(q*q))`  →  `(3*(q*q) + 2*q) + 1`
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (1 : Q') (Q'.ofNat 2 * q + Q'.ofNat 3 * (q * q))) ?_
  refine Q'.add_eqv_congr_right _ _ _ ?_
  exact Q'.add_comm_eqv (Q'.ofNat 2 * q) (Q'.ofNat 3 * (q * q))

/-- RHS combinator list: `(1−q)²·(3q²+2q+1)` — exactly the `pivot2_factor`
factorization list. -/
def Prhs : QPoly.Poly :=
  QPoly.pmul (QPoly.pmul [1, -(1 : Q')] [1, -(1 : Q')]) [1, Q'.ofNat 2, Q'.ofNat 3]

/-- `eval Prhs q` reduces to the raw `sosProduct` approx form. -/
theorem eval_Prhs (q : Q') :
    (QPoly.eval Prhs q).eqv
      (((Q'.ofNat 1 + -q) * (Q'.ofNat 1 + -q))
        * ((Q'.ofNat 3 * (q * q) + Q'.ofNat 2 * q) + Q'.ofNat 1)) := by
  refine Q'.eqv_trans _ _ _
    (QPoly.eval_pmul (QPoly.pmul [1, -(1 : Q')] [1, -(1 : Q')])
      [1, Q'.ofNat 2, Q'.ofNat 3] q) ?_
  refine q_mul_congr ?_ (eval_quad q)
  -- `eval (pmul [1,-1][1,-1]) q ≃ (1+-q)*(1+-q)`
  refine Q'.eqv_trans _ _ _ (QPoly.eval_pmul [1, -(1 : Q')] [1, -(1 : Q')] q) ?_
  exact q_mul_congr (eval_oneSub q) (eval_oneSub q)

/-! ## The pointwise `Q'` identity and the `CReal` lift -/

/-- The per-approximation `Q'` identity: `(pivotPoly x).approx n ≃
(sosProduct x).approx n`.  Chains: raw LHS ≃ `eval Plhs` ≃ `eval [1,0,0,-4,3]`
≃ (`pivot2_factor`) `eval (pmul…)` ≃ `eval Prhs` ≃ raw RHS. -/
theorem pivotPoly_eqv_sos_approx (x : CReal) (n : Nat) :
    ((pivotPoly x).approx n).eqv ((sosProduct x).approx n) :=
  -- `q := x.approx n`.  Each step below holds *definitionally* on the raw
  -- ends (`(pivotPoly x).approx n` unfolds to `eval_Plhs`'s RHS, etc.).
  Q'.eqv_trans _ _ _
    -- raw LHS  ≃  eval [1,0,0,-4,3] q
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_Plhs (x.approx n))) (Plhs_eq_canon (x.approx n)))
    (Q'.eqv_trans _ _ _ (QPoly.pivot2_factor (x.approx n))
      -- eval (pmul…) q  ≃  raw RHS
      (eval_Prhs (x.approx n)))

/-- **The pivot SOS-factorization identity at the `CReal` level:**
`1 + 3x⁴ − 4x³ ≃ (1−x)²(3x²+2x+1)` for every constructive real `x`. -/
theorem pivotPoly_eqv_sos (x : CReal) :
    CReal.Equiv (pivotPoly x) (sosProduct x) :=
  SumOfSquares.Equiv_of_approx_eqv (pivotPoly_eqv_sos_approx x)

end YMGap.Continuum.Pivot2

/-! ## Axiom-dependency gate (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Pivot2.pivotPoly_eqv_sos
