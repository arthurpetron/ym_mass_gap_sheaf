/-
# Exact positive five-node Haar quadrature on three SU(2) modes

The symmetric rational rule supported at `0`, plus-or-minus `1/2`, and
plus-or-minus `1`, with weights
`1/4` at zero, `1/3` at each half-node, and `1/24` at each endpoint, matches
the normalized semicircle moments through degree four.  It is therefore exact
on the Gram matrix of `chi0, chi1, chi2`, while remaining a positive functional
on every polynomial square.

This is still finite-sector quadrature.  The exact fence `H5(U6)=1` prevents
its use as the all-mode Haar functional, which must annihilate every
nontrivial character.
-/

import YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar

namespace YMGap.Continuum.SU2ClassPolynomialFiveNodeHaar

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

def half : Q' := Q'.mkPos 1 2 (by decide)
def endpointWeight : Q' := Q'.mkPos 1 24 (by decide)
def halfWeight : Q' := Q'.mkPos 1 3 (by decide)
def zeroWeight : Q' := Q'.mkPos 1 4 (by decide)

/-- Positive symmetric rational quadrature, exact through degree four. -/
def fiveNodeHaar (p : Poly) : Q' :=
  endpointWeight * (eval p 1 + eval p (-1)) +
    (halfWeight * (eval p half + eval p (-half)) +
      zeroWeight * eval p 0)

theorem fiveNodeHaar_congr {p q : Poly} (h : PolyEqv p q) :
    fiveNodeHaar p ≈ fiveNodeHaar q := by
  unfold fiveNodeHaar
  exact q_add_congr
    (Q'.mul_eqv_congr_left endpointWeight _ _
      (q_add_congr (h 1) (h (-1))))
    (q_add_congr
      (Q'.mul_eqv_congr_left halfWeight _ _
        (q_add_congr (h half) (h (-half))))
      (Q'.mul_eqv_congr_left zeroWeight _ _ (h 0)))

theorem fiveNodeHaar_add (p q : Poly) :
    fiveNodeHaar (padd p q) ≈ fiveNodeHaar p + fiveNodeHaar q := by
  unfold fiveNodeHaar
  refine Q'.eqv_trans _ _ _
    (q_add_congr
      (Q'.mul_eqv_congr_left endpointWeight _ _
        (q_add_congr (eval_padd p q 1) (eval_padd p q (-1))))
      (q_add_congr
        (Q'.mul_eqv_congr_left halfWeight _ _
          (q_add_congr (eval_padd p q half) (eval_padd p q (-half))))
        (Q'.mul_eqv_congr_left zeroWeight _ _ (eval_padd p q 0)))) ?_
  ring_qeqv

theorem fiveNodeHaar_scale (a : Q') (p : Poly) :
    fiveNodeHaar (pscale a p) ≈ a * fiveNodeHaar p := by
  unfold fiveNodeHaar
  refine Q'.eqv_trans _ _ _
    (q_add_congr
      (Q'.mul_eqv_congr_left endpointWeight _ _
        (q_add_congr (eval_pscale a p 1) (eval_pscale a p (-1))))
      (q_add_congr
        (Q'.mul_eqv_congr_left halfWeight _ _
          (q_add_congr (eval_pscale a p half) (eval_pscale a p (-half))))
        (Q'.mul_eqv_congr_left zeroWeight _ _ (eval_pscale a p 0)))) ?_
  ring_qeqv

theorem fiveNodeHaar_one : fiveNodeHaar pone ≈ 1 := by decide

/-- Positivity holds on every polynomial square, not just on retained modes. -/
theorem fiveNodeHaar_square_nonneg (p : Poly) :
    (0 : Q') ≤ fiveNodeHaar (pmul (pstar p) p) := by
  let target :=
    endpointWeight * (eval p 1 * eval p 1 + eval p (-1) * eval p (-1)) +
      (halfWeight *
          (eval p half * eval p half + eval p (-half) * eval p (-half)) +
        zeroWeight * (eval p 0 * eval p 0))
  have heq : fiveNodeHaar (pmul (pstar p) p) ≈ target := by
    unfold fiveNodeHaar pstar target
    exact q_add_congr
      (Q'.mul_eqv_congr_left endpointWeight _ _
        (q_add_congr (eval_pmul p p 1) (eval_pmul p p (-1))))
      (q_add_congr
        (Q'.mul_eqv_congr_left halfWeight _ _
          (q_add_congr (eval_pmul p p half) (eval_pmul p p (-half))))
        (Q'.mul_eqv_congr_left zeroWeight _ _ (eval_pmul p p 0)))
  have hend : (0 : Q') ≤
      eval p 1 * eval p 1 + eval p (-1) * eval p (-1) :=
    Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg _)
      (SumOfSquares.q_mul_self_nonneg _)
  have hhalf : (0 : Q') ≤
      eval p half * eval p half + eval p (-half) * eval p (-half) :=
    Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg _)
      (SumOfSquares.q_mul_self_nonneg _)
  have h0 : (0 : Q') ≤ eval p 0 * eval p 0 :=
    SumOfSquares.q_mul_self_nonneg _
  have htarget : (0 : Q') ≤ target := by
    unfold target
    exact Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide) hend)
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide) hhalf)
        (Q'.mul_nonneg _ _ (by decide) h0))
  exact Q'.le_trans' _ _ _ htarget
    (Q'.le_of_eqv (Q'.eqv_symm heq))

/-! ## Exact three-mode Haar table -/

theorem fiveNodeHaar_chebPoly_zero : fiveNodeHaar (chebPoly 0) ≈ 1 := by decide
theorem fiveNodeHaar_chebPoly_one : fiveNodeHaar (chebPoly 1) ≈ 0 := by decide
theorem fiveNodeHaar_chebPoly_two : fiveNodeHaar (chebPoly 2) ≈ 0 := by decide
theorem fiveNodeHaar_chebPoly_three : fiveNodeHaar (chebPoly 3) ≈ 0 := by decide
theorem fiveNodeHaar_chebPoly_four : fiveNodeHaar (chebPoly 4) ≈ 0 := by decide

def modeZero : Fin 3 := ⟨0, by decide⟩
def modeOne : Fin 3 := ⟨1, by decide⟩
def modeTwo : Fin 3 := ⟨2, by decide⟩

theorem fin_three_cases (i : Fin 3) :
    i = modeZero ∨ i = modeOne ∨ i = modeTwo := by
  cases i with
  | mk n hn =>
      cases n with
      | zero => exact Or.inl rfl
      | succ n =>
          cases n with
          | zero => exact Or.inr (Or.inl rfl)
          | succ n =>
              have hn0 : n = 0 := by omega
              subst n
              exact Or.inr (Or.inr rfl)

def polyMode (i : Fin 3) : Poly := chebPoly i.val

/-- The first three characters have the exact identity Haar Gram matrix. -/
theorem fiveNodeHaar_polyMode_delta (i j : Fin 3) :
    fiveNodeHaar (pmul (polyMode i) (polyMode j)) ≈
      if i.val = j.val then 1 else 0 := by
  rcases fin_three_cases i with hi | hi | hi <;> subst i
  <;> rcases fin_three_cases j with hj | hj | hj <;> subst j
  <;> decide

/-! ## Exact scope fence -/

/-- The next even character is already wrong: this is not full Haar. -/
theorem fiveNodeHaar_chebPoly_six :
    fiveNodeHaar (chebPoly 6) ≈ (1 : Q') := by decide

theorem fiveNodeHaar_not_full_character_Haar :
    ¬ (fiveNodeHaar (chebPoly 6) ≈ (0 : Q')) := by decide

end YMGap.Continuum.SU2ClassPolynomialFiveNodeHaar

#print axioms YMGap.Continuum.SU2ClassPolynomialFiveNodeHaar.fiveNodeHaar_congr
#print axioms YMGap.Continuum.SU2ClassPolynomialFiveNodeHaar.fiveNodeHaar_add
#print axioms YMGap.Continuum.SU2ClassPolynomialFiveNodeHaar.fiveNodeHaar_scale
#print axioms YMGap.Continuum.SU2ClassPolynomialFiveNodeHaar.fiveNodeHaar_square_nonneg
#print axioms YMGap.Continuum.SU2ClassPolynomialFiveNodeHaar.fiveNodeHaar_polyMode_delta
#print axioms YMGap.Continuum.SU2ClassPolynomialFiveNodeHaar.fiveNodeHaar_chebPoly_six
#print axioms YMGap.Continuum.SU2ClassPolynomialFiveNodeHaar.fiveNodeHaar_not_full_character_Haar
