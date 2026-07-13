/-
# Exact positive two-node Haar quadrature on the associative SU(2) carrier

`SU2ClassPolynomialAlgebra` replaces the nonassociative lowest-channel carrier
by the genuine rational class-polynomial algebra.  This module supplies the
smallest nondegenerate positive functional on that carrier which is exact on
the retained modes `chi0, chi1`: the symmetric two-node quadrature

  H2(p) = (p(1/2) + p(-1/2))/2.

It is normalized, respects extensional polynomial equality, is linear, and is
positive on every square.  Its Gram matrix on `chi0,chi1` is exactly the
identity, hence it agrees unconditionally with the rational two-mode GNS form
already used by `SU2FaithfulTwoModeGNSConnector`.  Conditional only on the
genuine semicircle-value theorem, the physical midpoint-Riemann Gram agrees
with this same functional.

This is a finite-sector quadrature, not full Haar integration.  The exact
fence `H2(chebPoly 4) = -1` shows that it already fails the Haar character
moment at the next even mode.  It therefore cannot discharge the all-mode
Peter--Weyl/Haar residual or the interacting Wilson-state identification.
-/

import YMGap.Continuum.SU2ClassPolynomialAlgebra
import YMGap.Continuum.SU2FaithfulTwoModeGNSConnector

namespace YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2FaithfulTwoModeGNSConnector
open YMGap.Continuum.SU2FiniteHaarRiemannTwoMode

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-- The exact node `1/2`. -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-- Symmetric two-node quadrature on the rational class-polynomial carrier. -/
def twoNodeHaar (p : Poly) : Q' :=
  half * (eval p half + eval p (-half))

/-- The quadrature descends through the extensional equality used by the
associative polynomial carrier. -/
theorem twoNodeHaar_congr {p q : Poly} (h : PolyEqv p q) :
    twoNodeHaar p ≈ twoNodeHaar q := by
  unfold twoNodeHaar
  exact Q'.mul_eqv_congr_left half _ _ (q_add_congr (h half) (h (-half)))

/-- Exact additivity. -/
theorem twoNodeHaar_add (p q : Poly) :
    twoNodeHaar (padd p q) ≈ twoNodeHaar p + twoNodeHaar q := by
  unfold twoNodeHaar
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left half _ _
      (q_add_congr (eval_padd p q half) (eval_padd p q (-half)))) ?_
  ring_qeqv

/-- Exact rational homogeneity. -/
theorem twoNodeHaar_scale (a : Q') (p : Poly) :
    twoNodeHaar (pscale a p) ≈ a * twoNodeHaar p := by
  unfold twoNodeHaar
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left half _ _
      (q_add_congr (eval_pscale a p half) (eval_pscale a p (-half)))) ?_
  ring_qeqv

/-- Normalization on the algebra unit. -/
theorem twoNodeHaar_one : twoNodeHaar pone ≈ 1 := by
  decide

/-- Positivity on every polynomial square. -/
theorem twoNodeHaar_square_nonneg (p : Poly) :
    (0 : Q') ≤ twoNodeHaar (pmul (pstar p) p) := by
  have heq : twoNodeHaar (pmul (pstar p) p) ≈
      half * (eval p half * eval p half + eval p (-half) * eval p (-half)) := by
    unfold twoNodeHaar pstar
    exact Q'.mul_eqv_congr_left half _ _
      (q_add_congr (eval_pmul p p half) (eval_pmul p p (-half)))
  have hsum : (0 : Q') ≤
      eval p half * eval p half + eval p (-half) * eval p (-half) :=
    Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg _)
      (SumOfSquares.q_mul_self_nonneg _)
  have hpos : (0 : Q') ≤
      half * (eval p half * eval p half + eval p (-half) * eval p (-half)) :=
    Q'.mul_nonneg _ _ (by decide) hsum
  exact Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv (Q'.eqv_symm heq))

/-! ## Exact retained-character table -/

theorem twoNodeHaar_chi0 : twoNodeHaar chi0 ≈ 1 := by decide
theorem twoNodeHaar_chi1 : twoNodeHaar chi1 ≈ 0 := by decide
theorem twoNodeHaar_chi2 : twoNodeHaar chi2 ≈ 0 := by decide

theorem twoNodeHaar_chi0_sq : twoNodeHaar (pmul chi0 chi0) ≈ 1 := by decide
theorem twoNodeHaar_chi0_chi1 : twoNodeHaar (pmul chi0 chi1) ≈ 0 := by decide
theorem twoNodeHaar_chi1_sq : twoNodeHaar (pmul chi1 chi1) ≈ 1 := by decide

/-- The two retained modes as actual polynomials in the associative carrier. -/
def polyMode (i : Fin 2) : Poly :=
  if i.val = 0 then chi0 else chi1

/-- Their Gram matrix under the exact quadrature is the identity. -/
theorem twoNodeHaar_polyMode_delta (i j : Fin 2) :
    twoNodeHaar (pmul (polyMode i) (polyMode j)) ≈
      if i.val = j.val then 1 else 0 := by
  rcases fin_two_cases i with hi | hi <;> subst i
  <;> rcases fin_two_cases j with hj | hj <;> subst j
  <;> decide

/-- The quadrature is exactly the nondegenerate rational two-mode GNS form. -/
theorem twoNodeHaar_matches_faithful_gns (i j : Fin 2) :
    twoNodeHaar (pmul (polyMode i) (polyMode j)) ≈
      faithfulModeGNS.B (modeVector i) (modeVector j) :=
  Q'.eqv_trans _ _ _ (twoNodeHaar_polyMode_delta i j)
    (Q'.eqv_symm (mode_gram i j))

/-- Once the genuine semicircle normalization is established, the normalized
midpoint-Riemann Gram and this exact polynomial functional are the same state
on the retained two-mode sector. -/
theorem normalizedMoment_matches_twoNodeHaar
    (hsemi : SemicircleValue.SemiConvergesToHalfPi) (i j : Fin 2) :
    CReal.Equiv (normalizedMoment i j)
      (CReal.ofQ' (twoNodeHaar (pmul (polyMode i) (polyMode j)))) := by
  refine CReal.Equiv.trans
    (faithful_normalized_moment_matches_gns hsemi i j) ?_
  exact CReal.Equiv.symm
    (CReal.ofQ'_equiv_of_eqv (twoNodeHaar_matches_faithful_gns i j))

/-! ## Exact scope fence -/

/-- The two-node rule fails at the next even character: `H2(U4) = -1`. -/
theorem twoNodeHaar_chebPoly_four :
    twoNodeHaar (chebPoly 4) ≈ (-1 : Q') := by decide

/-- Therefore this finite quadrature is not the full SU(2) Haar functional,
which annihilates every nontrivial character. -/
theorem twoNodeHaar_not_full_character_Haar :
    ¬ (twoNodeHaar (chebPoly 4) ≈ (0 : Q')) := by decide

end YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar

#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.twoNodeHaar_congr
#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.twoNodeHaar_add
#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.twoNodeHaar_scale
#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.twoNodeHaar_square_nonneg
#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.twoNodeHaar_polyMode_delta
#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.twoNodeHaar_matches_faithful_gns
#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.normalizedMoment_matches_twoNodeHaar
#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.twoNodeHaar_chebPoly_four
#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.twoNodeHaar_not_full_character_Haar
