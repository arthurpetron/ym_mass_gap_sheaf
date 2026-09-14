/-
# Multiplication and commutation of ORIGINAL continuous actions

Uniform Bernstein product estimates identify the already-constructed
product limit with every supplied continuous symbol H agreeing with F*G
on rational [0,1]. Thus H(T2)x = F(T2)G(T2)x on original represented
cyclic states. The H data are symbol presentation data, not a physical
or spectral premise. A general constructor for H's continuity data is
not asserted here. Commutation needs no H and holds for every F and G.

Every comparison uses one explicit stage for ALL rational points of [0,1].
No replacement carrier, scalar spectral model or image-limit premise is
used. Fixed SU(2) nome and spacing; no physical-scale or continuum closure.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing (bernsteinPoly_abs_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows

theorem mul_difference_bound (a b c d A D delta : Q')
    (hA : (0 : Q')≤A) (hD : (0 : Q')≤D)
    (ha : Q'.abs a≤A) (hd : Q'.abs d≤D)
    (hb : Q'.abs (b + -d)≤delta) (hc : Q'.abs (a + -c)≤delta) :
    Q'.abs (a*b + -(c*d))≤(A+D)*delta := by
  have hleft := Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le a (b + -d))
    (Q'.mul_le_mul_of_nonneg ha hb hA (Q'.abs_nonneg _))
  have hright := Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le d (a + -c))
    (Q'.mul_le_mul_of_nonneg hd hc hD (Q'.abs_nonneg _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (mul_sub_decomp a b c d)))
    (Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hleft hright) (Q'.ge_of_eqv (Q'.add_mul_eqv A D delta))))

def productScalarTolerance (F G : CtsMod) (epsilon : Q') : Q' :=
  linearTolerance (F.bound+G.bound) (Q'.zero_le_add _ _ (bound_nonneg F) (bound_nonneg G)) epsilon

theorem productScalarTolerance_pos (F G : CtsMod) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (0 : Q')<productScalarTolerance F G epsilon := linearTolerance_pos _ _ he

def productScalarModulus (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (epsilon : Q') : Nat :=
  max ((symbolErrorModulus F V).stage (productScalarTolerance F G epsilon))
    ((symbolErrorModulus G W).stage (productScalarTolerance F G epsilon))

theorem product_symbol_error (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : productScalarModulus F V G W epsilon≤n)
    (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    Q'.abs (QPoly.eval (productPolynomial F G n) t + -(F.f t*G.f t))≤epsilon := by
  have hd := productScalarTolerance_pos F G he
  have hF := bernstein_symbol_bound F V _ hd n (Nat.le_trans (Nat.le_max_left _ _) hn) t ht h1
  have hG := bernstein_symbol_bound G W _ hd n (Nat.le_trans (Nat.le_max_right _ _) hn) t ht h1
  have h := mul_difference_bound _ _ _ _ F.bound G.bound _ (bound_nonneg F) (bound_nonneg G)
    (bernsteinPoly_abs_bound F n t ht h1) (G.f_le t)
    (abs_sub_le_of_bounds hG.1 hG.2) (abs_sub_le_of_bounds hF.1 hF.2)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr_right _ _ _ (QPoly.eval_pmul _ _ t))))
    (Q'.le_trans' _ _ _ h (linearTolerance_budget _ (Q'.zero_le_add _ _ (bound_nonneg F) (bound_nonneg G)) he))

theorem two_sided_of_abs {a b epsilon : Q'} (h : Q'.abs (a + -b)≤epsilon) :
    a≤b+epsilon ∧ b≤a+epsilon :=
  ⟨le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_abs_self _) h),
    le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm b a)) h))⟩

def multiplicationModulus (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (H : CtsMod) (U : MonotoneOmegaVanishing H)
    (epsilon : Q') : Nat :=
  max (productScalarModulus F V G W (HalfPow.half*epsilon))
    ((symbolErrorModulus H U).stage (HalfPow.half*epsilon))

theorem product_symbol_close (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (H : CtsMod) (U : MonotoneOmegaVanishing H)
    (hH : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (H.f t) (F.f t*G.f t))
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : multiplicationModulus F V G W H U epsilon≤n)
    (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (productPolynomial F G n) t≤QPoly.eval (bernsteinPoly H n) t+epsilon ∧
    QPoly.eval (bernsteinPoly H n) t≤QPoly.eval (productPolynomial F G n) t+epsilon := by
  have hd := ExpNeg.half_mul_pos epsilon he
  have hp := two_sided_of_abs (product_symbol_error F V G W _ hd n (Nat.le_trans (Nat.le_max_left _ _) hn) t ht h1)
  have hh := bernstein_symbol_bound H U _ hd n (Nat.le_trans (Nat.le_max_right _ _) hn) t ht h1
  exact ⟨half_error_trans _ _ _ epsilon hp.1 (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hH t ht h1)) hh.2),
    half_error_trans _ _ _ epsilon hh.1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv (hH t ht h1)) hp.2)⟩

theorem productAction_eq_symbol (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (H : CtsMod) (U : MonotoneOmegaVanishing H)
    (hH : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (H.f t) (F.f t*G.f t)) (X : CyclicPresentation) :
    productAction F V G W X=symbolAction H U X := by
  apply rowLimits_eq_of_close (productRows F V G W X) (symbolRows H U X)
    (fun epsilon => multiplicationModulus F V G W H U (approximationTolerance X epsilon))
  intro epsilon he n hn
  rw [productRows_pin,symbolRows_pin]
  exact polynomial_close X _ _ epsilon he
    (product_symbol_close F V G W H U hH _ (approximationTolerance_pos X he) n hn)

/-- Multiplication for any represented product symbol; only rational [0,1] values are pinned. -/
theorem symbolAction_mul (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (H : CtsMod) (U : MonotoneOmegaVanishing H)
    (hH : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (H.f t) (F.f t*G.f t)) (X : CyclicPresentation) :
    symbolAction H U X=symbolAction F V (actionPresentation G W X) :=
  (productAction_eq_symbol F V G W H U hH X).symm.trans (productAction_eq_composition F V G W X)

theorem polynomial_eval_congr (X : CyclicPresentation) (p q : QPoly.Poly)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (QPoly.eval p t) (QPoly.eval q t)) :
    polynomialOperator p (state X)=polynomialOperator q (state X) := by
  apply completed_eq_of_small
  intro epsilon he
  apply polynomial_close X p q epsilon he
  intro t ht h1
  have hd := Q'.le_of_lt (approximationTolerance_pos X he)
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (h t ht h1)) (Q'.add_le_self_of_nonneg _ _ hd),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (h t ht h1)) (Q'.add_le_self_of_nonneg _ _ hd)⟩

/-- All represented continuous actions commute; no product-symbol package is required. -/
theorem symbolAction_comm (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :
    symbolAction F V (actionPresentation G W X)=symbolAction G W (actionPresentation F V X) := by
  rw [← productAction_eq_composition,← productAction_eq_composition]
  apply rowLimit_independent
  intro n
  rw [productRows_pin,productRows_pin]
  apply polynomial_eval_congr X
  intro t _ _
  exact Q'.eqv_trans _ _ _ (QPoly.eval_pmul _ _ t)
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.eqv_symm (QPoly.eval_pmul _ _ t)))

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.mul_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.productScalarTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.productScalarTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.productScalarModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.product_symbol_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.two_sided_of_abs
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.multiplicationModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.product_symbol_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.productAction_eq_symbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.symbolAction_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.polynomial_eval_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication.symbolAction_comm
