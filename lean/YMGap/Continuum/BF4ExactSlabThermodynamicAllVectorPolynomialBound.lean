/-
# Sharp polynomial bounds on the FULL ORIGINAL completed carrier

The all-vector Bernstein rows and their computed convergence prove
  a ||x||^2 <= <x,p(T2)x> <= b ||x||^2
whenever a<=p<=b on rational [0,1]. In particular polynomial positivity
holds on EVERY original completed vector, not only a probe's cyclic span.
Original operator symmetry and multiplication then give
  ||p(T2)x||^2 <= M^2 ||x||^2
from |p|<=M, with the corresponding distance and polynomial-difference bounds.

The rational norm cap is used only in the explicit convergence proof and
does not appear in the final bound. Quotient induction proves a proposition;
no Cauchy representative is chosen or returned from an arbitrary quotient.
No cyclic-density, normalization or spectral-model premise is supplied.
Continuous action on the full carrier and physical/continuum pins remain
subsequent obligations. The SU(2) nome and spacing are fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence

namespace YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (vector_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows (node node_nonnegative node_le_one)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (evalAt_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence
open YMGap.Continuum.RationalScalarTwoSidedError (le_of_all_errors)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)
local notation "point" X => Quotient.mk seminorm.completionSetoid X

def polynomialForm (x : Completion) (p : QPoly.Poly) : RC := completedInner x (polynomialOperator p x)

theorem polynomialForm_pin (X : seminorm.Cauchy) (p : QPoly.Poly) :
    Quotient.mk crealSetoid (limitAt X p 0)=polynomialForm (point X) p := limitAt_pin X p 0

theorem rowPolynomial_pin (X : seminorm.Cauchy) (n : Nat) (p : QPoly.Poly) :
    Quotient.mk crealSetoid (rowAt X n p 0)=average (point X) n (fun w => QPoly.eval p (node n w)) := by
  rw [rowAt_pin]
  exact average_congr (point X) n _ _ (fun w => evalAt_zero p (node n w))

theorem finite_lower (x : Completion) (n : Nat) (p : QPoly.Poly) (a : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → a≤QPoly.eval p t) :
    RCle (RCscale a (completedInner x x)) (average x n (fun w => QPoly.eval p (node n w))) := by
  rw [← average_const x n a]
  exact average_mono x n _ _ (fun w => h _ (node_nonnegative n w) (node_le_one n w))

theorem finite_upper (x : Completion) (n : Nat) (p : QPoly.Poly) (b : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → QPoly.eval p t≤b) :
    RCle (average x n (fun w => QPoly.eval p (node n w))) (RCscale b (completedInner x x)) := by
  rw [← average_const x n b]
  exact average_mono x n _ _ (fun w => h _ (node_nonnegative n w) (node_le_one n w))

theorem form_lower_represented (X : seminorm.Cauchy) (p : QPoly.Poly) (a : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → a≤QPoly.eval p t) :
    RCle (RCscale a (completedInner (point X) (point X))) (polynomialForm (point X) p) := by
  apply le_of_all_errors
  intro epsilon he
  let n := polynomialModulus X p 0 epsilon he
  have hf := finite_lower (point X) n p a h
  rw [← rowPolynomial_pin] at hf
  have hl : RCle (Quotient.mk crealSetoid (rowAt X n p 0))
      (RCadd (Quotient.mk crealSetoid (limitAt X p 0)) (rat epsilon)) :=
    (polynomial_error_le X p 0 epsilon he n (Nat.le_refl _)).1
  rw [polynomialForm_pin] at hl
  exact RCle_trans hf hl

theorem form_upper_represented (X : seminorm.Cauchy) (p : QPoly.Poly) (b : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → QPoly.eval p t≤b) :
    RCle (polynomialForm (point X) p) (RCscale b (completedInner (point X) (point X))) := by
  apply le_of_all_errors
  intro epsilon he
  let n := polynomialModulus X p 0 epsilon he
  have hf := finite_upper (point X) n p b h
  rw [← rowPolynomial_pin] at hf
  have hl : RCle (Quotient.mk crealSetoid (limitAt X p 0))
      (RCadd (Quotient.mk crealSetoid (rowAt X n p 0)) (rat epsilon)) :=
    (polynomial_error_le X p 0 epsilon he n (Nat.le_refl _)).2
  rw [polynomialForm_pin] at hl
  exact RCle_trans hl (RCadd_le_add hf (RCle_refl _))

theorem polynomialForm_lower (x : Completion) (p : QPoly.Poly) (a : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → a≤QPoly.eval p t) :
    RCle (RCscale a (completedInner x x)) (polynomialForm x p) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact form_lower_represented X p a h

theorem polynomialForm_upper (x : Completion) (p : QPoly.Poly) (b : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → QPoly.eval p t≤b) :
    RCle (polynomialForm x p) (RCscale b (completedInner x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact form_upper_represented X p b h

theorem polynomialForm_nonnegative (x : Completion) (p : QPoly.Poly)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → (0 : Q')≤QPoly.eval p t) :
    RCnonneg (polynomialForm x p) := by
  have hb := polynomialForm_lower x p 0 h
  rw [scale_zero] at hb
  exact hb

theorem polynomial_norm_square (x : Completion) (p : QPoly.Poly) :
    completedInner (polynomialOperator p x) (polynomialOperator p x)=polynomialForm x (QPoly.pmul p p) := by
  rw [operator_symmetric,← operator_mul]
  rfl

/-- The degree-independent sharp bound now holds on the FULL original carrier. -/
theorem polynomial_norm_bound (x : Completion) (p : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M) :
    RCle (completedInner (polynomialOperator p x) (polynomialOperator p x))
      (RCscale (M*M) (completedInner x x)) := by
  rw [polynomial_norm_square]
  apply polynomialForm_upper
  intro t ht h1
  have hu := Q'.le_trans' _ _ _ (Q'.le_abs_self _) (h t ht h1)
  have hl := Q'.le_trans' _ _ _ (Q'.neg_le_neg (h t ht h1)) (ExpNeg.neg_abs_le _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.eval_pmul p p t))
    (Q'.mul_le_of_bounds hM hM hl hu hl hu)

theorem polynomial_distance_bound (x y : Completion) (p : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M) :
    RCle (completedDist (polynomialOperator p x) (polynomialOperator p y))
      (RCscale (M*M) (completedDist x y)) := by
  unfold completedDist polynomialOperator
  rw [← vector_base_sub]
  exact polynomial_norm_bound (completedSub x y) p M hM h

theorem polynomial_difference_bound (x : Completion) (p q : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t-QPoly.eval q t)≤M) :
    RCle (completedDist (polynomialOperator p x) (polynomialOperator q x))
      (RCscale (M*M) (completedInner x x)) := by
  unfold completedDist polynomialOperator
  rw [← vector_sub]
  exact polynomial_norm_bound x (QPoly.psub p q) M hM (fun t ht h1 =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (QPoly.eval_psub p q t))) (h t ht h1))

end YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.polynomialForm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.polynomialForm_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.rowPolynomial_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.finite_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.finite_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.form_lower_represented
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.form_upper_represented
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.polynomialForm_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.polynomialForm_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.polynomialForm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.polynomial_norm_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.polynomial_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.polynomial_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound.polynomial_difference_bound
