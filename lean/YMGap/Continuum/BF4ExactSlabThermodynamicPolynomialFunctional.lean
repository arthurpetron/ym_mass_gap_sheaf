/-
# The ORIGINAL normalized positive bounded polynomial moment functional

The constructed Bernstein rows and their explicit convergence prove
order preservation on [0,1], positivity and sup-norm bounds. Rational
linearity and normalization are exact. The representative, its QCauchy
data and its SAME-original-operator pin were constructed upstream.

This is a functional on rational polynomials for the fixed original
SU(2) nome/spacing, not yet a spectral measure, continuous functional
calculus, continuous-time generator, continuum construction or Clay result.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.RationalScalarTwoSidedError

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def momentFunctional (p : QPoly.Poly) : RC := Quotient.mk crealSetoid (limitAt p 0)

theorem functional_pin (p : QPoly.Poly) :
    momentFunctional p=completedInner unitProbe.val (polynomialVector unitProbe.val p 0) := limitAt_pin p 0

theorem rowAverage_congr (n : Nat) (f g : Word (n+1) → Q') (h : ∀ w,Q'.eqv (f w) (g w)) :
    rowAverage n f=rowAverage n g := by
  unfold rowAverage
  congr 1
  funext w
  exact scale_congr (h w) _

theorem row_polynomial_pin (n : Nat) (p : QPoly.Poly) :
    Quotient.mk crealSetoid (rowAt n p 0)=rowAverage n (fun w => QPoly.eval p (node n w)) :=
  (rowAt_pin n p 0).trans (rowAverage_congr n _ _ (fun w => evalAt_zero p (node n w)))

theorem finite_lower (n : Nat) (p : QPoly.Poly) (a : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → a≤QPoly.eval p t) :
    RCle (rat a) (Quotient.mk crealSetoid (rowAt n p 0)) := by
  rw [row_polynomial_pin,← rowAverage_const n a]
  exact rowAverage_mono n _ _ (fun w => h _ (node_nonnegative n w) (node_le_one n w))

theorem finite_upper (n : Nat) (p : QPoly.Poly) (b : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → QPoly.eval p t≤b) :
    RCle (Quotient.mk crealSetoid (rowAt n p 0)) (rat b) := by
  rw [row_polynomial_pin,← rowAverage_const n b]
  exact rowAverage_mono n _ _ (fun w => h _ (node_nonnegative n w) (node_le_one n w))

theorem functional_lower (p : QPoly.Poly) (a : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → a≤QPoly.eval p t) : RCle (rat a) (momentFunctional p) := by
  apply le_of_all_errors
  intro epsilon he
  let n := polynomialModulus p 0 epsilon he
  exact RCle_trans (finite_lower n p a h) (polynomial_error_le p 0 epsilon he n (Nat.le_refl _)).1

theorem functional_upper (p : QPoly.Poly) (b : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → QPoly.eval p t≤b) : RCle (momentFunctional p) (rat b) := by
  apply le_of_all_errors
  intro epsilon he
  let n := polynomialModulus p 0 epsilon he
  have hc : RCle (momentFunctional p) (RCadd (Quotient.mk crealSetoid (rowAt n p 0)) (rat epsilon)) :=
    (polynomial_error_le p 0 epsilon he n (Nat.le_refl _)).2
  exact RCle_trans hc
    (RCadd_le_add (finite_upper n p b h) (RCle_refl _))

theorem functional_positive (p : QPoly.Poly)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → (0 : Q')≤QPoly.eval p t) : RCnonneg (momentFunctional p) :=
  functional_lower p 0 h

/-- Every rational sup-norm bound is inherited, with constant exactly one. -/
theorem functional_sup_bound (p : QPoly.Poly) (M : Q')
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M) :
    RCle (rat (-M)) (momentFunctional p) ∧ RCle (momentFunctional p) (rat M) :=
  ⟨functional_lower p (-M) (fun t ht h1 => Q'.le_trans' _ _ _ (Q'.neg_le_neg (h t ht h1))
      (ExpNeg.neg_abs_le _)),
    functional_upper p M (fun t ht h1 => Q'.le_trans' _ _ _ (Q'.le_abs_self _) (h t ht h1))⟩

theorem nested_error (a : RC) (e f : Q') :
    RCadd (RCadd a (rat e)) (rat f)=RCadd a (rat (e+f)) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_assoc_eqv (A.approx n) e f))

theorem functional_mono (p q : QPoly.Poly)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → QPoly.eval p t≤QPoly.eval q t) :
    RCle (momentFunctional p) (momentFunctional q) := by
  apply le_of_all_errors
  intro epsilon he
  let d := epsilon*HalfPow.half
  have hd : (0 : Q')<d := Q'.mul_pos he (Q'.invSucc_pos 1)
  let n := max (polynomialModulus p 0 d hd) (polynomialModulus q 0 d hd)
  have hp : RCle (momentFunctional p) (RCadd (Quotient.mk crealSetoid (rowAt n p 0)) (rat d)) :=
    (polynomial_error_le p 0 d hd n (Nat.le_max_left _ _)).2
  have hq : RCle (Quotient.mk crealSetoid (rowAt n q 0)) (RCadd (momentFunctional q) (rat d)) :=
    (polynomial_error_le q 0 d hd n (Nat.le_max_right _ _)).1
  have hrow : RCle (Quotient.mk crealSetoid (rowAt n p 0)) (Quotient.mk crealSetoid (rowAt n q 0)) := by
    rw [row_polynomial_pin,row_polynomial_pin]
    exact rowAverage_mono n _ _ (fun w => h _ (node_nonnegative n w) (node_le_one n w))
  have hb := RCle_trans hp (RCadd_le_add (RCle_trans hrow hq) (RCle_refl _))
  change RCle (momentFunctional p) (RCadd (RCadd (momentFunctional q) (rat d)) (rat d)) at hb
  rw [nested_error] at hb
  have heq : (rat (d+d))=(rat epsilon) := Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => half_add_half epsilon))
  rw [heq] at hb
  exact hb

theorem functional_congr (p q : QPoly.Poly)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (QPoly.eval p t) (QPoly.eval q t)) :
    momentFunctional p=momentFunctional q :=
  RCle_antisymm (functional_mono p q (fun t ht h1 => Q'.le_of_eqv (h t ht h1)))
    (functional_mono q p (fun t ht h1 => Q'.ge_of_eqv (h t ht h1)))

theorem rc_add_zero (a : RC) : RCadd a RCzero=a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n)))

theorem rc_zero_add (a : RC) : RCadd RCzero a=a := (add_comm _ _).trans (rc_add_zero a)

theorem combineRC_add (f : Nat → RC) (p q : QPoly.Poly) (r : Nat) :
    combineRC f (QPoly.padd p q) r=RCadd (combineRC f p r) (combineRC f q r) := by
  induction p generalizing q r with
  | nil => exact (rc_zero_add _).symm
  | cons c p ih =>
      cases q with
      | nil => exact (rc_add_zero _).symm
      | cons d q =>
          simp only [QPoly.padd,combineRC,ih,scale_add]
          exact add_regroup _ _ _ _

theorem combineRC_scale (f : Nat → RC) (c : Q') (p : QPoly.Poly) (r : Nat) :
    combineRC f (QPoly.pscale c p) r=RCscale c (combineRC f p r) := by
  induction p generalizing r with
  | nil => exact (RCscale_RCzero c).symm
  | cons d p ih =>
      simp only [QPoly.pscale,combineRC,ih,← RCscale_RCscale,← RCscale_RCadd]

theorem functional_add (p q : QPoly.Poly) :
    momentFunctional (QPoly.padd p q)=RCadd (momentFunctional p) (momentFunctional q) := by
  unfold momentFunctional limitAt
  simp only [combine_pin]
  exact combineRC_add _ p q 0

theorem functional_scale (c : Q') (p : QPoly.Poly) :
    momentFunctional (QPoly.pscale c p)=RCscale c (momentFunctional p) := by
  unfold momentFunctional limitAt
  simp only [combine_pin]
  exact combineRC_scale _ c p 0

theorem functional_constant (c : Q') : momentFunctional [c]=rat c := by
  change RCadd (RCscale c (limitMoment 0)) RCzero=rat c
  rw [rc_add_zero,limitMoment_pin]
  change RCscale c (completedInner unitProbe.val (completedTime 0 unitProbe.val))=rat c
  rw [completedTime_zero,unitProbe_norm,scale_one_real]

theorem functional_one : momentFunctional [1]=Quotient.mk crealSetoid cone := functional_constant 1

end YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.momentFunctional
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.rowAverage_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.row_polynomial_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.finite_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.finite_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_sup_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.nested_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.rc_add_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.rc_zero_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.combineRC_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.combineRC_scale
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_scale
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_constant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional.functional_one
