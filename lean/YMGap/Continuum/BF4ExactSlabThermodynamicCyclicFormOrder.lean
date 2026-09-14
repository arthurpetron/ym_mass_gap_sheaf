/-
# Polynomial order gives ORIGINAL cyclic quadratic-form order

The cyclic form <p(T2)r(T2)v,r(T2)v> is the already-constructed positive
moment functional on p*r*r. Pointwise order on [0,1] therefore gives form
order. The represented pairing-limit theorem extends it to every original
represented cyclic state, without assuming a spectral decomposition.

In particular a nonnegative polynomial has nonnegative original quadratic
form on this sector. This is not a strictly positive physical gap, and it
does not identify the represented sector with the full physical carrier.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
import YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCyclicFormOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear (completedInner_zero_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm (probe_inner_product)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (functional_mono)
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation

theorem eval_cyclic_form (p r : QPoly.Poly) (t : Q') :
    Q'.eqv (QPoly.eval (QPoly.pmul (QPoly.pmul p r) r) t)
      (QPoly.eval p t*(QPoly.eval r t*QPoly.eval r t)) :=
  Q'.eqv_trans _ _ _ (QPoly.eval_pmul _ _ t)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (QPoly.eval_pmul p r t)) (Q'.mul_assoc_eqv _ _ _))

theorem cyclic_form_mono (p q r : QPoly.Poly)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → QPoly.eval p t≤QPoly.eval q t) :
    RCle (completedInner (polynomialOperator p (polynomialOperator r unitProbe.val)) (polynomialOperator r unitProbe.val))
      (completedInner (polynomialOperator q (polynomialOperator r unitProbe.val)) (polynomialOperator r unitProbe.val)) := by
  rw [← operator_mul,← operator_mul]
  unfold polynomialOperator
  rw [probe_inner_product,probe_inner_product]
  apply functional_mono
  intro t ht h1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_cyclic_form p r t))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (h t ht h1) (SumOfSquares.q_mul_self_nonneg _))
      (Q'.ge_of_eqv (eval_cyclic_form q r t)))

/-- Order on the interval controls the quadratic form on the SAME original represented state. -/
theorem polynomial_form_mono (X : CyclicPresentation) (p q : QPoly.Poly)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → QPoly.eval p t≤QPoly.eval q t) :
    RCle (completedInner (polynomialOperator p (state X)) (state X))
      (completedInner (polynomialOperator q (state X)) (state X)) := by
  have hr := rowLimit_pairing_le (operatorRows p X.rows) X.rows (operatorRows q X.rows) X.rows (by
    intro n
    rw [operatorRows_pin,operatorRows_pin,X.point_pin]
    exact cyclic_form_mono p q (X.polynomial n) h)
  rw [operator_rowLimit,operator_rowLimit] at hr
  exact hr

theorem polynomial_form_nonnegative (X : CyclicPresentation) (p : QPoly.Poly)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → (0 : Q')≤QPoly.eval p t) :
    RCnonneg (completedInner (polynomialOperator p (state X)) (state X)) := by
  have hp := polynomial_form_mono X [] p h
  change RCle (completedInner _ (state X)) _ at hp
  rw [show polynomialOperator [] (state X)=
    YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.completedZero from rfl,
    completedInner_zero_left] at hp
  exact hp

end YMGap.Continuum.BF4ExactSlabThermodynamicCyclicFormOrder

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicFormOrder.eval_cyclic_form
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicFormOrder.cyclic_form_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicFormOrder.polynomial_form_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicFormOrder.polynomial_form_nonnegative
