/-
# The ORIGINAL thermodynamic reflected form

The constructed all-face limits contain the literal mixed product of an
upper reflected expression and a lower expression. Hence the original
finite-slab OS forms converge to the form below, with explicit volume and
representative Cauchy moduli and the same geometric error estimate.

Symmetry, rational bilinearity, reflection positivity, normalization and
sharp Cauchy--Schwarz pass through this same sequence. The unit rows are
pinned to the already-constructed lower mean, not to a separately chosen
state. No physical transfer, stationary vacuum, gap or continuum is asserted.
-/

import YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit
import YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit (rate)
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay (boxSize)

def formSequence {base : Nat} (e f : PlaquetteExpression base) (margin : Nat) : CReal :=
  form nome nome_pos nome_lt_one (enlarge margin e) (enlarge margin f)

theorem formSequence_pin {base : Nat} (e f : PlaquetteExpression base) (margin : Nat) :
    formSequence e f margin = meanSequence (reflectedProduct e f) margin := by
  unfold formSequence form meanSequence BF4ExactSlabSpacetimeExpectationDecay.mean
  rw [reflectedProduct_pin]

def formLimit {base : Nat} (e f : PlaquetteExpression base) : CReal :=
  meanLimit (reflectedProduct e f)

def formLimitCauchy {base : Nat} (e f : PlaquetteExpression base) : QCauchy (formLimit e f).approx :=
  meanLimitCauchy (reflectedProduct e f)

def formVolumeModulus {base : Nat} (e f : PlaquetteExpression base) : Q' → Nat :=
  volumeModulus (reflectedProduct e f)

theorem form_converges {base : Nat} (e f : PlaquetteExpression base) :
    ConvergesTo (formSequence e f) (formLimit e f) := by
  have hseq : formSequence e f = meanSequence (reflectedProduct e f) := funext (formSequence_pin e f)
  rw [hseq]
  exact meanLimit_converges (reflectedProduct e f)

theorem form_geometric_bound {base : Nat} (e f : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (formLimit e f) (formSequence e f margin)))
      (ofQ' (amplitude (reflectedProduct e f) * rate^(margin+1-boxSize base))) := by
  rw [formSequence_pin]
  exact meanLimit_geometric_bound (reflectedProduct e f) margin

theorem form_error_le {base : Nat} (e f : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hm : formVolumeModulus e f epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (formLimit e f) (formSequence e f margin))) (ofQ' epsilon) := by
  rw [formSequence_pin]
  exact meanLimit_error_le (reflectedProduct e f) epsilon he margin hm

theorem form_symm {base : Nat} (e f : PlaquetteExpression base) :
    Equiv (formLimit e f) (formLimit f e) :=
  Equiv_of_limit_of_equal
    (fun margin => BF4ExactSlabPlaquetteReflectedForm.form_symm nome nome_pos nome_lt_one
      (enlarge margin e) (enlarge margin f)) (form_converges e f) (form_converges f e)

theorem form_add_left {base : Nat} (e f g : PlaquetteExpression base) :
    Equiv (formLimit (.add e f) g) (CReal.add (formLimit e g) (formLimit f g)) :=
  Equiv_of_limit_of_equal
    (fun margin => BF4ExactSlabPlaquetteReflectedForm.form_add_left nome nome_pos nome_lt_one
      (enlarge margin e) (enlarge margin f) (enlarge margin g))
    (form_converges (.add e f) g) (convergesTo_add (form_converges e g) (form_converges f g))

theorem form_add_right {base : Nat} (e f g : PlaquetteExpression base) :
    Equiv (formLimit e (.add f g)) (CReal.add (formLimit e f) (formLimit e g)) :=
  Equiv_of_limit_of_equal
    (fun margin => BF4ExactSlabPlaquetteReflectedForm.form_add_right nome nome_pos nome_lt_one
      (enlarge margin e) (enlarge margin f) (enlarge margin g))
    (form_converges e (.add f g)) (convergesTo_add (form_converges e f) (form_converges e g))

theorem form_smul_left {base : Nat} (c : Q') (e f : PlaquetteExpression base) :
    Equiv (formLimit (.smul c e) f) (CReal.mul (ofQ' c) (formLimit e f)) :=
  Equiv_of_limit_of_equal
    (fun margin => BF4ExactSlabPlaquetteReflectedForm.form_smul_left nome nome_pos nome_lt_one c
      (enlarge margin e) (enlarge margin f))
    (form_converges (.smul c e) f) (convergesTo_const_mul (ofQ' c) (form_converges e f))

theorem form_smul_right {base : Nat} (c : Q') (e f : PlaquetteExpression base) :
    Equiv (formLimit e (.smul c f)) (CReal.mul (ofQ' c) (formLimit e f)) :=
  Equiv_of_limit_of_equal
    (fun margin => BF4ExactSlabPlaquetteReflectedForm.form_smul_right nome nome_pos nome_lt_one c
      (enlarge margin e) (enlarge margin f))
    (form_converges e (.smul c f)) (convergesTo_const_mul (ofQ' c) (form_converges e f))

/-- Reflection positivity of the actual original thermodynamic OS form. -/
theorem form_nonnegative {base : Nat} (e : PlaquetteExpression base) :
    leEv (ofQ' 0) (formLimit e e) :=
  leEv_of_convergesTo_le (convergesTo_const _) (form_converges e e)
    (fun margin => BF4ExactSlabPlaquetteReflectedForm.form_nonnegative nome nome_pos nome_lt_one
      (enlarge margin e))

theorem form_unit (base : Nat) :
    Equiv (formLimit (.unit : PlaquetteExpression base) .unit) CReal.cone :=
  Equiv_of_limit_of_equal
    (fun margin => BF4ExactSlabPlaquetteReflectedForm.form_unit nome nome_pos nome_lt_one (base+margin))
    (form_converges .unit .unit) (convergesTo_const _)

theorem lowerMeanSequence_pin {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    BF4ExactSlabPlaquetteConnectedCovariance.mean nome nome_pos nome_lt_one (enlarge margin e) =
      BF4ExactSlabExpressionThermodynamicLimit.meanSequence e margin := by
  unfold BF4ExactSlabPlaquetteConnectedCovariance.mean
    BF4ExactSlabExpressionThermodynamicLimit.meanSequence
    BF4ExactSlabExpressionExpectationDecay.expressionMean
  rw [← evaluate_lower_enlarge, evaluate_fromLower]

theorem lowerMeanSequence_converges {base : Nat} (e : PlaquetteExpression base) :
    ConvergesTo
      (fun margin => BF4ExactSlabPlaquetteConnectedCovariance.mean nome nome_pos nome_lt_one (enlarge margin e))
      (BF4ExactSlabExpressionThermodynamicLimit.meanLimit e) := by
  have hseq := funext (lowerMeanSequence_pin e)
  rw [hseq]
  exact BF4ExactSlabExpressionThermodynamicLimit.meanLimit_converges e

theorem form_unit_left_mean {base : Nat} (e : PlaquetteExpression base) :
    Equiv (formLimit .unit e) (BF4ExactSlabExpressionThermodynamicLimit.meanLimit e) :=
  Equiv_of_limit_of_equal
    (fun margin => BF4ExactSlabPlaquetteConnectedCovariance.form_unit_left_mean nome nome_pos nome_lt_one
      (enlarge margin e)) (form_converges .unit e) (lowerMeanSequence_converges e)

theorem form_unit_right_mean {base : Nat} (e : PlaquetteExpression base) :
    Equiv (formLimit e .unit) (BF4ExactSlabExpressionThermodynamicLimit.meanLimit e) :=
  (form_symm e .unit).trans (form_unit_left_mean e)

/-- Sharp CS survives volume convergence, without a chosen global approximation bound. -/
theorem form_cauchySchwarz {base : Nat} (e f : PlaquetteExpression base) :
    leEv (CReal.mul (formLimit e f) (formLimit e f))
      (CReal.mul (formLimit e e) (formLimit f f)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (form_converges e f) (form_converges e f))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (form_converges e e) (form_converges f f))
    (fun margin => BF4ExactSlabPlaquetteReflectedForm.form_cauchySchwarz nome nome_pos nome_lt_one
      (enlarge margin e) (enlarge margin f))

private theorem equiv_zero_of_square_le_zero (A : CReal)
    (h : leEv (CReal.mul A A) (ofQ' 0)) : Equiv A (ofQ' 0) := by
  intro epsilon he
  obtain ⟨index, hN⟩ := h (epsilon * epsilon) (Q'.mul_pos he he)
  refine ⟨index, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon * epsilon := by
    have hs := hN n hn
    change A.approx n * A.approx n ≤ 0 + epsilon * epsilon at hs
    rwa [Q'.zero_add'] at hs
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

theorem form_radical_zero {base : Nat} (e f : PlaquetteExpression base)
    (he : Equiv (formLimit e e) (ofQ' 0)) : Equiv (formLimit e f) (ofQ' 0) :=
  equiv_zero_of_square_le_zero _ (leEv_trans (form_cauchySchwarz e f)
    (leEv_of_equiv ((Pivot2.mul_congr_left he).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv ((formLimit f f).approx n))))))

end YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.formSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.formSequence_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.formLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.formLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.formVolumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_error_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_add_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_add_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.lowerMeanSequence_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.lowerMeanSequence_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_unit_left_mean
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_unit_right_mean
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm.form_radical_zero
