/-
# The ORIGINAL normalized cutoff-limit plaquette reflected form

For rational 0<w<1, the form is exactly E(theta(p) q) for actual lower
plaquette expressions. Its symmetry, rational bilinearity, positivity,
unit normalization and sharp Cauchy--Schwarz are proved for the SAME
original interacting action. Norm-null expressions pair to zero.

The form carries the explicit original expectation Cauchy modulus.
Its bounds depend on w, the slab and the expressions. No uniform physical
gap, inter-slab maps, physical time operator or completed physical carrier
is supplied by this module.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "faces" => slabPhysicalFaceEdges (centralExtent half)
local notation "lambda" => actionReciprocal w hw0 hw1 half

def rawLimit (e f : PlaquetteExpression half) : CReal :=
  numeratorLimit w hw0 hw1 blocks (centralExtent half) faces (polyMul (upper e) (lower f))

def form (e f : PlaquetteExpression half) : CReal :=
  expectation w hw0 hw1 half (polyMul (upper e) (lower f))

/-- This is the literal reflected observable, with the original action and Z. -/
theorem form_reflected (e f : PlaquetteExpression half) :
    CReal.Equiv (form w hw0 hw1 e f)
      (expectation w hw0 hw1 half
        (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (lower e)) (lower f))) :=
  (expectation_reflection_eq_upper w e f hw0 hw1).symm

theorem form_symm (e f : PlaquetteExpression half) :
    CReal.Equiv (form w hw0 hw1 e f) (form w hw0 hw1 f e) :=
  (expectation_reflection_image w half hw0 hw1 ((upper_reflection e).mul (lower_reflection f))
    (supported_polyMul (upper_supported e) (lower_supported f))
    (supported_polyMul (lower_supported e) (upper_supported f))).trans
    (expectation_congr w hw0 hw1 half (RatPolyCoeffEqv.mul_comm (lower e) (upper f)))

theorem form_congr {e e' f f' : PlaquetteExpression half}
    (he : expressionEqv e e') (hf : expressionEqv f f') :
    CReal.Equiv (form w hw0 hw1 e f) (form w hw0 hw1 e' f') :=
  expectation_congr w hw0 hw1 half (he.2.mul hf.1)

theorem form_add_left (e f g : PlaquetteExpression half) :
    CReal.Equiv (form w hw0 hw1 (.add e f) g)
      (CReal.add (form w hw0 hw1 e g) (form w hw0 hw1 f g)) := by
  change CReal.Equiv (expectation w hw0 hw1 half (polyMul (polyAdd (upper e) (upper f)) (lower g))) _
  rw [polyMul_add_left_exact]
  exact expectation_add w hw0 hw1 half _ _

theorem form_smul_left (c : Q') (e f : PlaquetteExpression half) :
    CReal.Equiv (form w hw0 hw1 (.smul c e) f)
      (CReal.mul (CReal.ofQ' c) (form w hw0 hw1 e f)) :=
  (expectation_congr w hw0 hw1 half (RatPolyCoeffEqv.polyMul_smul_left c (upper e) (lower f))).trans
    (expectation_smul w hw0 hw1 half c _)

theorem form_add_right (e f g : PlaquetteExpression half) :
    CReal.Equiv (form w hw0 hw1 e (.add f g))
      (CReal.add (form w hw0 hw1 e f) (form w hw0 hw1 e g)) :=
  (form_symm w hw0 hw1 _ _).trans ((form_add_left w hw0 hw1 f g e).trans
    (Pivot2.add_congr (form_symm w hw0 hw1 f e) (form_symm w hw0 hw1 g e)))

theorem form_smul_right (c : Q') (e f : PlaquetteExpression half) :
    CReal.Equiv (form w hw0 hw1 e (.smul c f))
      (CReal.mul (CReal.ofQ' c) (form w hw0 hw1 e f)) :=
  (form_symm w hw0 hw1 _ _).trans ((form_smul_left w hw0 hw1 c f e).trans
    (Pivot2.mul_congr_right (form_symm w hw0 hw1 f e)))

theorem form_nonnegative (e : PlaquetteExpression half) :
    CReal.leEv (CReal.ofQ' 0) (form w hw0 hw1 e e) :=
  CReal.leEv_trans (expectation_reflection_nonnegative w e hw0 hw1)
    (CReal.leEv_of_equiv (expectation_reflection_eq_upper w e e hw0 hw1))

theorem form_unit (half : Nat) :
    CReal.Equiv (form w hw0 hw1 (.unit : PlaquetteExpression half) .unit) CReal.cone :=
  (expectation_congr w hw0 hw1 half (RatPolyCoeffEqv.one_mul polyOne)).trans
    (expectation_one w hw0 hw1 half)

def formCauchy (e f : PlaquetteExpression half) : CReal.QCauchy (form w hw0 hw1 e f).approx :=
  expectationCauchy w hw0 hw1 half (polyMul (upper e) (lower f))

def formModulus (e f : PlaquetteExpression half) (epsilon : Q') : Nat :=
  (formCauchy w hw0 hw1 e f).M epsilon

theorem form_approx_close (e f : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (i j : Nat) (hi : formModulus w hw0 hw1 e f epsilon ≤ i)
    (hj : formModulus w hw0 hw1 e f epsilon ≤ j) :
    (form w hw0 hw1 e f).approx i ≤ (form w hw0 hw1 e f).approx j + epsilon ∧
    (form w hw0 hw1 e f).approx j ≤ (form w hw0 hw1 e f).approx i + epsilon :=
  (formCauchy w hw0 hw1 e f).bound epsilon he i j hi hj

def rawBound (e f : PlaquetteExpression half) : Q' :=
  numeratorBound w half (polyMul (upper e) (lower f))

include hw0 in
theorem rawBound_nonnegative (e f : PlaquetteExpression half) : (0 : Q') ≤ rawBound w e f :=
  numeratorBound_nonnegative w hw0 half _

include hw0 hw1 in
theorem rawForm_abs_le (K : Nat) (e f : PlaquetteExpression half) :
    Q'.abs (rawForm w K e f) ≤ rawBound w e f :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
    (Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (heatProduct_coefficientL1_bound hw0 hw1 K _ _)
        (polynomialCoefficientL1_nonnegative _)))

theorem rawLimit_approx_abs_le (e f : PlaquetteExpression half) (n : Nat) :
    Q'.abs ((rawLimit w hw0 hw1 e f).approx n) ≤ rawBound w e f :=
  numerator_approx_abs_le w hw0 hw1 half _ n

theorem rawLimit_converges (e f : PlaquetteExpression half) :
    CReal.ConvergesTo (fun K => CReal.ofQ' (rawForm w K e f)) (rawLimit w hw0 hw1 e f) :=
  numerator_converges w hw0 hw1 blocks (centralExtent half) faces _

/-- Sharp CS passes through the ORIGINAL cutoff sequence with explicit bounds. -/
theorem rawLimit_cauchySchwarz (e f : PlaquetteExpression half) :
    CReal.leEv (CReal.mul (rawLimit w hw0 hw1 e f) (rawLimit w hw0 hw1 e f))
      (CReal.mul (rawLimit w hw0 hw1 e e) (rawLimit w hw0 hw1 f f)) := by
  have hAmul : CReal.ConvergesTo
      (fun K => CReal.mul (CReal.ofQ' (rawForm w K e f)) (CReal.ofQ' (rawForm w K e f)))
      (CReal.mul (rawLimit w hw0 hw1 e f) (rawLimit w hw0 hw1 e f)) :=
    CReal.convergesTo_mul (B := rawBound w e f)
      (u := fun K => CReal.ofQ' (rawForm w K e f))
      (v := fun K => CReal.ofQ' (rawForm w K e f))
      (U := rawLimit w hw0 hw1 e f) (V := rawLimit w hw0 hw1 e f)
      (rawBound_nonnegative w hw0 e f) (fun K _ => rawForm_abs_le w hw0 hw1 K e f)
      (rawLimit_approx_abs_le w hw0 hw1 e f)
      (rawLimit_converges w hw0 hw1 e f) (rawLimit_converges w hw0 hw1 e f)
  have hBmul : CReal.ConvergesTo
      (fun K => CReal.mul (CReal.ofQ' (rawForm w K e e)) (CReal.ofQ' (rawForm w K f f)))
      (CReal.mul (rawLimit w hw0 hw1 e e) (rawLimit w hw0 hw1 f f)) :=
    CReal.convergesTo_mul (B := Q'.max' (rawBound w e e) (rawBound w f f))
      (u := fun K => CReal.ofQ' (rawForm w K e e))
      (v := fun K => CReal.ofQ' (rawForm w K f f))
      (U := rawLimit w hw0 hw1 e e) (V := rawLimit w hw0 hw1 f f)
      (Q'.le_trans' _ _ _ (rawBound_nonnegative w hw0 e e) (Q'.le_max'_left _ _))
      (fun K _ => Q'.le_trans' _ _ _ (rawForm_abs_le w hw0 hw1 K e e) (Q'.le_max'_left _ _))
      (fun n => Q'.le_trans' _ _ _ (rawLimit_approx_abs_le w hw0 hw1 f f n) (Q'.le_max'_right _ _))
      (rawLimit_converges w hw0 hw1 e e) (rawLimit_converges w hw0 hw1 f f)
  refine CReal.leEv_of_ofQ'_limit_le
    (r := fun K => rawForm w K e f * rawForm w K e f)
    (r' := fun K => rawForm w K e e * rawForm w K f f) hAmul hBmul ?_
  intro epsilon he
  exact ⟨0, fun K _ => Q'.le_trans' _ _ _ (rawForm_cauchySchwarz w (Q'.le_of_lt hw0) K e f)
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))⟩

private theorem common_factor (A B L : CReal) :
    CReal.Equiv (CReal.mul (CReal.mul A L) (CReal.mul B L))
      (CReal.mul (CReal.mul L L) (CReal.mul A B)) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv ((A.approx n * L.approx n) * (B.approx n * L.approx n))
    ((L.approx n * L.approx n) * (A.approx n * B.approx n))
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

theorem form_cauchySchwarz (e f : PlaquetteExpression half) :
    CReal.leEv (CReal.mul (form w hw0 hw1 e f) (form w hw0 hw1 e f))
      (CReal.mul (form w hw0 hw1 e e) (form w hw0 hw1 f f)) :=
  (CReal.leEv_congr
    (common_factor (rawLimit w hw0 hw1 e f) (rawLimit w hw0 hw1 e f) lambda)
    (common_factor (rawLimit w hw0 hw1 e e) (rawLimit w hw0 hw1 f f) lambda)).mpr
    (CReal.leEv_mul_nonneg_left
      (CReal.mul_nonneg (reciprocal_nonnegative w hw0 hw1 half) (reciprocal_nonnegative w hw0 hw1 half))
      (rawLimit_cauchySchwarz w hw0 hw1 e f))

private theorem equiv_zero_of_square_le_zero (A : CReal)
    (h : CReal.leEv (CReal.mul A A) (CReal.ofQ' 0)) : CReal.Equiv A (CReal.ofQ' 0) := by
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

/-- Actual normalized norm-null observables pair to zero; no square root is chosen. -/
theorem form_radical_zero (e f : PlaquetteExpression half)
    (he : CReal.Equiv (form w hw0 hw1 e e) (CReal.ofQ' 0)) :
    CReal.Equiv (form w hw0 hw1 e f) (CReal.ofQ' 0) :=
  equiv_zero_of_square_le_zero _ (CReal.leEv_trans (form_cauchySchwarz w hw0 hw1 e f)
    (CReal.leEv_of_equiv ((Pivot2.mul_congr_left he).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv ((form w hw0 hw1 f f).approx n))))))

end YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.rawLimit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_reflected
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_add_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_add_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_unit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.formCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.formModulus
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.rawBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.rawBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.rawForm_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.rawLimit_approx_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.rawLimit_converges
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.rawLimit_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm.form_radical_zero
