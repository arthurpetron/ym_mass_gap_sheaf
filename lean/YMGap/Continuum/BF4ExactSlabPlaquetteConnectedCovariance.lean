/-
# Literal ORIGINAL connected reflected covariance on the unit complement

The coefficient of the rank-one projection is exactly the original
expectation E(p), with its constructive modulus. Thus centered completed
expression states pair to E(theta(p)q)-E(p)E(q), using the SAME full action
and partition function in every expectation. The covariance has explicit
QCauchy data, symmetry, positive diagonal and sharp Cauchy--Schwarz.

This is a finite-slab, cutoff-limit connected covariance identity. There
is no temporal separation estimate, stationary physical vacuum, nonzero
excitation witness, strict spectral gap or continuum limit in this file.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity

namespace YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection
open YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half
local notation "u" => completedUnit w hw0 hw1 half
local notation "B" => completedInner w hw0 hw1

def mean (e : PlaquetteExpression half) : CReal := expectation w hw0 hw1 half (lower e)

def meanCauchy (e : PlaquetteExpression half) : QCauchy (mean w hw0 hw1 e).approx :=
  expectationCauchy w hw0 hw1 half (lower e)

theorem form_unit_left_mean (e : PlaquetteExpression half) : Equiv (form w hw0 hw1 .unit e) (mean w hw0 hw1 e) :=
  expectation_congr w hw0 hw1 half (RatPolyCoeffEqv.one_mul (lower e))

theorem form_unit_right_mean (e : PlaquetteExpression half) : Equiv (form w hw0 hw1 e .unit) (mean w hw0 hw1 e) :=
  (form_symm w hw0 hw1 e .unit).trans (form_unit_left_mean w hw0 hw1 e)

theorem unitCoefficient_constant_mean (e : PlaquetteExpression half) :
    Equiv (unitCoefficient w hw0 hw1 ((D).constant e)) (mean w hw0 hw1 e) :=
  (representativeInner_constant w hw0 hw1 e .unit).trans (form_unit_right_mean w hw0 hw1 e)

theorem unitProjection_expression_mean (e : PlaquetteExpression half) :
    unitProjection w hw0 hw1 (embedExpression w hw0 hw1 e) =
      completedRealSmul w hw0 hw1 (mean w hw0 hw1 e) (meanCauchy w hw0 hw1 e) u :=
  (unitProjection_mk w hw0 hw1 ((D).constant e)).trans
    (completedRealSmul_congr w hw0 hw1 _ _ _ _ (unitCoefficient_constant_mean w hw0 hw1 e) u)

theorem centeredExpression_mean (e : PlaquetteExpression half) :
    (centeredExpression w hw0 hw1 e).val = completedSub w hw0 hw1 (embedExpression w hw0 hw1 e)
      (completedRealSmul w hw0 hw1 (mean w hw0 hw1 e) (meanCauchy w hw0 hw1 e) u) := by
  change completedSub w hw0 hw1 (embedExpression w hw0 hw1 e) (unitProjection w hw0 hw1 (embedExpression w hw0 hw1 e)) = _
  rw [unitProjection_expression_mean]

/-- All three expectations use the literal ORIGINAL finite-slab functional. -/
def connectedCovariance (e f : PlaquetteExpression half) : CReal :=
  CReal.sub (expectation w hw0 hw1 half
    (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (lower e)) (lower f)))
    (CReal.mul (mean w hw0 hw1 e) (mean w hw0 hw1 f))

def connectedCovarianceCauchy (e f : PlaquetteExpression half) : QCauchy (connectedCovariance w hw0 hw1 e f).approx :=
  scalarAddCauchy _ _
    (expectationCauchy w hw0 hw1 half
      (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (lower e)) (lower f)))
    (scalarNegCauchy _ (scalarMulCauchy _ _ (meanCauchy w hw0 hw1 e) (meanCauchy w hw0 hw1 f)))

theorem connectedCovariance_pairing (e f : PlaquetteExpression half) :
    B (centeredExpression w hw0 hw1 e).val (centeredExpression w hw0 hw1 f).val =
      Quotient.mk crealSetoid (connectedCovariance w hw0 hw1 e f) := by
  have hcross : pairing w hw0 hw1 e f = Quotient.mk crealSetoid
      (expectation w hw0 hw1 half
        (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (lower e)) (lower f))) :=
    Quotient.sound (form_reflected w hw0 hw1 e f)
  have hleft : pairing w hw0 hw1 e .unit = Quotient.mk crealSetoid (mean w hw0 hw1 e) :=
    Quotient.sound (form_unit_right_mean w hw0 hw1 e)
  have hright : pairing w hw0 hw1 .unit f = Quotient.mk crealSetoid (mean w hw0 hw1 f) :=
    Quotient.sound (form_unit_left_mean w hw0 hw1 f)
  change B (center w hw0 hw1 (embedExpression w hw0 hw1 e)) (center w hw0 hw1 (embedExpression w hw0 hw1 f)) = _
  rw [centered_inner_embedExpression, hcross, hleft, hright]
  rfl

theorem connectedCovariance_symm (e f : PlaquetteExpression half) :
    Equiv (connectedCovariance w hw0 hw1 e f) (connectedCovariance w hw0 hw1 f e) := by
  apply Quotient.exact (s := crealSetoid)
  rw [← connectedCovariance_pairing, ← connectedCovariance_pairing, completedInner_symm]

theorem connectedCovariance_nonnegative (e : PlaquetteExpression half) : leEv czero (connectedCovariance w hw0 hw1 e e) := by
  have h := completedInner_nonnegative w hw0 hw1 (centeredExpression w hw0 hw1 e).val
  rw [connectedCovariance_pairing] at h
  exact h

theorem connectedCovariance_cauchySchwarz (e f : PlaquetteExpression half) :
    leEv (CReal.mul (connectedCovariance w hw0 hw1 e f) (connectedCovariance w hw0 hw1 e f))
      (CReal.mul (connectedCovariance w hw0 hw1 e e) (connectedCovariance w hw0 hw1 f f)) := by
  have h := completedInner_cauchySchwarz w hw0 hw1 (centeredExpression w hw0 hw1 e).val (centeredExpression w hw0 hw1 f).val
  rw [connectedCovariance_pairing, connectedCovariance_pairing, connectedCovariance_pairing] at h
  exact h

end YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.mean
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.meanCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.form_unit_left_mean
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.form_unit_right_mean
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.unitCoefficient_constant_mean
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.unitProjection_expression_mean
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.centeredExpression_mean
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.connectedCovarianceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance_cauchySchwarz
