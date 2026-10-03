/-
# A one-head positive-source regression mismatch

For the original one-quaternion Haar law with unit insertion, the positive
incoming polynomial `2+x₀` and constant second input give a nonzero
determinant residual `U*b-A*C`. Thus U*J is strictly larger than the
Gram-only term `A^2*(U*H[c^2]-C^2)`. This is only a finite Haar witness, not an
original Yang--Mills terminal message or a claim about the full score budget.
-/

import YMGap.Continuum.QuaternionHaarUnitScalarSquare
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace

namespace YMGap.Continuum.QuaternionHaarConditionalRegressionWitness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (PolyQuaternion)
open YMGap.Continuum.QuaternionHaarSquareCertificate (Certificate)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
  (oneAddScalar oneAddScalar_certificate)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_coordinate)

local infix:50 " ≈ " => Q'.eqv

/-- The positive incoming polynomial `2+x₀` on one original quaternion head. -/
def incoming : RatPoly :=
  polyAdd polyOne (oneAddScalar (PolyQuaternion.coordinateVariable 0))

/-- Constant second input, with the same one-head unit Haar insertion. -/
def reference : RatPoly := polyOne

/-- An actual original-Haar positivity certificate for the incoming source. -/
def incoming_certificate : Certificate 1 incoming :=
  Certificate.add (Certificate.one 1)
    (oneAddScalar_certificate
      (QuaternionHaarUnitScalarSquare.Supported.coordinate (by decide))
      (haarNorm_coordinate (by decide)))

/-- Explicit unit floor, stronger than mere incoming nonnegativity. -/
def incoming_floor_certificate : Certificate 1 (polyAdd incoming (polyNeg polyOne)) :=
  Certificate.ofCoeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => polyOne | _ => oneAddScalar (PolyQuaternion.coordinateVariable 0)))
    (oneAddScalar_certificate
      (QuaternionHaarUnitScalarSquare.Supported.coordinate (by decide))
      (haarNorm_coordinate (by decide)))

def headMean : Q' := quaternionHaar 1 incoming
def referenceMean : Q' := quaternionHaar 1 reference
def headSecond : Q' := quaternionHaar 1 (polyMul incoming incoming)
def crossMoment : Q' := quaternionHaar 1 (polyMul incoming reference)
def referenceSecond : Q' := quaternionHaar 1 (polyMul reference reference)

/-- The one-head Gram determinant for the two columns. -/
def gram : Q' := headSecond * referenceSecond - crossMoment * crossMoment

/-- The determinant residual appearing in the conditional regression. -/
def residual : Q' := headSecond * referenceMean - headMean * crossMoment

/-- J is the literal paired square, not an alias of the mismatch E. -/
def pairedSquare : Q' :=
  let X := polyAdd (polySmul headMean reference)
    (polyNeg (polySmul referenceMean incoming))
  quaternionHaar 1 (polyMul X X)

theorem original_haar_moments :
    headMean ≈ 2 ∧ referenceMean ≈ 1 ∧
    headSecond ≈ Q'.mkPos 17 4 (by decide) ∧ crossMoment ≈ 2 ∧
    referenceSecond ≈ 1 := by
  decide

theorem gram_exact : gram ≈ Q'.mkPos 1 4 (by decide) := by
  decide

theorem residual_exact : residual ≈ Q'.mkPos 1 4 (by decide) := by
  decide

theorem pairedSquare_exact : pairedSquare ≈ Q'.mkPos 1 4 (by decide) := by
  decide

theorem residual_square_exact : residual*residual ≈ Q'.mkPos 1 16 (by decide) := by
  decide

/-- Even with a positive incoming source, the regression residual is not
automatically omitted from the paired-square regression. -/
theorem regression_gram_mismatch :
    headSecond * pairedSquare > headMean * headMean * gram := by
  decide

#print axioms incoming
#print axioms reference
#print axioms incoming_certificate
#print axioms incoming_floor_certificate
#print axioms headMean
#print axioms referenceMean
#print axioms headSecond
#print axioms crossMoment
#print axioms referenceSecond
#print axioms gram
#print axioms residual
#print axioms pairedSquare
#print axioms original_haar_moments
#print axioms gram_exact
#print axioms residual_exact
#print axioms pairedSquare_exact
#print axioms residual_square_exact
#print axioms regression_gram_mismatch

end YMGap.Continuum.QuaternionHaarConditionalRegressionWitness
