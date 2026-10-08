/-
# A positive-terminal, square-weight counterexample to Hessian sign dropping

On the literal one-quaternion Haar carrier, T=1+x0/2 has the certified
strict floor 1/2 and Q=(1-x0)^2 is a supported square. Nevertheless
H[Q*(T*J(JT)-(JT)^2)]=1/12>0 for J=D01+D23. Thus kernel windows and a
nonnegative insertion do not imply a nonpositive integrated log-Hessian.

This is a finite diagnostic, NOT a realization by the original interacting
T1, spatial/reciprocal/noise weight, or a Yang--Mills counterexample. Frozen
jet semantics do not justify ignoring derivatives of an insertion in IBP.
-/

import YMGap.Continuum.SU2QuaternionPairedFrameAt
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative (angularDerivative_congr)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.SU2QuaternionPairedFrameAt

local infix:50 " ≈ " => Q'.eqv

/-- A literal positive affine terminal, without an assumed marginal pin. -/
def witnessTerminal : RatPoly :=
  polyAdd polyOne (polySmul HalfPow.half (polyVar 0))

/-- The literal square insertion, with no density or normalization inverse. -/
def witnessWeight : RatPoly :=
  let p := polyAdd polyOne (polyNeg (polyVar 0))
  polyMul p p

/-- The unaugmented signed Hessian correction in the same original Haar. -/
def weightedHessian : Q' :=
  let d := pairedDerivativeAt 0 0 witnessTerminal
  quaternionHaar 1 (polyMul witnessWeight
    (polyAdd (polyMul witnessTerminal (pairedDerivativeAt 0 0 d))
      (polyNeg (polyMul d d))))

/-- The insertion is actually constructed as a supported polynomial square. -/
def witnessWeight_certificate : Certificate 1 witnessWeight :=
  Certificate.square _
    (supported_add (supported_one 1)
      (coordinateSquareBound 1 0 (by decide)).neg.support)

/-- The terminal has the actual positive floor 1/2 on the same carrier. -/
def witnessTerminal_floor_certificate :
    Certificate 1 (polyAdd witnessTerminal (polyNeg (cap HalfPow.half))) := by
  let P := (coordinateSquareBound 1 0 (by decide)).neg.cross (SquareBound.one 1)
  have h : RatPolyCoeffEqv (polyAdd witnessTerminal (polyNeg (cap HalfPow.half)))
      (polySmul HalfPow.half
        (polyAdd (cap 1) (polyNeg (polyMul (polyNeg (polyVar 0)) polyOne)))) :=
    RatPolyCoeffEqv.of_canon_termwise (by decide)
  exact Certificate.ofCoeff h
    (Certificate.smul HalfPow.half HalfPow.half_nonneg P)

theorem witnessTerminal_floor_positive : (0 : Q') < HalfPow.half := by decide

/-- The other literal window endpoint is 3/2, with constructed evidence. -/
def witnessTerminal_upper_certificate :
    Certificate 1 (polyAdd (cap (1+HalfPow.half)) (polyNeg witnessTerminal)) := by
  let P := (coordinateSquareBound 1 0 (by decide)).cross (SquareBound.one 1)
  have h : RatPolyCoeffEqv
      (polyAdd (cap (1+HalfPow.half)) (polyNeg witnessTerminal))
      (polySmul HalfPow.half (polyAdd (cap 1) (polyNeg (polyMul (polyVar 0) polyOne)))) :=
    RatPolyCoeffEqv.of_canon_termwise (by decide)
  exact Certificate.ofCoeff h
    (Certificate.smul HalfPow.half HalfPow.half_nonneg P)

/-- Coalesce the actual first jet before computing the literal Haar value. -/
theorem witnessTerminal_first_pin : RatPolyCoeffEqv
    (pairedDerivativeAt 0 0 witnessTerminal) (polySmul (-HalfPow.half) (polyVar 1)) :=
  RatPolyCoeffEqv.of_canon_termwise (by decide)

/-- Transport the first jet before computing its actual repeated derivative.
The literal trailing zero is retained: arbitrary coefficient probes distinguish
the monomials [1,0] and [1], although Haar integration does not. -/
theorem witnessTerminal_second_pin : RatPolyCoeffEqv
    (pairedDerivativeAt 0 0 (pairedDerivativeAt 0 0 witnessTerminal))
    [([1,0], -HalfPow.half)] := by
  have h : RatPolyCoeffEqv
      (pairedDerivativeAt 0 0 (pairedDerivativeAt 0 0 witnessTerminal))
      (pairedDerivativeAt 0 0 (polySmul (-HalfPow.half) (polyVar 1))) :=
    (angularDerivative_congr 0 1 witnessTerminal_first_pin).add
      (angularDerivative_congr 2 3 witnessTerminal_first_pin)
  exact h.trans (RatPolyCoeffEqv.of_canon_termwise (by decide))

/-- Exact kernel rational arithmetic; no native decision or analytic premise. -/
theorem weightedHessian_eq_twelfth :
    weightedHessian ≈ Q'.mkPos 1 12 (by decide) := by
  have h := ((witnessTerminal_second_pin.mul_left witnessTerminal).add
    (RatPolyCoeffEqv.neg (witnessTerminal_first_pin.mul witnessTerminal_first_pin))).mul_left
      witnessWeight
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := 1) h) (by decide)

theorem weightedHessian_positive : (0 : Q') < weightedHessian :=
  Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < Q'.mkPos 1 12 (by decide))
    (Q'.le_of_eqv (Q'.eqv_symm weightedHessian_eq_twelfth))

end YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction

#print axioms YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction.witnessWeight_certificate
#print axioms YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction.witnessTerminal_floor_certificate
#print axioms YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction.witnessTerminal_floor_positive
#print axioms YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction.witnessTerminal_upper_certificate
#print axioms YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction.witnessTerminal_first_pin
#print axioms YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction.witnessTerminal_second_pin
#print axioms YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction.weightedHessian_eq_twelfth
#print axioms YMGap.Continuum.SU2QuaternionWeightedHessianSignObstruction.weightedHessian_positive
