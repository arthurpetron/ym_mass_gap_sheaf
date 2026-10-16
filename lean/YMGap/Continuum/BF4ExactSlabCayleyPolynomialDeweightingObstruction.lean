/-
# Global polynomial de-weighting is obstructed at the Cayley south pole

The one-link Cayley denominator `1+r` vanishes at the rational unit
quaternion `-1`.  Consequently no polynomial corrector can turn it into one
on every rational unit-quaternion assignment, or even give the corrected
product a strictly positive uniform lower bound.

This rules out a global polynomial/geometric-series de-weighting shortcut for
the denominator-cleared ORIGINAL expectations.  It does not rule out a
multi-chart construction, a cutoff excluding the south pole with controlled
error, or an alternative bounded group-coordinate source jet.
-/

import YMGap.Continuum.QuaternionHaarFiniteProductOrder
import YMGap.Continuum.RationalQuaternionRatPoly
import YMGap.Continuum.SU2QuaternionWilsonWeightSOS

namespace YMGap.Continuum.BF4ExactSlabCayleyPolynomialDeweightingObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion
open YMGap.Continuum.RingNormaliser (evalMono)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (RatPolyCoeffEqv)
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
  (evalRatPoly_one evalRatPoly_var)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder
open YMGap.Continuum.RationalQuaternionRatPoly (evalRatPoly_neg)

local infix:50 " ≈ " => Q'.eqv

/-- The scalar Cayley denominator of the first quaternion block. -/
def cayleyScalarDenominator : RatPoly :=
  polyAdd polyOne (polyVar 0)

/-- Every link is the rational south pole `-1`. -/
def allSouthPole : Nat → UnitNorm := fun _ => unitNegativeOne

/-- Pointwise equality on every rational unit-quaternion assignment. -/
def UnitPointEqv (left right : RatPoly) : Prop :=
  ∀ qs : Nat → UnitNorm,
    evalRatPoly (environment qs) left ≈ evalRatPoly (environment qs) right

private theorem weighted_eval (rho : Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum (evalMono rho) p = evalRatPoly rho p
  | [] => rfl
  | term :: rest =>
      congrArg (fun value => term.2 * evalMono rho term.1 + value)
        (weighted_eval rho rest)

private theorem eval_coeff (rho : Nat → Q') {left right : RatPoly}
    (h : RatPolyCoeffEqv left right) :
    evalRatPoly rho left ≈ evalRatPoly rho right := by
  simpa only [weighted_eval] using h (evalMono rho)

theorem cayleyScalarDenominator_allSouthPole :
    evalRatPoly (environment allSouthPole) cayleyScalarDenominator ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_add _ _ _)
    (Q'.eqv_trans _ (1 + (-1)) _
      (Q'.add_eqv_congr'
        (evalRatPoly_one _)
        (Q'.eqv_trans _ _ _ (evalRatPoly_var _ 0) (by decide)))
      (by decide))

theorem correctedProduct_allSouthPole (corrector : RatPoly) :
    evalRatPoly (environment allSouthPole)
      (polyMul cayleyScalarDenominator corrector) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_mul _ _ _)
    (Q'.eqv_trans _
      (0 * evalRatPoly (environment allSouthPole) corrector) _
      (Q'.mul_eqv_congr_right _ _ _ cayleyScalarDenominator_allSouthPole)
      (Q'.zero_mul_eqv _))

/-- No polynomial is an exact inverse of `1+r` on all rational unit points. -/
theorem no_unitPoint_polynomial_inverse (corrector : RatPoly) :
    ¬ UnitPointEqv (polyMul cayleyScalarDenominator corrector) polyOne := by
  intro h
  have hzeroOne : (0 : Q') ≈ 1 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (correctedProduct_allSouthPole corrector))
      (Q'.eqv_trans _ _ _ (h allSouthPole) (evalRatPoly_one _))
  exact (by decide : ¬ ((0 : Q') ≈ 1)) hzeroOne

/-- Coefficient equality would imply the forbidden unit-point inverse. -/
theorem no_coefficient_polynomial_inverse (corrector : RatPoly) :
    ¬ RatPolyCoeffEqv (polyMul cayleyScalarDenominator corrector) polyOne := by
  intro h
  apply no_unitPoint_polynomial_inverse corrector
  intro qs
  exact eval_coeff (environment qs) h

/-- Multiplying by any polynomial corrector cannot produce a strictly
positive lower bound on the full rational unit carrier. -/
theorem no_uniform_positive_correctedProduct
    (corrector : RatPoly) (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    ¬ ∀ qs : Nat → UnitNorm,
      epsilon ≤ evalRatPoly (environment qs)
        (polyMul cayleyScalarDenominator corrector) := by
  intro h
  have hepsilonZero : epsilon ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (h allSouthPole)
      (Q'.le_of_eqv (correctedProduct_allSouthPole corrector))
  exact (Int.not_lt_of_ge hepsilonZero) hepsilon

end YMGap.Continuum.BF4ExactSlabCayleyPolynomialDeweightingObstruction

#print axioms YMGap.Continuum.BF4ExactSlabCayleyPolynomialDeweightingObstruction.cayleyScalarDenominator_allSouthPole
#print axioms YMGap.Continuum.BF4ExactSlabCayleyPolynomialDeweightingObstruction.correctedProduct_allSouthPole
#print axioms YMGap.Continuum.BF4ExactSlabCayleyPolynomialDeweightingObstruction.no_unitPoint_polynomial_inverse
#print axioms YMGap.Continuum.BF4ExactSlabCayleyPolynomialDeweightingObstruction.no_coefficient_polynomial_inverse
#print axioms YMGap.Continuum.BF4ExactSlabCayleyPolynomialDeweightingObstruction.no_uniform_positive_correctedProduct
