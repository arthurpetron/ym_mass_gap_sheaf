/-
# Recentered polynomial for the sharp cubic-debt coefficient threshold

After writing `A = k + 2` and clearing the positive denominator
`(A - 1)^6 * (A + 1)^4`, the old cubic-debt coefficient comparison is the
nonnegativity of one degree-ten integer polynomial.  This file records that
polynomial directly in the reflective rational ring substrate and recenters
it at `A = 1332 + X`, corresponding to `k = 1330 + X`.

Kernel normalization proves that every recentered coefficient is
nonnegative.  The separate semantic bridge to the physical coefficient keeps
all denominator-positivity and clearing steps explicit.
-/

import YMGap.Continuum.CoreBResidualSimplex

namespace YMGap.Continuum.HarmonicLowerSixCubicDebtCoefficient1330Polynomial

open YMGap.Constructive
open YMGap.Continuum.CoreBResidualSimplex

private abbrev PE := RingNormaliser.PolyExpr

/-- The denominator-cleared coefficient polynomial at a symbolic value `A`.

It is
`2916*(A-1)^6*(A+1)^4
 - 40320*A*(12*(A+1)^2+1)*(2*A^2-1)^3`.
-/
def pCubicDebtCoefficientClearedAt (A : PE) : PE :=
  let one : PE := .const 1
  let AminusOne : PE := .add A (.neg one)
  let AplusOne : PE := .add A one
  let twoASquaredMinusOne : PE :=
    .add (.mul (.const 2) (.pow A 2)) (.neg one)
  let profileFactor : PE :=
    .add (.mul (.const 12) (.pow AplusOne 2)) one
  .add
    (.mul (.const 2916)
      (.mul (.pow AminusOne 6) (.pow AplusOne 4)))
    (.neg
      (.mul (.const 40320)
        (.mul A
          (.mul profileFactor (.pow twoASquaredMinusOne 3)))))

/-- Recenter at `A = 1332 + X`, i.e. `k = 1330 + X`. -/
def pCubicDebtCoefficient1330 : PE :=
  pCubicDebtCoefficientClearedAt
    (.add (.const 1332) (.var 0))

/-- The complete recentered degree-ten polynomial has nonnegative integer
coefficients.  This is a closed kernel computation, not a sampled estimate. -/
theorem pCubicDebtCoefficient1330_coefficients_nonnegative :
    RawCoefficientsNonnegative
      (fastNormalize pCubicDebtCoefficient1330) = true := by
  decide

/-- Evaluation environment for the nonnegative recentering slack. -/
def cubicDebt1330Environment (X : Q') (index : Nat) : Q' :=
  if index = 0 then X else 0

private theorem cubicDebt1330Environment_nonnegative
    (X : Q') (hX : (0 : Q') ≤ X) :
    ∀ index, (0 : Q') ≤ cubicDebt1330Environment X index := by
  intro index
  unfold cubicDebt1330Environment
  by_cases hindex : index = 0
  · rw [if_pos hindex]
    exact hX
  · rw [if_neg hindex]
    exact Q'.le_refl' 0

/-- The cleared polynomial is nonnegative for every `A = 1332 + X` with
`X >= 0`. -/
theorem pCubicDebtCoefficient1330_eval_nonnegative
    (X : Q') (hX : (0 : Q') ≤ X) :
    (0 : Q') ≤ RingNormaliser.eval
      (cubicDebt1330Environment X) pCubicDebtCoefficient1330 :=
  eval_nonneg_of_fast_coefficients
    (cubicDebt1330Environment_nonnegative X hX)
    pCubicDebtCoefficient1330_coefficients_nonnegative

#print axioms pCubicDebtCoefficient1330_coefficients_nonnegative
#print axioms pCubicDebtCoefficient1330_eval_nonnegative

end YMGap.Continuum.HarmonicLowerSixCubicDebtCoefficient1330Polynomial
