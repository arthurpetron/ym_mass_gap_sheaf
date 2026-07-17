/-
# Exact coefficient certificate for the cubic-debt/mass splice at `k = 1330`

After clearing the positive denominators in the literal moment coefficient,
the remaining degree-twelve polynomial is expanded at `A = k+2 = 1332+X`.
Kernel normalization checks every coefficient nonnegative.
-/

import YMGap.Continuum.CoreBResidualSimplex

namespace YMGap.Continuum.HarmonicLowerSixCubicDebtCoefficient1330Certificate

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CoreBResidualSimplex

private abbrev PE := RingNormaliser.PolyExpr

/-- Cleared difference
`2916*(A^2-1)^6 - 40320*A*(A+1)^2*(12*(A+1)^2+1)*(2*(A^2-1)+1)^3`
under the shift `A = 1332 + X`. -/
def pCubicDebtCoefficient1330 : PE :=
  let X : PE := .var 0
  let A : PE := .add (.const 1332) X
  let E : PE := .add A (.const 1)
  let d : PE := .add (.pow A 2) (.neg (.const 1))
  .add
    (.mul (.const 2916) (.pow d 6))
    (.neg
      (.mul (.const 40320)
        (.mul A
          (.mul (.pow E 2)
            (.mul (.add (.mul (.const 12) (.pow E 2)) (.const 1))
              (.pow (.add (.mul (.const 2) d) (.const 1)) 3))))))

/-- The shifted cleared difference is coefficientwise nonnegative. -/
theorem pCubicDebtCoefficient1330_coefficients_nonnegative :
    RawCoefficientsNonnegative
      (fastNormalize pCubicDebtCoefficient1330) = true := by
  decide

def coefficient1330Environment (X : Q') (i : Nat) : Q' :=
  if i = 0 then X else 0

private theorem coefficient1330Environment_nonnegative
    (X : Q') (hX : (0 : Q') ≤ X) :
    ∀ i, (0 : Q') ≤ coefficient1330Environment X i := by
  intro i
  unfold coefficient1330Environment
  by_cases hi : i = 0
  · rw [if_pos hi]
    exact hX
  · rw [if_neg hi]
    exact Q'.le_refl' 0

/-- Pointwise nonnegativity for every constructive rational slack `X >= 0`. -/
theorem pCubicDebtCoefficient1330_eval_nonnegative
    (X : Q') (hX : (0 : Q') ≤ X) :
    (0 : Q') ≤ RingNormaliser.eval
      (coefficient1330Environment X) pCubicDebtCoefficient1330 :=
  eval_nonneg_of_fast_coefficients
    (coefficient1330Environment_nonnegative X hX)
    pCubicDebtCoefficient1330_coefficients_nonnegative

#print axioms pCubicDebtCoefficient1330_coefficients_nonnegative
#print axioms pCubicDebtCoefficient1330_eval_nonnegative

end YMGap.Continuum.HarmonicLowerSixCubicDebtCoefficient1330Certificate
