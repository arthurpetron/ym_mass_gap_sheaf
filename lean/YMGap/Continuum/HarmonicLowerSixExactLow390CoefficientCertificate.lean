/-
# Recentered low-mode coefficient certificate for the exact lower-six head

For the eight modes below the square-root-slack chart, the exact cleared
numerator is expanded at `D = 392 + X`, corresponding to `k = 390 + X`.
Every coefficient is checked nonnegative by kernel reduction.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

namespace YMGap.Continuum.HarmonicLowerSixExactLow390CoefficientCertificate

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

/-- Low-mode substitution `D = 392 + X` at a fixed mode. -/
def pExactLowerLow390 (n : Nat) : RingNormaliser.PolyExpr :=
  pExactLowerNumerator (.add (.const 392) (.var 0)) (.const n)

/-- All eight shifted numerator polynomials have nonnegative coefficients. -/
theorem pExactLowerLow390_coefficients_nonnegative :
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow390 0)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow390 1)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow390 2)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow390 3)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow390 4)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow390 5)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow390 6)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow390 7)) = true := by
  decide

#print axioms pExactLowerLow390_coefficients_nonnegative

end YMGap.Continuum.HarmonicLowerSixExactLow390CoefficientCertificate
