/-
Kernel-checked dense coefficient certificate for the high-mode exact lower
polynomial.

This module intentionally contains the expensive closed computation while the
generic dense-convolution semantics live in the imported module.  Lake can
therefore cache the arithmetic certificate independently of later semantic
bridge work.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighDenseRows

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighDenseCertificate

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Constructive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighDenseRows

/-- Every integer coefficient of the complete two-variable high-mode
numerator is nonnegative.  This is a closed kernel reduction; no measured
number or external oracle enters the proof. -/
theorem pExactLowerHigh_dense_coefficients_nonnegative :
    denseRowsNonnegative pExactLowerHigh = true := by
  decide

/-- The cleared high-mode numerator is nonnegative after the physical slack
substitution for every nonnegative pair `(M,Z)`. -/
theorem pExactLowerHigh_eval_nonnegative (M Z : Q')
    (hM : (0 : Q') ≤ M) (hZ : (0 : Q') ≤ Z) :
    (0 : Q') ≤ RingNormaliser.eval (highEnvironment M Z) pExactLowerHigh :=
  eval_nonnegative_of_dense_rows
    pExactLowerHigh_dense_coefficients_nonnegative M Z hM hZ

#print axioms pExactLowerHigh_dense_coefficients_nonnegative
#print axioms pExactLowerHigh_eval_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighDenseCertificate
