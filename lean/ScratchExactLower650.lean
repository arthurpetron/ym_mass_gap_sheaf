import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

namespace ScratchExactLower650

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Continuum
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

def low650 (n : Nat) : RingNormaliser.PolyExpr :=
  pExactLowerNumerator (.add (.const 249) (.var 0)) (.const n)

theorem low650_nonnegative :
    RawCoefficientsNonnegative (fastNormalize (low650 0)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (low650 1)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (low650 2)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (low650 3)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (low650 4)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (low650 5)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (low650 6)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (low650 7)) = true := by
  decide

#print axioms low650_nonnegative

end ScratchExactLower650
