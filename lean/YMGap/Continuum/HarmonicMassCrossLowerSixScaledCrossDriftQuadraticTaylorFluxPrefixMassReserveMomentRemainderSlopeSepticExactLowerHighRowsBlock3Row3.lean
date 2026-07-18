import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

private theorem highRows_block3_row3_support :
    highRowSupport 3 3 = true := by decide

private theorem highRows_block3_row3_coefficients0 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 3 3 0 6) = true := by decide

private theorem highRows_block3_row3_coefficients1 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 3 3 6 10) = true := by decide

private theorem highRows_block3_row3_coefficients2 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 3 3 16 14) = true := by decide

private theorem highRows_block3_row3_coefficients3 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 3 3 30 20) = true := by decide

private theorem highRows_block3_row3_coefficients4 :
    denseMRowNonnegative (highRowDenseCoefficientTail 3 3 50) = true := by decide

theorem highRows_block3_row3 :
    ((highRowsBlockTail 3 3).take 1).all highRowPred = true :=
  highRow_certificate_of_staged_dense_coefficients 3 3
    highRows_block3_row3_support
    highRows_block3_row3_coefficients0
    highRows_block3_row3_coefficients1
    highRows_block3_row3_coefficients2
    highRows_block3_row3_coefficients3
    highRows_block3_row3_coefficients4

#print axioms highRows_block3_row3

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows
