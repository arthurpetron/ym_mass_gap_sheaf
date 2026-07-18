import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

private theorem highRows_block3_row4_support :
    highRowSupport 3 4 = true := by decide

private theorem highRows_block3_row4_coefficients0 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 3 4 0 6) = true := by decide

private theorem highRows_block3_row4_coefficients1 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 3 4 6 10) = true := by decide

private theorem highRows_block3_row4_coefficients2 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 3 4 16 14) = true := by decide

private theorem highRows_block3_row4_coefficients3 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 3 4 30 20) = true := by decide

private theorem highRows_block3_row4_coefficients4 :
    denseMRowNonnegative (highRowDenseCoefficientTail 3 4 50) = true := by decide

theorem highRows_block3_row4 :
    ((highRowsBlockTail 3 4).take 1).all highRowPred = true :=
  highRow_certificate_of_staged_dense_coefficients 3 4
    highRows_block3_row4_support
    highRows_block3_row4_coefficients0
    highRows_block3_row4_coefficients1
    highRows_block3_row4_coefficients2
    highRows_block3_row4_coefficients3
    highRows_block3_row4_coefficients4

#print axioms highRows_block3_row4

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows
