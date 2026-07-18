import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

private theorem highRows_block4_row0_support :
    highRowSupport 4 0 = true := by decide

private theorem highRows_block4_row0_coefficients0 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 4 0 0 6) = true := by decide

private theorem highRows_block4_row0_coefficients1 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 4 0 6 10) = true := by decide

private theorem highRows_block4_row0_coefficients2 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 4 0 16 14) = true := by decide

private theorem highRows_block4_row0_coefficients3 :
    denseMRowNonnegative (highRowDenseCoefficientSlice 4 0 30 20) = true := by decide

private theorem highRows_block4_row0_coefficients4 :
    denseMRowNonnegative (highRowDenseCoefficientTail 4 0 50) = true := by decide

theorem highRows_block4_row0 :
    ((highRowsBlockTail 4 0).take 1).all highRowPred = true :=
  highRow_certificate_of_staged_dense_coefficients 4 0
    highRows_block4_row0_support
    highRows_block4_row0_coefficients0
    highRows_block4_row0_coefficients1
    highRows_block4_row0_coefficients2
    highRows_block4_row0_coefficients3
    highRows_block4_row0_coefficients4

#print axioms highRows_block4_row0

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows
