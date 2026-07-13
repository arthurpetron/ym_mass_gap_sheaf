import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pCell_six_RR_normal :
    RingNormaliser.normalize (pCellNegRR pv 6) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 0, 48, -64, -960, 1280, 3072,
          -4096]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
