import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pCell_five_left_normal :
    RingNormaliser.normalize (pCellNegLeft pv 5) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, -720, -8304, -36000, -72960, -69120,
          -24576]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_five_right_normal :
    RingNormaliser.normalize (pCellNegRight pv 5) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 0, 336, 1440, -3840, -23040, -24576]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_five_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 0, 7344, 48864, 103680, 74880, 9216, 1536])
          (pa
            (pIntPoly pv [0, 0, -720, -8304, -36000, -72960, -69120,
              -24576])
            (pIntPoly pv [0, 0, 0, 336, 1440, -3840, -23040,
              -24576]))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 6624, 40896, 69120, -1920, -82944,
          -47616]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
