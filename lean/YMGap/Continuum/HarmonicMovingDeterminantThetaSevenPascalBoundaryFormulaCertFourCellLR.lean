import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pCell_four_left_normal :
    RingNormaliser.normalize (pCellNegLeft pv 4) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, -5760, -36480, -84480, -84480, -30720]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_four_right_normal :
    RingNormaliser.normalize (pCellNegRight pv 4) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 0, -1920, -15360, -38400, -30720]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_four_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 5760, 44880, 108000, 93120, 23040, 3840])
          (pa
            (pIntPoly pv [0, 0, -5760, -36480, -84480, -84480, -30720])
            (pIntPoly pv [0, 0, 0, -1920, -15360, -38400, -30720]))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 5760, 39120, 69600, -6720, -99840, -57600]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
