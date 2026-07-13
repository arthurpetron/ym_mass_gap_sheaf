import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pCell_four_A_normal :
    RingNormaliser.normalize (pCellA pv 4) =
      RingNormaliser.normalize (pIntPoly pv [0, 0, 15120, 50400, 40320]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_four_C_normal :
    RingNormaliser.normalize (pCellC pv 4) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 5760, 29760, 57600, 52800, 23040, 3840]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_four_pos_expanded_normal :
    RingNormaliser.normalize
        (pa (pIntPoly pv [0, 0, 15120, 50400, 40320])
          (pIntPoly pv [0, 5760, 29760, 57600, 52800, 23040, 3840])) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 5760, 44880, 108000, 93120, 23040, 3840]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
