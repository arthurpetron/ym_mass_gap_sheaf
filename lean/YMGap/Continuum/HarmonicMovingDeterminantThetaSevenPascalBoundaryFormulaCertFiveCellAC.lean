import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pCell_five_A_normal :
    RingNormaliser.normalize (pCellA pv 5) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 5040, 36960, 80640, 53760]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_five_C_normal :
    RingNormaliser.normalize (pCellC pv 5) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 2304, 11904, 23040, 21120, 9216, 1536]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_five_pos_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 0, 5040, 36960, 80640, 53760])
          (pIntPoly pv [0, 0, 2304, 11904, 23040, 21120, 9216,
            1536])) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 7344, 48864, 103680, 74880, 9216,
          1536]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
