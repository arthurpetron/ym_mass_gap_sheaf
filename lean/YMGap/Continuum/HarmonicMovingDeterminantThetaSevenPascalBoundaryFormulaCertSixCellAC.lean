import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pCell_six_A_normal :
    RingNormaliser.normalize (pCellA pv 6) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 0, 5040, 36960, 80640, 53760]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_six_C_normal :
    RingNormaliser.normalize (pCellC pv 6) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, -384, -1216, 128, 4160, 5504, 2816, 512]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_six_pos_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 0, 0, 5040, 36960, 80640, 53760])
          (pIntPoly pv [0, 0, -384, -1216, 128, 4160, 5504, 2816,
            512])) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, -384, 3824, 37088, 84800, 59264, 2816,
          512]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
