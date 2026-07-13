import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pExpanded_five_step_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, -18118080, -104963040, -299829600, -388281600,
            49351680, 489162240, 272678400])
          (pm (pc 5670)
            (pIntPoly pv [0, 0, 6624, 40896, 69120, -1920, -82944,
              -47616]))) =
      RingNormaliser.normalize
        (pm (pc 720) (pFormula 5 (pa pv (pc 1)))) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
