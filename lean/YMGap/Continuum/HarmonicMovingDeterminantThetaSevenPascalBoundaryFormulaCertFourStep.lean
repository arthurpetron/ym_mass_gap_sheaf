import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pExpanded_four_step_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, -51438240, -300056400, -504176400, -24494400,
            553573440, 326592000])
          (pm (pc 5670)
            (pIntPoly pv [0, 5760, 39120, 69600, -6720, -99840,
              -57600]))) =
      RingNormaliser.normalize
        (pm (pc 720) (pFormula 4 (pa pv (pc 1)))) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
