import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pExpanded_six_step_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, -14605920, -38134800, -7986960, -69945120,
            -260880480, -70761600, 277119360, 184965120, 230400])
          (pm (pc 5670)
            (pIntPoly pv [0, 0, -384, 3536, 33696, 69440, 23424, -46336,
              -32256]))) =
      RingNormaliser.normalize
        (pm (pc 720) (pFormula 6 (pa pv (pc 1)))) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
