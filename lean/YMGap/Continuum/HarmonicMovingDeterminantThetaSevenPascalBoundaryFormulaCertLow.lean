import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pStep_zero_normal :
    RingNormaliser.normalize (pStep pv 0) =
      RingNormaliser.normalize (pm (pc 720) (pFormula 0 (pa pv (pc 1)))) := by decide

set_option maxRecDepth 100000 in
theorem pStep_one_normal :
    RingNormaliser.normalize (pStep pv 1) =
      RingNormaliser.normalize (pm (pc 720) (pFormula 1 (pa pv (pc 1)))) := by decide

set_option maxRecDepth 100000 in
theorem pStep_two_normal :
    RingNormaliser.normalize (pStep pv 2) =
      RingNormaliser.normalize (pm (pc 720) (pFormula 2 (pa pv (pc 1)))) := by decide

set_option maxRecDepth 100000 in
theorem pStep_three_normal :
    RingNormaliser.normalize (pStep pv 3) =
      RingNormaliser.normalize (pm (pc 720) (pFormula 3 (pa pv (pc 1)))) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
