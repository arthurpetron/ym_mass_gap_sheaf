import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pOld_four_A_normal :
    RingNormaliser.normalize (pOldFourA pv) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, -48988800, -288489600, -315705600,
          304819200, 348364800]) := by decide

set_option maxRecDepth 100000 in
theorem pOld_four_B_normal :
    RingNormaliser.normalize (pOldFourB pv) =
      RingNormaliser.normalize
        (pIntPoly pv [0, -51438240, -251067600, -215686800, 291211200,
          248754240, -21772800]) := by decide

set_option maxRecDepth 100000 in
theorem pOld_four_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 0, -48988800, -288489600, -315705600,
            304819200, 348364800])
          (pIntPoly pv [0, -51438240, -251067600, -215686800, 291211200,
            248754240, -21772800])) =
      RingNormaliser.normalize
        (pIntPoly pv [0, -51438240, -300056400, -504176400, -24494400,
          553573440, 326592000]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
