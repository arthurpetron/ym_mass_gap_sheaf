import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pOld_five_A_normal :
    RingNormaliser.normalize (pOldFiveA pv) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, -31207680, -237323520, -508032000,
          -108864000, 571898880, 313528320]) := by decide

set_option maxRecDepth 100000 in
theorem pOld_five_B_normal :
    RingNormaliser.normalize (pOldFiveB pv) =
      RingNormaliser.normalize
        (pIntPoly pv [0, -18118080, -73755360, -62506080, 119750400,
          158215680, -82736640, -40849920]) := by decide

set_option maxRecDepth 100000 in
theorem pOld_five_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 0, -31207680, -237323520, -508032000,
            -108864000, 571898880, 313528320])
          (pIntPoly pv [0, -18118080, -73755360, -62506080, 119750400,
            158215680, -82736640, -40849920])) =
      RingNormaliser.normalize
        (pIntPoly pv [0, -18118080, -104963040, -299829600, -388281600,
          49351680, 489162240, 272678400]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
