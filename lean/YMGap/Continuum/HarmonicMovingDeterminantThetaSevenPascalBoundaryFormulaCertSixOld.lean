import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pOld_six_A_normal :
    RingNormaliser.normalize (pOldSixA pv) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 6305040, 22725360, -89812800, -389188800,
          -191600640, 409328640, 232243200]) := by decide

set_option maxRecDepth 100000 in
theorem pOld_six_B_normal :
    RingNormaliser.normalize (pOldSixB pv) =
      RingNormaliser.normalize
        (pIntPoly pv [0, -14605920, -44439840, -30712320, 19867680,
          128308320, 120839040, -132209280, -47278080, 230400]) := by decide

set_option maxRecDepth 100000 in
theorem pOld_six_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 0, 6305040, 22725360, -89812800, -389188800,
            -191600640, 409328640, 232243200])
          (pIntPoly pv [0, -14605920, -44439840, -30712320, 19867680,
            128308320, 120839040, -132209280, -47278080, 230400])) =
      RingNormaliser.normalize
        (pIntPoly pv [0, -14605920, -38134800, -7986960, -69945120,
          -260880480, -70761600, 277119360, 184965120, 230400]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
