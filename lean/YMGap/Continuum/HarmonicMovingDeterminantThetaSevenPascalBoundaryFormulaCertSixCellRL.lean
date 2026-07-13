import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

private def x : PE := pa (pm (pc 4) pv) (pc 3)

set_option maxRecDepth 100000 in
theorem pChoose_six_RL_step1_normal :
    RingNormaliser.normalize (pa (pc (-15)) (pm x (pIntPoly pv [1]))) =
      RingNormaliser.normalize (pIntPoly pv [-12, 4]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_RL_step2_normal :
    RingNormaliser.normalize
        (pa (pc 85) (pm x (pIntPoly pv [-12, 4]))) =
      RingNormaliser.normalize (pIntPoly pv [49, -36, 16]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_RL_step3_normal :
    RingNormaliser.normalize
        (pa (pc (-225)) (pm x (pIntPoly pv [49, -36, 16]))) =
      RingNormaliser.normalize (pIntPoly pv [-78, 88, -96, 64]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_RL_step4_normal :
    RingNormaliser.normalize
        (pa (pc 274) (pm x (pIntPoly pv [-78, 88, -96, 64]))) =
      RingNormaliser.normalize (pIntPoly pv [40, -48, 64, -192, 256]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_RL_step5_normal :
    RingNormaliser.normalize
        (pa (pc (-120))
          (pm x (pIntPoly pv [40, -48, 64, -192, 256]))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 16, 0, -320, 0, 1024]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_RL_step6_normal :
    RingNormaliser.normalize
        (pa (pc 0)
          (pm x (pIntPoly pv [0, 16, 0, -320, 0, 1024]))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 48, 64, -960, -1280, 3072, 4096]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
