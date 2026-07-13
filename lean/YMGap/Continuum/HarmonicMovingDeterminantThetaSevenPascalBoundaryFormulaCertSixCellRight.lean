import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

private def x : PE := pa (pm (pc 4) pv) (pc 4)

set_option maxRecDepth 100000 in
theorem pChoose_six_LR_step1_normal :
    RingNormaliser.normalize (pa (pc (-15)) (pm x (pIntPoly pv [1]))) =
      RingNormaliser.normalize (pIntPoly pv [-11, 4]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LR_step2_normal :
    RingNormaliser.normalize
        (pa (pc 85) (pm x (pIntPoly pv [-11, 4]))) =
      RingNormaliser.normalize (pIntPoly pv [41, -28, 16]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LR_step3_normal :
    RingNormaliser.normalize
        (pa (pc (-225)) (pm x (pIntPoly pv [41, -28, 16]))) =
      RingNormaliser.normalize (pIntPoly pv [-61, 52, -48, 64]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LR_step4_normal :
    RingNormaliser.normalize
        (pa (pc 274) (pm x (pIntPoly pv [-61, 52, -48, 64]))) =
      RingNormaliser.normalize (pIntPoly pv [30, -36, 16, 64, 256]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LR_step5_normal :
    RingNormaliser.normalize
        (pa (pc (-120))
          (pm x (pIntPoly pv [30, -36, 16, 64, 256]))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, -24, -80, 320, 1280, 1024]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LR_step6_normal :
    RingNormaliser.normalize
        (pa (pc 0)
          (pm x (pIntPoly pv [0, -24, -80, 320, 1280, 1024]))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, -96, -416, 960, 6400, 9216, 4096]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
