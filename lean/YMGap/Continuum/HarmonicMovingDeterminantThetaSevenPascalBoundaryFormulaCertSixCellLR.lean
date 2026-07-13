import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

private def x : PE := pa (pm (pc 4) pv) (pc 5)

set_option maxRecDepth 100000 in
theorem pChoose_six_LL_step1_normal :
    RingNormaliser.normalize (pa (pc (-15)) (pm x (pIntPoly pv [1]))) =
      RingNormaliser.normalize (pIntPoly pv [-10, 4]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LL_step2_normal :
    RingNormaliser.normalize
        (pa (pc 85) (pm x (pIntPoly pv [-10, 4]))) =
      RingNormaliser.normalize (pIntPoly pv [35, -20, 16]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LL_step3_normal :
    RingNormaliser.normalize
        (pa (pc (-225)) (pm x (pIntPoly pv [35, -20, 16]))) =
      RingNormaliser.normalize (pIntPoly pv [-50, 40, 0, 64]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LL_step4_normal :
    RingNormaliser.normalize
        (pa (pc 274) (pm x (pIntPoly pv [-50, 40, 0, 64]))) =
      RingNormaliser.normalize (pIntPoly pv [24, 0, 160, 320, 256]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LL_step5_normal :
    RingNormaliser.normalize
        (pa (pc (-120))
          (pm x (pIntPoly pv [24, 0, 160, 320, 256]))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 96, 800, 2240, 2560, 1024]) := by decide

set_option maxRecDepth 100000 in
theorem pChoose_six_LL_step6_normal :
    RingNormaliser.normalize
        (pa (pc 0)
          (pm x (pIntPoly pv [0, 96, 800, 2240, 2560, 1024]))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 480, 4384, 14400, 21760, 15360, 4096]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
