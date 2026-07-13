import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormulaExpressions

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

set_option maxRecDepth 100000 in
theorem pCell_six_LL_expanded_normal :
    RingNormaliser.normalize
        (pn (pm pv (pm pv
          (pIntPoly pv [0, 480, 4384, 14400, 21760, 15360, 4096])))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 0, -480, -4384, -14400, -21760, -15360,
          -4096]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_six_LR_expanded_normal :
    RingNormaliser.normalize
        (pn (pm pv (pm pv (pm (pc 3)
          (pIntPoly pv [0, -96, -416, 960, 6400, 9216, 4096]))))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 0, 288, 1248, -2880, -19200, -27648,
          -12288]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_six_RL_expanded_normal :
    RingNormaliser.normalize
        (pn (pm pv (pm pv (pm (pc 3)
          (pIntPoly pv [0, 48, 64, -960, -1280, 3072, 4096]))))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 0, -144, -192, 2880, 3840, -9216,
          -12288]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_six_left_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 0, 0, -480, -4384, -14400, -21760, -15360,
            -4096])
          (pIntPoly pv [0, 0, 0, 288, 1248, -2880, -19200, -27648,
            -12288])) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 0, -192, -3136, -17280, -40960, -43008,
          -16384]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_six_right_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 0, 0, -144, -192, 2880, 3840, -9216,
            -12288])
          (pIntPoly pv [0, 0, 0, 48, -64, -960, 1280, 3072,
            -4096])) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, 0, -96, -256, 1920, 5120, -6144,
          -16384]) := by decide

set_option maxRecDepth 100000 in
theorem pCell_six_expanded_normal :
    RingNormaliser.normalize
        (pa
          (pIntPoly pv [0, 0, -384, 3824, 37088, 84800, 59264, 2816,
            512])
          (pa
            (pIntPoly pv [0, 0, 0, -192, -3136, -17280, -40960, -43008,
              -16384])
            (pIntPoly pv [0, 0, 0, -96, -256, 1920, 5120, -6144,
              -16384]))) =
      RingNormaliser.normalize
        (pIntPoly pv [0, 0, -384, 3536, 33696, 69440, 23424, -46336,
          -32256]) := by decide

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
