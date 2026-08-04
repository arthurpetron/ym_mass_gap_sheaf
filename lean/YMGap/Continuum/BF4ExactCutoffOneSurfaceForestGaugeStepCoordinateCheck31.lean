import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

set_option maxRecDepth 200000
set_option maxHeartbeats 120000000

private theorem surfaceForestGaugeStepUniverseCodes31_left_coordinateCheck_true :
    [3454, 3455, 3492, 3495, 3502, 3506, 3508, 3512].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

private theorem surfaceForestGaugeStepUniverseCodes31_right_coordinateCheck_true :
    [3513, 3514, 3518, 3519, 3553, 3559, 3564, 3568].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

theorem surfaceForestGaugeStepUniverseCodes31_coordinateCheck_true :
    surfaceForestGaugeStepUniverseCodes31.all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  change (([3454, 3455, 3492, 3495, 3502, 3506, 3508, 3512] ++
    [3513, 3514, 3518, 3519, 3553, 3559, 3564, 3568]).all
      decodedSelectedTranslationStepCoordinateCheck = true)
  simp only [List.all_append,
    surfaceForestGaugeStepUniverseCodes31_left_coordinateCheck_true,
    surfaceForestGaugeStepUniverseCodes31_right_coordinateCheck_true, Bool.and_self]

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeStepUniverseCodes31_coordinateCheck_true
