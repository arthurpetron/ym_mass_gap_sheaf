import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

set_option maxRecDepth 200000
set_option maxHeartbeats 120000000

private theorem surfaceForestGaugeStepUniverseCodes25_left_coordinateCheck_true :
    [2522, 2524, 2525, 2526, 2554, 2590, 2622, 2650].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

private theorem surfaceForestGaugeStepUniverseCodes25_right_coordinateCheck_true :
    [2682, 2783, 2815, 3140, 3143, 3146, 3148, 3150].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

theorem surfaceForestGaugeStepUniverseCodes25_coordinateCheck_true :
    surfaceForestGaugeStepUniverseCodes25.all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  change (([2522, 2524, 2525, 2526, 2554, 2590, 2622, 2650] ++
    [2682, 2783, 2815, 3140, 3143, 3146, 3148, 3150]).all
      decodedSelectedTranslationStepCoordinateCheck = true)
  simp only [List.all_append,
    surfaceForestGaugeStepUniverseCodes25_left_coordinateCheck_true,
    surfaceForestGaugeStepUniverseCodes25_right_coordinateCheck_true, Bool.and_self]

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeStepUniverseCodes25_coordinateCheck_true
