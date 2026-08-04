import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

set_option maxRecDepth 200000
set_option maxHeartbeats 120000000

private theorem surfaceForestGaugeStepUniverseCodes24_left_coordinateCheck_true :
    [2450, 2452, 2454, 2456, 2458, 2462, 2484, 2494].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

private theorem surfaceForestGaugeStepUniverseCodes24_right_coordinateCheck_true :
    [2497, 2500, 2503, 2506, 2508, 2512, 2514, 2516].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

theorem surfaceForestGaugeStepUniverseCodes24_coordinateCheck_true :
    surfaceForestGaugeStepUniverseCodes24.all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  change (([2450, 2452, 2454, 2456, 2458, 2462, 2484, 2494] ++
    [2497, 2500, 2503, 2506, 2508, 2512, 2514, 2516]).all
      decodedSelectedTranslationStepCoordinateCheck = true)
  simp only [List.all_append,
    surfaceForestGaugeStepUniverseCodes24_left_coordinateCheck_true,
    surfaceForestGaugeStepUniverseCodes24_right_coordinateCheck_true, Bool.and_self]

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeStepUniverseCodes24_coordinateCheck_true
