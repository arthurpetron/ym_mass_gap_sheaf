import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

set_option maxRecDepth 200000
set_option maxHeartbeats 120000000

private theorem surfaceForestGaugeStepUniverseCodes30_left_coordinateCheck_true :
    [3358, 3359, 3361, 3364, 3370, 3428, 3431, 3436].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

private theorem surfaceForestGaugeStepUniverseCodes30_right_coordinateCheck_true :
    [3438, 3440, 3442, 3444, 3448, 3449, 3450, 3453].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

theorem surfaceForestGaugeStepUniverseCodes30_coordinateCheck_true :
    surfaceForestGaugeStepUniverseCodes30.all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  change (([3358, 3359, 3361, 3364, 3370, 3428, 3431, 3436] ++
    [3438, 3440, 3442, 3444, 3448, 3449, 3450, 3453]).all
      decodedSelectedTranslationStepCoordinateCheck = true)
  simp only [List.all_append,
    surfaceForestGaugeStepUniverseCodes30_left_coordinateCheck_true,
    surfaceForestGaugeStepUniverseCodes30_right_coordinateCheck_true, Bool.and_self]

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeStepUniverseCodes30_coordinateCheck_true
