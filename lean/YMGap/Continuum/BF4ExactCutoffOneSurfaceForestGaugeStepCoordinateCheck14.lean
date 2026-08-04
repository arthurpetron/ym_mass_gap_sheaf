import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

set_option maxRecDepth 200000
set_option maxHeartbeats 120000000

private theorem surfaceForestGaugeStepUniverseCodes14_left_coordinateCheck_true :
    [1452, 1456, 1465, 1466, 1469, 1470, 1471, 1473].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

private theorem surfaceForestGaugeStepUniverseCodes14_right_coordinateCheck_true :
    [1479, 1484, 1488, 1490, 1492, 1496, 1497, 1498].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

theorem surfaceForestGaugeStepUniverseCodes14_coordinateCheck_true :
    surfaceForestGaugeStepUniverseCodes14.all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  change (([1452, 1456, 1465, 1466, 1469, 1470, 1471, 1473] ++
    [1479, 1484, 1488, 1490, 1492, 1496, 1497, 1498]).all
      decodedSelectedTranslationStepCoordinateCheck = true)
  simp only [List.all_append,
    surfaceForestGaugeStepUniverseCodes14_left_coordinateCheck_true,
    surfaceForestGaugeStepUniverseCodes14_right_coordinateCheck_true, Bool.and_self]

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeStepUniverseCodes14_coordinateCheck_true
