import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

set_option maxRecDepth 200000
set_option maxHeartbeats 120000000

private theorem surfaceForestGaugeStepUniverseCodes15_left_coordinateCheck_true :
    [1501, 1502, 1503, 1518, 1522, 1524, 1528, 1529].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

private theorem surfaceForestGaugeStepUniverseCodes15_right_coordinateCheck_true :
    [1530, 1534, 1535, 1565, 1584, 1597, 1624, 1630].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

theorem surfaceForestGaugeStepUniverseCodes15_coordinateCheck_true :
    surfaceForestGaugeStepUniverseCodes15.all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  change (([1501, 1502, 1503, 1518, 1522, 1524, 1528, 1529] ++
    [1530, 1534, 1535, 1565, 1584, 1597, 1624, 1630]).all
      decodedSelectedTranslationStepCoordinateCheck = true)
  simp only [List.all_append,
    surfaceForestGaugeStepUniverseCodes15_left_coordinateCheck_true,
    surfaceForestGaugeStepUniverseCodes15_right_coordinateCheck_true, Bool.and_self]

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeStepUniverseCodes15_coordinateCheck_true
