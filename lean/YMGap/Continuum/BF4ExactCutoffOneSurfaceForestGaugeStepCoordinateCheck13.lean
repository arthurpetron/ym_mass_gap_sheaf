import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

set_option maxRecDepth 200000
set_option maxHeartbeats 120000000

private theorem surfaceForestGaugeStepUniverseCodes13_left_coordinateCheck_true :
    [1375, 1386, 1398, 1404, 1412, 1415, 1422, 1424].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

private theorem surfaceForestGaugeStepUniverseCodes13_right_coordinateCheck_true :
    [1426, 1428, 1432, 1433, 1434, 1437, 1438, 1439].all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  decide

theorem surfaceForestGaugeStepUniverseCodes13_coordinateCheck_true :
    surfaceForestGaugeStepUniverseCodes13.all
      decodedSelectedTranslationStepCoordinateCheck = true := by
  change (([1375, 1386, 1398, 1404, 1412, 1415, 1422, 1424] ++
    [1426, 1428, 1432, 1433, 1434, 1437, 1438, 1439]).all
      decodedSelectedTranslationStepCoordinateCheck = true)
  simp only [List.all_append,
    surfaceForestGaugeStepUniverseCodes13_left_coordinateCheck_true,
    surfaceForestGaugeStepUniverseCodes13_right_coordinateCheck_true, Bool.and_self]

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeStepUniverseCodes13_coordinateCheck_true
