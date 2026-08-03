import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem faceSlice3_normal0 :
    compactCovarianceCheck (faceSliceEntry 3 0) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
