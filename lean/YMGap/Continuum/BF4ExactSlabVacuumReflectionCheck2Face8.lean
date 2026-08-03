import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face7
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem faceSlice2_normal8 :
    compactCovarianceCheck (faceSliceEntry 2 8) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
