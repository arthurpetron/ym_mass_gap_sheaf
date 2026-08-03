import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face2
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem faceSlice4_normal3 :
    compactCovarianceCheck (faceSliceEntry 4 3) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
