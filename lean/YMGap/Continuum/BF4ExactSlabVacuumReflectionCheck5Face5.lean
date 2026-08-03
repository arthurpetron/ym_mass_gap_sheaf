import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face4
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face5Raw
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face5Target
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem faceSlice5_normal5 :
    compactCovarianceCheck (faceSliceEntry 5 5) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  simp only [fastCompactCovarianceCheck]
  rw [faceSlice5_normal5_raw, faceSlice5_normal5_target]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
