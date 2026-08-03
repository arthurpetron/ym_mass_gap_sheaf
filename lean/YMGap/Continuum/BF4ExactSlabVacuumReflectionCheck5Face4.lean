import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face3
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face4Raw
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face4Target
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem faceSlice5_normal4 :
    compactCovarianceCheck (faceSliceEntry 5 4) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  simp only [fastCompactCovarianceCheck]
  rw [faceSlice5_normal4_raw, faceSlice5_normal4_target]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal4
