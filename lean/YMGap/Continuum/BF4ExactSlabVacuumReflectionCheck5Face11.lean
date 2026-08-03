import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face10
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face11Source
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face11Target
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem faceSlice5_normal11 :
    compactCovarianceCheck (faceSliceEntry 5 11) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  simp only [fastCompactCovarianceCheck]
  rw [faceSlice5_normal11_source, faceSlice5_normal11_target]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal11
