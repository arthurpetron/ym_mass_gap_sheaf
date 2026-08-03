import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face9
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face10Source
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face10Target
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem faceSlice5_normal10 :
    compactCovarianceCheck (faceSliceEntry 5 10) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  simp only [fastCompactCovarianceCheck]
  rw [faceSlice5_normal10_source, faceSlice5_normal10_target]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal10
