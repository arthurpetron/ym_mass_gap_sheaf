import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face2
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face3Raw
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face3Target
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem faceSlice4_normal3 :
    compactCovarianceCheck (faceSliceEntry 4 3) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  simp only [fastCompactCovarianceCheck]
  rw [faceSlice4_normal3_raw, faceSlice4_normal3_target]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice4_normal3
