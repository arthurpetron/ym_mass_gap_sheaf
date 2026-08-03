import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face1RawCanonical
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
theorem faceSlice5_normal1_raw_drop :
    (fastCompactReflectRaw
      (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 1)).scalar).drop 32 =
        faceSlice5Raw1Canonical.drop 32 := by
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal1_raw_drop
