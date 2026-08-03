import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face3RawCanonical

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork

theorem faceSlice4_normal3_raw_take :
    (fastCompactReflectRaw
      (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 4 3)).scalar).take 32 =
        faceSlice4Raw3Canonical.take 32 := by
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice4_normal3_raw_take
