import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face10RawCanonical

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork

theorem faceSlice5_normal10_raw_drop :
    (fastCompactReflectRaw
      (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 10)).scalar).drop 32 =
        faceSlice5Raw10Canonical.drop 32 := by
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal10_raw_drop
