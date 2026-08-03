import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face5RawCanonical

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

theorem faceSlice5_normal5_target :
    canon (sparseRaw
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (faceSliceEntry 5 5))).scalar) =
          canon faceSlice5Raw5Canonical := by decide

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal5_target
