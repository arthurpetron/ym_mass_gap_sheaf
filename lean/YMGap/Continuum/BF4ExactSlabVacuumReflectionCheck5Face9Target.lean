import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face9Canonical

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

theorem faceSlice5_normal9_target :
    canon (sparseRaw
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (faceSliceEntry 5 9))).scalar) =
          faceSlice5Normal9Canonical := by
  decide

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal9_target
