import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face1RawCanonical
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
theorem faceSlice5_normal1_target :
    canon (sparseRaw
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (faceSliceEntry 5 1))).scalar) =
          canon faceSlice5Raw1Canonical := by
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal1_target
