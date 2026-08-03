import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face10Raw
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5TailCanonical

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.RingNormaliser

theorem faceSlice5_normal10_source :
    canon (fastCompactReflectRaw
      (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 10)).scalar) =
        faceSlice5Normal10Canonical := by
  rw [faceSlice5_normal10_raw]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal10_source
