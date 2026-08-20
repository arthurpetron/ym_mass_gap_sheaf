import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face4RawCanonical
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face4RawTake
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face4RawDrop

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork

theorem faceSlice4_normal4_raw :
    fastCompactReflectRaw
      (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 4 4)).scalar =
        faceSlice4Raw4Canonical := by
  rw [← List.take_append_drop 32
      (fastCompactReflectRaw
        (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 4 4)).scalar),
    faceSlice4_normal4_raw_take, faceSlice4_normal4_raw_drop,
    List.take_append_drop]
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice4_normal4_raw
