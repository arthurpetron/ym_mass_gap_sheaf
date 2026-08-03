import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face9RawCanonical
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face9RawTake
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face9RawDrop

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork

theorem faceSlice5_normal9_raw :
    fastCompactReflectRaw
      (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 9)).scalar =
        faceSlice5Raw9Canonical := by
  rw [← List.take_append_drop 32
      (fastCompactReflectRaw
        (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 9)).scalar),
    faceSlice5_normal9_raw_take, faceSlice5_normal9_raw_drop,
    List.take_append_drop]
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal9_raw
