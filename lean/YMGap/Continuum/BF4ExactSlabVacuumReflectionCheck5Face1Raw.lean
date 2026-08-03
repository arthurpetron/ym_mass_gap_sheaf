import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face1RawCanonical
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face1RawTake
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face1RawDrop
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
theorem faceSlice5_normal1_raw :
    fastCompactReflectRaw
      (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 1)).scalar =
        faceSlice5Raw1Canonical := by
  rw [← List.take_append_drop 32
      (fastCompactReflectRaw
        (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 1)).scalar),
    faceSlice5_normal1_raw_take, faceSlice5_normal1_raw_drop,
    List.take_append_drop]
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal1_raw
