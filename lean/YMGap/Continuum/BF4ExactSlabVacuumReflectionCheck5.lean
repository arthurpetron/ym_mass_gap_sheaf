import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face0
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face1
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face2
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face3
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face4
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face5
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face6
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face7
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face8
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face9
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face10
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face11

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private theorem faceSlice5_entries : faceSlice 5 =
    [faceSliceEntry 5 0, faceSliceEntry 5 1, faceSliceEntry 5 2,
     faceSliceEntry 5 3, faceSliceEntry 5 4, faceSliceEntry 5 5,
     faceSliceEntry 5 6, faceSliceEntry 5 7, faceSliceEntry 5 8,
     faceSliceEntry 5 9, faceSliceEntry 5 10, faceSliceEntry 5 11] := by decide

theorem faceSlice5_normal : (faceSlice 5).all compactCovarianceCheck = true := by
  rw [faceSlice5_entries]
  exact allTwelveNormal compactCovarianceCheck _ _ _ _ _ _ _ _ _ _ _ _
    faceSlice5_normal0 faceSlice5_normal1 faceSlice5_normal2 faceSlice5_normal3
    faceSlice5_normal4 faceSlice5_normal5 faceSlice5_normal6 faceSlice5_normal7
    faceSlice5_normal8 faceSlice5_normal9 faceSlice5_normal10 faceSlice5_normal11

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
