import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face0
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face1
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face2
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face3
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face4
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face5
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face6
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face7
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face8
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face9
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face10
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face11

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private theorem faceSlice1_entries : faceSlice 1 =
    [faceSliceEntry 1 0, faceSliceEntry 1 1, faceSliceEntry 1 2,
     faceSliceEntry 1 3, faceSliceEntry 1 4, faceSliceEntry 1 5,
     faceSliceEntry 1 6, faceSliceEntry 1 7, faceSliceEntry 1 8,
     faceSliceEntry 1 9, faceSliceEntry 1 10, faceSliceEntry 1 11] := by decide

theorem faceSlice1_normal : (faceSlice 1).all compactCovarianceCheck = true := by
  rw [faceSlice1_entries]
  exact allTwelveNormal compactCovarianceCheck _ _ _ _ _ _ _ _ _ _ _ _
    faceSlice1_normal0 faceSlice1_normal1 faceSlice1_normal2 faceSlice1_normal3
    faceSlice1_normal4 faceSlice1_normal5 faceSlice1_normal6 faceSlice1_normal7
    faceSlice1_normal8 faceSlice1_normal9 faceSlice1_normal10 faceSlice1_normal11

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
