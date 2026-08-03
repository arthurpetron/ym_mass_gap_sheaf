import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face0
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face1
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face2
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face3
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face4
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face5
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face6
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face7
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face8
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face9
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face10
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face11

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private theorem faceSlice4_entries : faceSlice 4 =
    [faceSliceEntry 4 0, faceSliceEntry 4 1, faceSliceEntry 4 2,
     faceSliceEntry 4 3, faceSliceEntry 4 4, faceSliceEntry 4 5,
     faceSliceEntry 4 6, faceSliceEntry 4 7, faceSliceEntry 4 8,
     faceSliceEntry 4 9, faceSliceEntry 4 10, faceSliceEntry 4 11] := by decide

theorem faceSlice4_normal : (faceSlice 4).all compactCovarianceCheck = true := by
  rw [faceSlice4_entries]
  exact allTwelveNormal compactCovarianceCheck _ _ _ _ _ _ _ _ _ _ _ _
    faceSlice4_normal0 faceSlice4_normal1 faceSlice4_normal2 faceSlice4_normal3
    faceSlice4_normal4 faceSlice4_normal5 faceSlice4_normal6 faceSlice4_normal7
    faceSlice4_normal8 faceSlice4_normal9 faceSlice4_normal10 faceSlice4_normal11

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
