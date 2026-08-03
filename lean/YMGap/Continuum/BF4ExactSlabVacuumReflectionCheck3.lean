import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face0
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face1
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face2
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face3
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face4
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face5
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face6
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face7
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face8
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face9
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face10
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face11

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private theorem faceSlice3_entries : faceSlice 3 =
    [faceSliceEntry 3 0, faceSliceEntry 3 1, faceSliceEntry 3 2,
     faceSliceEntry 3 3, faceSliceEntry 3 4, faceSliceEntry 3 5,
     faceSliceEntry 3 6, faceSliceEntry 3 7, faceSliceEntry 3 8,
     faceSliceEntry 3 9, faceSliceEntry 3 10, faceSliceEntry 3 11] := by decide

theorem faceSlice3_normal : (faceSlice 3).all compactCovarianceCheck = true := by
  rw [faceSlice3_entries]
  exact allTwelveNormal compactCovarianceCheck _ _ _ _ _ _ _ _ _ _ _ _
    faceSlice3_normal0 faceSlice3_normal1 faceSlice3_normal2 faceSlice3_normal3
    faceSlice3_normal4 faceSlice3_normal5 faceSlice3_normal6 faceSlice3_normal7
    faceSlice3_normal8 faceSlice3_normal9 faceSlice3_normal10 faceSlice3_normal11

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
