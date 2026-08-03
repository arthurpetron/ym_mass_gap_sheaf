import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face0
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face1
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face2
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face3
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face4
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face5
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face6
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face7
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face8
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face9
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face10
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0Face11

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private theorem faceSlice0_entries : faceSlice 0 =
    [faceSliceEntry 0 0, faceSliceEntry 0 1, faceSliceEntry 0 2,
     faceSliceEntry 0 3, faceSliceEntry 0 4, faceSliceEntry 0 5,
     faceSliceEntry 0 6, faceSliceEntry 0 7, faceSliceEntry 0 8,
     faceSliceEntry 0 9, faceSliceEntry 0 10, faceSliceEntry 0 11] := by decide

theorem faceSlice0_normal : (faceSlice 0).all compactCovarianceCheck = true := by
  rw [faceSlice0_entries]
  exact allTwelveNormal compactCovarianceCheck _ _ _ _ _ _ _ _ _ _ _ _
    faceSlice0_normal0 faceSlice0_normal1 faceSlice0_normal2 faceSlice0_normal3
    faceSlice0_normal4 faceSlice0_normal5 faceSlice0_normal6 faceSlice0_normal7
    faceSlice0_normal8 faceSlice0_normal9 faceSlice0_normal10 faceSlice0_normal11

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
