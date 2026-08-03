import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face0
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face1
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face2
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face3
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face4
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face5
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face6
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face7
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face8
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face9
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face10
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2Face11

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private theorem faceSlice2_entries : faceSlice 2 =
    [faceSliceEntry 2 0, faceSliceEntry 2 1, faceSliceEntry 2 2,
     faceSliceEntry 2 3, faceSliceEntry 2 4, faceSliceEntry 2 5,
     faceSliceEntry 2 6, faceSliceEntry 2 7, faceSliceEntry 2 8,
     faceSliceEntry 2 9, faceSliceEntry 2 10, faceSliceEntry 2 11] := by decide

theorem faceSlice2_normal : (faceSlice 2).all compactCovarianceCheck = true := by
  rw [faceSlice2_entries]
  exact allTwelveNormal compactCovarianceCheck _ _ _ _ _ _ _ _ _ _ _ _
    faceSlice2_normal0 faceSlice2_normal1 faceSlice2_normal2 faceSlice2_normal3
    faceSlice2_normal4 faceSlice2_normal5 faceSlice2_normal6 faceSlice2_normal7
    faceSlice2_normal8 faceSlice2_normal9 faceSlice2_normal10 faceSlice2_normal11

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
