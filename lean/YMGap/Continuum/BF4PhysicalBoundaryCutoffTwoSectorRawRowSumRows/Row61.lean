/- Process-isolated exact stored row-sum check, row 61. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem cutoffTwoSectorRawRowSumRow61_checked :
    cutoffTwoSectorRawRowSumCheck 61 = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck.cutoffTwoSectorRawRowSumRow61_checked
