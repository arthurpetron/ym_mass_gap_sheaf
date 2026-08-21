/- Process-isolated exact stored row-sum check, row 36. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem cutoffTwoSectorRawRowSumRow36_checked :
    cutoffTwoSectorRawRowSumCheck 36 = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck.cutoffTwoSectorRawRowSumRow36_checked
