/- Process-isolated exact stored row-sum check, row 46. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem cutoffTwoSectorRawRowSumRow46_checked :
    cutoffTwoSectorRawRowSumCheck 46 = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck.cutoffTwoSectorRawRowSumRow46_checked
