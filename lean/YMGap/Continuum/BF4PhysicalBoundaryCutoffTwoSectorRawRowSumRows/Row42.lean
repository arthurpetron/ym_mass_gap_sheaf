/- Process-isolated exact stored row-sum check, row 42. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem cutoffTwoSectorRawRowSumRow42_checked :
    cutoffTwoSectorRawRowSumCheck 42 = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck.cutoffTwoSectorRawRowSumRow42_checked
