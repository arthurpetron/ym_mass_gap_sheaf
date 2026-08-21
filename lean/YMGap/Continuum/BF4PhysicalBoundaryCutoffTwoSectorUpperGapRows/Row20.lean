/- Kernel comparison of historical row 20 with all canonical sparse entries. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGapData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem cutoffTwoSectorCanonicalUpperBridgeRow20_checked :
    cutoffTwoSectorCanonicalUpperBridgeRowCheck 20 = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap.cutoffTwoSectorCanonicalUpperBridgeRow20_checked
