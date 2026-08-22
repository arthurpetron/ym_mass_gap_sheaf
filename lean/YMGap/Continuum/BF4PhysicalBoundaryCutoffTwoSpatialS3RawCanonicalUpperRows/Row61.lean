/- Process-isolated raw canonical upper row 61. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck

theorem cutoffTwoSectorRawCanonicalUpperRow61_checked :
    cutoffTwoSectorRawCanonicalUpperRowCheck (61 : Fin 65) = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows.cutoffTwoSectorRawCanonicalUpperRow61_checked
