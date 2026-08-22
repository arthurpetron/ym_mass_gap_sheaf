/- Process-isolated raw canonical upper row 03. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck

theorem cutoffTwoSectorRawCanonicalUpperRow03_checked :
    cutoffTwoSectorRawCanonicalUpperRowCheck (3 : Fin 65) = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows.cutoffTwoSectorRawCanonicalUpperRow03_checked
