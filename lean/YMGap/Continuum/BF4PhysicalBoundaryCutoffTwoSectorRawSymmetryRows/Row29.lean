/- Stored raw-kernel symmetry row 29. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem cutoffTwoSectorRawSymmetryRow29_checked :
    cutoffTwoSectorRawSymmetryRowCheck 29 = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck.cutoffTwoSectorRawSymmetryRow29_checked

