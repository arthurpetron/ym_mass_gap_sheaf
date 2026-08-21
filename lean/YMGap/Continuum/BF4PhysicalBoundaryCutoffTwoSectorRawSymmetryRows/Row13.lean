/- Stored raw-kernel symmetry row 13. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem cutoffTwoSectorRawSymmetryRow13_checked :
    cutoffTwoSectorRawSymmetryRowCheck 13 = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck.cutoffTwoSectorRawSymmetryRow13_checked

