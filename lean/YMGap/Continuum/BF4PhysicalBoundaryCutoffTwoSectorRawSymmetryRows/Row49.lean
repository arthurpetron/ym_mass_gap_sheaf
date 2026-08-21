/- Stored raw-kernel symmetry row 49. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem cutoffTwoSectorRawSymmetryRow49_checked :
    cutoffTwoSectorRawSymmetryRowCheck 49 = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck.cutoffTwoSectorRawSymmetryRow49_checked

