/- Generated local-zero row 59, chunk 2. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

def cutoffTwoSectorLocalZeroRow59Chunk02Check : Bool :=
  ([44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64]).all fun column =>
    cutoffTwoSectorLocalZeroEntryCheck 59 column

theorem cutoffTwoSectorLocalZeroRow59Chunk02Check_checked :
    cutoffTwoSectorLocalZeroRow59Chunk02Check = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.cutoffTwoSectorLocalZeroRow59Chunk02Check_checked
