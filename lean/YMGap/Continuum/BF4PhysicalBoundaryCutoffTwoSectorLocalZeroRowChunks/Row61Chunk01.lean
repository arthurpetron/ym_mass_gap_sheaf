/- Generated local-zero row 61, chunk 1. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

def cutoffTwoSectorLocalZeroRow61Chunk01Check : Bool :=
  ([22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]).all fun column =>
    cutoffTwoSectorLocalZeroEntryCheck 61 column

theorem cutoffTwoSectorLocalZeroRow61Chunk01Check_checked :
    cutoffTwoSectorLocalZeroRow61Chunk01Check = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.cutoffTwoSectorLocalZeroRow61Chunk01Check_checked
