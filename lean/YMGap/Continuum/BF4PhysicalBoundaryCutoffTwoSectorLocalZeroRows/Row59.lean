/- Generated chunked local-zero row 59. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRowChunks.Row59Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRowChunks.Row59Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRowChunks.Row59Chunk02

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

theorem cutoffTwoSectorLocalZeroRow59_checked :
    cutoffTwoSectorLocalZeroRowCheck 59 = true := by
  unfold cutoffTwoSectorLocalZeroRowCheck
  have hsplit : List.range 65 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] ++ [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43] ++ [44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64] := by
    decide
  have hfirst :
      ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]).all (fun column =>
        cutoffTwoSectorLocalZeroEntryCheck 59 column) = true := by
    exact cutoffTwoSectorLocalZeroRow59Chunk00Check_checked
  have hsecond :
      ([22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]).all (fun column =>
        cutoffTwoSectorLocalZeroEntryCheck 59 column) = true := by
    exact cutoffTwoSectorLocalZeroRow59Chunk01Check_checked
  have hthird :
      ([44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64]).all (fun column =>
        cutoffTwoSectorLocalZeroEntryCheck 59 column) = true := by
    exact cutoffTwoSectorLocalZeroRow59Chunk02Check_checked
  rw [hsplit, List.all_append, List.all_append,
    hfirst, hsecond, hthird]
  rfl

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.cutoffTwoSectorLocalZeroRow59_checked
