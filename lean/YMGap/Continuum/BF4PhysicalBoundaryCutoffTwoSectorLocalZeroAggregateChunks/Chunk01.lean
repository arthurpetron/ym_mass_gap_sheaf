/- Generated five-row local-zero aggregate chunk 1. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row09

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

theorem cutoffTwoSectorLocalZeroRowsChunk01_checked :
    ([5, 6, 7, 8, 9]).all cutoffTwoSectorLocalZeroRowCheck = true := by
  simp only [List.all_cons, List.all_nil, cutoffTwoSectorLocalZeroRow05_checked, cutoffTwoSectorLocalZeroRow06_checked, cutoffTwoSectorLocalZeroRow07_checked, cutoffTwoSectorLocalZeroRow08_checked, cutoffTwoSectorLocalZeroRow09_checked]
  rfl

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.cutoffTwoSectorLocalZeroRowsChunk01_checked
