/- Generated five-row local-zero aggregate chunk 2. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row14

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

theorem cutoffTwoSectorLocalZeroRowsChunk02_checked :
    ([10, 11, 12, 13, 14]).all cutoffTwoSectorLocalZeroRowCheck = true := by
  simp only [List.all_cons, List.all_nil, cutoffTwoSectorLocalZeroRow10_checked, cutoffTwoSectorLocalZeroRow11_checked, cutoffTwoSectorLocalZeroRow12_checked, cutoffTwoSectorLocalZeroRow13_checked, cutoffTwoSectorLocalZeroRow14_checked]
  rfl

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.cutoffTwoSectorLocalZeroRowsChunk02_checked
