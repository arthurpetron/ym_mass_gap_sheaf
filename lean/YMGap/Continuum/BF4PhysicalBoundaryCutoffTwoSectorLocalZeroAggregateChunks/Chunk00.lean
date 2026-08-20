/- Generated five-row local-zero aggregate chunk 0. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row04

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

theorem cutoffTwoSectorLocalZeroRowsChunk00_checked :
    ([0, 1, 2, 3, 4]).all cutoffTwoSectorLocalZeroRowCheck = true := by
  simp only [List.all_cons, List.all_nil, cutoffTwoSectorLocalZeroRow00_checked, cutoffTwoSectorLocalZeroRow01_checked, cutoffTwoSectorLocalZeroRow02_checked, cutoffTwoSectorLocalZeroRow03_checked, cutoffTwoSectorLocalZeroRow04_checked]
  rfl

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.cutoffTwoSectorLocalZeroRowsChunk00_checked
