/- Generated five-row local-zero aggregate chunk 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row25
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row26
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row27
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row28
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row29

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

theorem cutoffTwoSectorLocalZeroRowsChunk05_checked :
    ([25, 26, 27, 28, 29]).all cutoffTwoSectorLocalZeroRowCheck = true := by
  simp only [List.all_cons, List.all_nil, cutoffTwoSectorLocalZeroRow25_checked, cutoffTwoSectorLocalZeroRow26_checked, cutoffTwoSectorLocalZeroRow27_checked, cutoffTwoSectorLocalZeroRow28_checked, cutoffTwoSectorLocalZeroRow29_checked]
  rfl

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.cutoffTwoSectorLocalZeroRowsChunk05_checked
