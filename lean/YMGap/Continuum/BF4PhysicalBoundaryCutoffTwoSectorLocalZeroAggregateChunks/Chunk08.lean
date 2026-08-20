/- Generated five-row local-zero aggregate chunk 8. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row40
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row41
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row42
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row43
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row44

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

theorem cutoffTwoSectorLocalZeroRowsChunk08_checked :
    ([40, 41, 42, 43, 44]).all cutoffTwoSectorLocalZeroRowCheck = true := by
  simp only [List.all_cons, List.all_nil, cutoffTwoSectorLocalZeroRow40_checked, cutoffTwoSectorLocalZeroRow41_checked, cutoffTwoSectorLocalZeroRow42_checked, cutoffTwoSectorLocalZeroRow43_checked, cutoffTwoSectorLocalZeroRow44_checked]
  rfl

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.cutoffTwoSectorLocalZeroRowsChunk08_checked
