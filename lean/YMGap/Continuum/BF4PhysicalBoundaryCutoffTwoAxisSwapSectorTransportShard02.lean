/- Compact aggregate for first-axis-swap states
11 through 15. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State15

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard02

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard02Indices : List (Fin 65) :=
  [11, 12, 13, 14, 15]

theorem axisSwap01Shard02AllChecked :
    axisSwap01Shard02Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard02Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State11LinkTransportCheckedAt,
    axisSwap01State12LinkTransportCheckedAt,
    axisSwap01State13LinkTransportCheckedAt,
    axisSwap01State14LinkTransportCheckedAt,
    axisSwap01State15LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard02

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard02.axisSwap01Shard02AllChecked
