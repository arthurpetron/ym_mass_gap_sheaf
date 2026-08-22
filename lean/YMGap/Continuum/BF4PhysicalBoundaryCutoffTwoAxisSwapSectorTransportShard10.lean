/- Compact aggregate for first-axis-swap states
51 through 55. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State51
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State52
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State53
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State54
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State55

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard10

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard10Indices : List (Fin 65) :=
  [51, 52, 53, 54, 55]

theorem axisSwap01Shard10AllChecked :
    axisSwap01Shard10Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard10Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State51LinkTransportCheckedAt,
    axisSwap01State52LinkTransportCheckedAt,
    axisSwap01State53LinkTransportCheckedAt,
    axisSwap01State54LinkTransportCheckedAt,
    axisSwap01State55LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard10

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard10.axisSwap01Shard10AllChecked
