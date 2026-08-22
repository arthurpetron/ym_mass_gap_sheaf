/- Compact aggregate for first-axis-swap states
56 through 60. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State56
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State57
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State58
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State59
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State60

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard11

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard11Indices : List (Fin 65) :=
  [56, 57, 58, 59, 60]

theorem axisSwap01Shard11AllChecked :
    axisSwap01Shard11Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard11Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State56LinkTransportCheckedAt,
    axisSwap01State57LinkTransportCheckedAt,
    axisSwap01State58LinkTransportCheckedAt,
    axisSwap01State59LinkTransportCheckedAt,
    axisSwap01State60LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard11

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard11.axisSwap01Shard11AllChecked
