/- Compact aggregate for first-axis-swap states
6 through 10. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State10

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard01

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard01Indices : List (Fin 65) :=
  [6, 7, 8, 9, 10]

theorem axisSwap01Shard01AllChecked :
    axisSwap01Shard01Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard01Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State06LinkTransportCheckedAt,
    axisSwap01State07LinkTransportCheckedAt,
    axisSwap01State08LinkTransportCheckedAt,
    axisSwap01State09LinkTransportCheckedAt,
    axisSwap01State10LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard01

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard01.axisSwap01Shard01AllChecked
