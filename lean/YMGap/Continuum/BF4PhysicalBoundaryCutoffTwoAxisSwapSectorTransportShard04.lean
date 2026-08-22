/- Compact aggregate for first-axis-swap states
21 through 25. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State21
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State22
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State23
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State24
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State25

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard04Indices : List (Fin 65) :=
  [21, 22, 23, 24, 25]

theorem axisSwap01Shard04AllChecked :
    axisSwap01Shard04Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard04Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State21LinkTransportCheckedAt,
    axisSwap01State22LinkTransportCheckedAt,
    axisSwap01State23LinkTransportCheckedAt,
    axisSwap01State24LinkTransportCheckedAt,
    axisSwap01State25LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01Shard04AllChecked
