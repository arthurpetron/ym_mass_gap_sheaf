/- Compact aggregate for first-axis-swap states
26 through 30. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State26
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State27
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State28
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State29
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State30

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard05

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard05Indices : List (Fin 65) :=
  [26, 27, 28, 29, 30]

theorem axisSwap01Shard05AllChecked :
    axisSwap01Shard05Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard05Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State26LinkTransportCheckedAt,
    axisSwap01State27LinkTransportCheckedAt,
    axisSwap01State28LinkTransportCheckedAt,
    axisSwap01State29LinkTransportCheckedAt,
    axisSwap01State30LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard05

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard05.axisSwap01Shard05AllChecked
