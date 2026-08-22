/- Compact aggregate for first-axis-swap states
36 through 40. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State36
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State37
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State38
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State39
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State40

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard07

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard07Indices : List (Fin 65) :=
  [36, 37, 38, 39, 40]

theorem axisSwap01Shard07AllChecked :
    axisSwap01Shard07Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard07Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State36LinkTransportCheckedAt,
    axisSwap01State37LinkTransportCheckedAt,
    axisSwap01State38LinkTransportCheckedAt,
    axisSwap01State39LinkTransportCheckedAt,
    axisSwap01State40LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard07

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard07.axisSwap01Shard07AllChecked
