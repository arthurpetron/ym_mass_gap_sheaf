/- Compact aggregate for first-axis-swap states
1 through 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard00

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard00Indices : List (Fin 65) :=
  [1, 2, 3, 4, 5]

theorem axisSwap01Shard00AllChecked :
    axisSwap01Shard00Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard00Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State01LinkTransportCheckedAt,
    axisSwap01State02LinkTransportCheckedAt,
    axisSwap01State03LinkTransportCheckedAt,
    axisSwap01State04LinkTransportCheckedAt,
    axisSwap01State05LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard00

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard00.axisSwap01Shard00AllChecked
