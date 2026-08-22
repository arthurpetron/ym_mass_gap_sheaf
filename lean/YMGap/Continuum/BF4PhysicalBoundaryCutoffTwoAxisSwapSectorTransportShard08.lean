/- Compact aggregate for first-axis-swap states
41 through 45. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State41
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State42
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State43
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State44
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State45

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard08

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard08Indices : List (Fin 65) :=
  [41, 42, 43, 44, 45]

theorem axisSwap01Shard08AllChecked :
    axisSwap01Shard08Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard08Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State41LinkTransportCheckedAt,
    axisSwap01State42LinkTransportCheckedAt,
    axisSwap01State43LinkTransportCheckedAt,
    axisSwap01State44LinkTransportCheckedAt,
    axisSwap01State45LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard08

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard08.axisSwap01Shard08AllChecked
