/- Compact aggregate for first-axis-swap states
16 through 20. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State16
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State17
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State18
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State19
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State20

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard03Indices : List (Fin 65) :=
  [16, 17, 18, 19, 20]

theorem axisSwap01Shard03AllChecked :
    axisSwap01Shard03Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard03Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State16LinkTransportCheckedAt,
    axisSwap01State17LinkTransportCheckedAt,
    axisSwap01State18LinkTransportCheckedAt,
    axisSwap01State19LinkTransportCheckedAt,
    axisSwap01State20LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01Shard03AllChecked
