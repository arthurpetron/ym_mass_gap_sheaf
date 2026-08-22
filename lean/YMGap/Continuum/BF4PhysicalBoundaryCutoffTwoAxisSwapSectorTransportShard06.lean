/- Compact aggregate for first-axis-swap states
31 through 35. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State31
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State32
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State33
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State34
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State35

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard06Indices : List (Fin 65) :=
  [31, 32, 33, 34, 35]

theorem axisSwap01Shard06AllChecked :
    axisSwap01Shard06Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard06Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State31LinkTransportCheckedAt,
    axisSwap01State32LinkTransportCheckedAt,
    axisSwap01State33LinkTransportCheckedAt,
    axisSwap01State34LinkTransportCheckedAt,
    axisSwap01State35LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01Shard06AllChecked
