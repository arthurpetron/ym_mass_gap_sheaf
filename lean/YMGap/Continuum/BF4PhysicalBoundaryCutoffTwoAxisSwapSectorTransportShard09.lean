/- Compact aggregate for first-axis-swap states
46 through 50. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State46
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State47
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State48
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State49
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State50

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard09Indices : List (Fin 65) :=
  [46, 47, 48, 49, 50]

theorem axisSwap01Shard09AllChecked :
    axisSwap01Shard09Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard09Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State46LinkTransportCheckedAt,
    axisSwap01State47LinkTransportCheckedAt,
    axisSwap01State48LinkTransportCheckedAt,
    axisSwap01State49LinkTransportCheckedAt,
    axisSwap01State50LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01Shard09AllChecked
