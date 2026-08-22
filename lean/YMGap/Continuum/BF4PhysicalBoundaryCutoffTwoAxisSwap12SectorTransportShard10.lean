/- Compact aggregate for second-axis-swap states
51 through 55. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State51
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State52
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State53
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State54
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State55

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard10

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard10Indices : List (Fin 65) :=
  [51, 52, 53, 54, 55]

theorem axisSwap12Shard10AllChecked :
    axisSwap12Shard10Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard10Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State51LinkTransportCheckedAt,
    axisSwap12State52LinkTransportCheckedAt,
    axisSwap12State53LinkTransportCheckedAt,
    axisSwap12State54LinkTransportCheckedAt,
    axisSwap12State55LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard10

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard10.axisSwap12Shard10AllChecked
