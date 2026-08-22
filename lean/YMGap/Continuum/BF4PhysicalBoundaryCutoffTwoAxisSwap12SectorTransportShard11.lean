/- Compact aggregate for second-axis-swap states
56 through 60. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State56
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State57
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State58
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State59
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State60

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard11Indices : List (Fin 65) :=
  [56, 57, 58, 59, 60]

theorem axisSwap12Shard11AllChecked :
    axisSwap12Shard11Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard11Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State56LinkTransportCheckedAt,
    axisSwap12State57LinkTransportCheckedAt,
    axisSwap12State58LinkTransportCheckedAt,
    axisSwap12State59LinkTransportCheckedAt,
    axisSwap12State60LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11.axisSwap12Shard11AllChecked
