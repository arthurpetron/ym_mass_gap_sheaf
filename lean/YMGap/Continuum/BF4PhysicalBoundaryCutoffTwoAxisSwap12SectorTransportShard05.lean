/- Compact aggregate for second-axis-swap states
26 through 30. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State26
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State27
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State28
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State29
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State30

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard05

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard05Indices : List (Fin 65) :=
  [26, 27, 28, 29, 30]

theorem axisSwap12Shard05AllChecked :
    axisSwap12Shard05Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard05Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State26LinkTransportCheckedAt,
    axisSwap12State27LinkTransportCheckedAt,
    axisSwap12State28LinkTransportCheckedAt,
    axisSwap12State29LinkTransportCheckedAt,
    axisSwap12State30LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard05

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard05.axisSwap12Shard05AllChecked
