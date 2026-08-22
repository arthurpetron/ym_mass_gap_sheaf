/- Compact aggregate for second-axis-swap states
21 through 25. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State21
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State22
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State23
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State24
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State25

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard04

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard04Indices : List (Fin 65) :=
  [21, 22, 23, 24, 25]

theorem axisSwap12Shard04AllChecked :
    axisSwap12Shard04Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard04Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State21LinkTransportCheckedAt,
    axisSwap12State22LinkTransportCheckedAt,
    axisSwap12State23LinkTransportCheckedAt,
    axisSwap12State24LinkTransportCheckedAt,
    axisSwap12State25LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard04

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard04.axisSwap12Shard04AllChecked
