/- Compact aggregate for second-axis-swap states
36 through 40. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State36
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State37
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State38
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State39
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State40

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard07Indices : List (Fin 65) :=
  [36, 37, 38, 39, 40]

theorem axisSwap12Shard07AllChecked :
    axisSwap12Shard07Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard07Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State36LinkTransportCheckedAt,
    axisSwap12State37LinkTransportCheckedAt,
    axisSwap12State38LinkTransportCheckedAt,
    axisSwap12State39LinkTransportCheckedAt,
    axisSwap12State40LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07.axisSwap12Shard07AllChecked
