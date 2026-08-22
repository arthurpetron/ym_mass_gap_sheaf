/- Compact aggregate for second-axis-swap states
11 through 15. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State15

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard02Indices : List (Fin 65) :=
  [11, 12, 13, 14, 15]

theorem axisSwap12Shard02AllChecked :
    axisSwap12Shard02Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard02Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State11LinkTransportCheckedAt,
    axisSwap12State12LinkTransportCheckedAt,
    axisSwap12State13LinkTransportCheckedAt,
    axisSwap12State14LinkTransportCheckedAt,
    axisSwap12State15LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02.axisSwap12Shard02AllChecked
