/- Compact aggregate for second-axis-swap states
6 through 10. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State10

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard01

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard01Indices : List (Fin 65) :=
  [6, 7, 8, 9, 10]

theorem axisSwap12Shard01AllChecked :
    axisSwap12Shard01Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard01Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State06LinkTransportCheckedAt,
    axisSwap12State07LinkTransportCheckedAt,
    axisSwap12State08LinkTransportCheckedAt,
    axisSwap12State09LinkTransportCheckedAt,
    axisSwap12State10LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard01

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard01.axisSwap12Shard01AllChecked
