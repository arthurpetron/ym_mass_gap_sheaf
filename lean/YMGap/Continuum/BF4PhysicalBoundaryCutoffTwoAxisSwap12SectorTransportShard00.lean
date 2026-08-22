/- Compact aggregate for second-axis-swap states
1 through 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard00Indices : List (Fin 65) :=
  [1, 2, 3, 4, 5]

theorem axisSwap12Shard00AllChecked :
    axisSwap12Shard00Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard00Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State01LinkTransportCheckedAt,
    axisSwap12State02LinkTransportCheckedAt,
    axisSwap12State03LinkTransportCheckedAt,
    axisSwap12State04LinkTransportCheckedAt,
    axisSwap12State05LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00.axisSwap12Shard00AllChecked
