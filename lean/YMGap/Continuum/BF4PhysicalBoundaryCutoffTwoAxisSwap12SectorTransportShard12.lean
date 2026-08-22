/- Compact aggregate for second-axis-swap states
61 through 64. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State61
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State62
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State63
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State64

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard12

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard12Indices : List (Fin 65) :=
  [61, 62, 63, 64]

theorem axisSwap12Shard12AllChecked :
    axisSwap12Shard12Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard12Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State61LinkTransportCheckedAt,
    axisSwap12State62LinkTransportCheckedAt,
    axisSwap12State63LinkTransportCheckedAt,
    axisSwap12State64LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard12

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard12.axisSwap12Shard12AllChecked
