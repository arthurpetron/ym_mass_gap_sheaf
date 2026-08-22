/- Compact aggregate for second-axis-swap states
16 through 20. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State16
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State17
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State18
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State19
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State20

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard03

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard03Indices : List (Fin 65) :=
  [16, 17, 18, 19, 20]

theorem axisSwap12Shard03AllChecked :
    axisSwap12Shard03Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard03Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State16LinkTransportCheckedAt,
    axisSwap12State17LinkTransportCheckedAt,
    axisSwap12State18LinkTransportCheckedAt,
    axisSwap12State19LinkTransportCheckedAt,
    axisSwap12State20LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard03

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard03.axisSwap12Shard03AllChecked
