/- Compact aggregate for second-axis-swap states
31 through 35. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State31
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State32
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State33
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State34
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State35

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard06

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard06Indices : List (Fin 65) :=
  [31, 32, 33, 34, 35]

theorem axisSwap12Shard06AllChecked :
    axisSwap12Shard06Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard06Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State31LinkTransportCheckedAt,
    axisSwap12State32LinkTransportCheckedAt,
    axisSwap12State33LinkTransportCheckedAt,
    axisSwap12State34LinkTransportCheckedAt,
    axisSwap12State35LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard06

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard06.axisSwap12Shard06AllChecked
