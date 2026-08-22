/- Compact aggregate for second-axis-swap states
46 through 50. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State46
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State47
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State48
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State49
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State50

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard09

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard09Indices : List (Fin 65) :=
  [46, 47, 48, 49, 50]

theorem axisSwap12Shard09AllChecked :
    axisSwap12Shard09Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard09Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State46LinkTransportCheckedAt,
    axisSwap12State47LinkTransportCheckedAt,
    axisSwap12State48LinkTransportCheckedAt,
    axisSwap12State49LinkTransportCheckedAt,
    axisSwap12State50LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard09

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard09.axisSwap12Shard09AllChecked
