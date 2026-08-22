/- Compact aggregate for second-axis-swap states
41 through 45. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State41
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State42
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State43
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State44
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates.State45

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard08

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

def axisSwap12Shard08Indices : List (Fin 65) :=
  [41, 42, 43, 44, 45]

theorem axisSwap12Shard08AllChecked :
    axisSwap12Shard08Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard08Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap12State41LinkTransportCheckedAt,
    axisSwap12State42LinkTransportCheckedAt,
    axisSwap12State43LinkTransportCheckedAt,
    axisSwap12State44LinkTransportCheckedAt,
    axisSwap12State45LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard08

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard08.axisSwap12Shard08AllChecked
