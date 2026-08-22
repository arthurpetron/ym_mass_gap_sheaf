/- Compact aggregate for first-axis-swap states
61 through 64. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State61
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State62
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State63
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates.State64

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard12Indices : List (Fin 65) :=
  [61, 62, 63, 64]

theorem axisSwap01Shard12AllChecked :
    axisSwap01Shard12Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard12Indices
  simp only [List.all_cons, List.all_nil,
    axisSwap01State61LinkTransportCheckedAt,
    axisSwap01State62LinkTransportCheckedAt,
    axisSwap01State63LinkTransportCheckedAt,
    axisSwap01State64LinkTransportCheckedAt,
    Bool.true_and]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01Shard12AllChecked
