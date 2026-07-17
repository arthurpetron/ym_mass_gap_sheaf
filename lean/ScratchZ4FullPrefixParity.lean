import YMGap.Continuum.Z4UnitCubeEnumerationParity

namespace YMGap.Continuum.Z4UnitCubeFullPrefixParity

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4UnitCubeEnumerationParity

theorem selectedPrefixCount_full_even {n : Nat} (hn : 2 ≤ n)
    (linkId : Nat) :
    selectedPrefixCount n linkId (incidentPlaqIdsByLinkId n linkId).length % 2 = 0 := by
  unfold selectedPrefixCount incidentPlaqIdsByLinkId
  split
  · rfl
  · rename_i indexed hindexed
    rw [List.take_length]
    exact selectedIncidentIds_even hn indexed.2

end YMGap.Continuum.Z4UnitCubeFullPrefixParity
