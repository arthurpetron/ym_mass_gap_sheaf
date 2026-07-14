/-
# Full-prefix parity for the elementary cube mode

The finite trivalent resolution records cumulative selected-face parity in
each link block.  Geometric closure now implies that the final cumulative
parity is zero for every enumerated physical link, at every box scale that
contains the unit cube.
-/

import YMGap.Continuum.Z4UnitCubeEnumerationParity

namespace YMGap.Continuum.Z4UnitCubeFullPrefixParity

open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-- Taking the entire incident list leaves even selected-face parity. -/
theorem selectedPrefixCount_full_even {n : Nat} (hn : 2 ≤ n)
    (linkId : Nat) :
    selectedPrefixCount n linkId
        (incidentPlaqIdsByLinkId n linkId).length % 2 = 0 := by
  unfold selectedPrefixCount incidentPlaqIdsByLinkId
  split
  · rfl
  · rename_i indexed _
    rw [List.take_length]
    exact selectedIncidentIds_even hn indexed.2

#print axioms selectedPrefixCount_full_even

end YMGap.Continuum.Z4UnitCubeFullPrefixParity
