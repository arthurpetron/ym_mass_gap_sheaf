/-
# Bounded and physical membership of the elementary cube at every volume

The all-volume fusion proof produces a genuine graph-physical cube label.
This file connects that predicate to the finite constructive enumeration of
bounded and physical edge labellings.  The same label is present at every
character cutoff at least two.
-/

import YMGap.Continuum.Z4UnitCubeAllVolumePhysicality

namespace YMGap.Continuum.Z4UnitCubeAllVolumeMembership

open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeAllVolumePhysicality

/-- The cube label uses only doubled spins zero and two, independently of
the size of the surrounding finite box. -/
theorem unitCubeSurfaceLabel_mem_bounded_all_volumes (n : Nat) :
    unitCubeSurfaceLabel n ∈ boundedEdgeLabellings 2
      (usedResolutionEdges n) := by
  apply boundedEdgeLabellings_complete
  · intro edge he
    simp only [unitCubeSurfaceLabel, if_pos he]
    split
    · split <;> omega
    · split
      · omega
      · split <;> omega
  · intro edge he
    simp [unitCubeSurfaceLabel, he]

/-- Every box containing the unit cube enumerates it as a physical
cutoff-two mode. -/
theorem unitCubeSurfaceLabel_mem_physical_all_volumes
    {n : Nat} (hn : 2 ≤ n) :
    unitCubeSurfaceLabel n ∈ physicalEdgeLabellings 2
      (usedResolutionEdges n) (resolutionVertices n) := by
  exact List.mem_filter.mpr
    ⟨unitCubeSurfaceLabel_mem_bounded_all_volumes n,
      unitCubeSurfaceLabel_physical_all_volumes hn⟩

/-- Enlarging the character cutoff preserves the bounded cube label at
every volume. -/
theorem unitCubeSurfaceLabel_mem_bounded_all_volumes_at_cutoff
    {K n : Nat} (hK : 2 ≤ K) :
    unitCubeSurfaceLabel n ∈ boundedEdgeLabellings K
      (usedResolutionEdges n) := by
  have hold := boundedEdgeLabellings_sound 2
    (usedResolutionEdges n) (unitCubeSurfaceLabel n)
    (unitCubeSurfaceLabel_mem_bounded_all_volumes n)
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    have hbound := hold.1 edge hedge
    omega
  · exact hold.2

/-- Every finite box and every cutoff at least two therefore contains the
same elementary closed-surface mode. -/
theorem unitCubeSurfaceLabel_mem_physical_all_volumes_at_cutoff
    {K n : Nat} (hK : 2 ≤ K) (hn : 2 ≤ n) :
    unitCubeSurfaceLabel n ∈ physicalEdgeLabellings K
      (usedResolutionEdges n) (resolutionVertices n) := by
  exact List.mem_filter.mpr
    ⟨unitCubeSurfaceLabel_mem_bounded_all_volumes_at_cutoff hK,
      unitCubeSurfaceLabel_physical_all_volumes hn⟩

#print axioms unitCubeSurfaceLabel_mem_bounded_all_volumes
#print axioms unitCubeSurfaceLabel_mem_physical_all_volumes
#print axioms unitCubeSurfaceLabel_mem_bounded_all_volumes_at_cutoff
#print axioms unitCubeSurfaceLabel_mem_physical_all_volumes_at_cutoff

end YMGap.Continuum.Z4UnitCubeAllVolumeMembership
