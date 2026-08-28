/-
# The concrete seven-cube pivot retains one quarter

Package the selected seven-cube binary surface as the left physical replica
and the vacuum labelling as the right replica.  The exact corrected-slab face
order at the unique pivot is `(1,1,1,1,0)` on the left and all zero on the
right.  The production valence-five kernel theorem therefore gives every
source-target coordinate at least `1/4`.

This is the geometry-to-representation bridge for the unique exceptional
link.  The remaining global task is to choose one product target whose
realized strand component disconnects the marked faces.

Constructive contract: literal finite geometry, definitional vacuum data,
and the proved production kernel floor only; no choice principle, unchecked
existence claim, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor
import YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile

namespace YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile

/-! ## 1. One literal physical pair -/

def sevenCubeSwitchLeftPhysical : SlabLabelling :=
  slabBinarySupportLabelling 5 sevenCubeSwitchSurface

def sevenCubeSwitchRightPhysical : SlabLabelling :=
  slabBinarySupportLabelling 5 []

def sevenCubeSwitchPivotRecouplingData :
    SlabPhysicalPairRecouplingData 5 5 where
  leftPhysical := sevenCubeSwitchLeftPhysical
  rightPhysical := sevenCubeSwitchRightPhysical
  link := sevenCubeSwitchPivot
  degree_eq := sevenCubeSwitchPivot_degree_five

/-! ## 2. Exact production external words -/

private theorem sevenCubeSwitchLeftExternalSpins_eq :
    slabLinkExternalSpins 5 sevenCubeSwitchLeftPhysical
        sevenCubeSwitchPivot =
      externalSpinsOfList [1, 1, 1, 1, 0] := by
  unfold slabLinkExternalSpins sevenCubeSwitchLeftPhysical
  rw [sevenCubeSwitchPivot_spinList]

theorem sevenCubeSwitchPivot_leftExternal_zero :
    (slabLinkExternalSpins 5 sevenCubeSwitchLeftPhysical
      sevenCubeSwitchPivot) 0 = 1 := by
  rw [sevenCubeSwitchLeftExternalSpins_eq]
  rfl

theorem sevenCubeSwitchPivot_leftExternal_one :
    (slabLinkExternalSpins 5 sevenCubeSwitchLeftPhysical
      sevenCubeSwitchPivot) 1 = 1 := by
  rw [sevenCubeSwitchLeftExternalSpins_eq]
  rfl

theorem sevenCubeSwitchPivot_leftExternal_two :
    (slabLinkExternalSpins 5 sevenCubeSwitchLeftPhysical
      sevenCubeSwitchPivot) 2 = 1 := by
  rw [sevenCubeSwitchLeftExternalSpins_eq]
  rfl

theorem sevenCubeSwitchPivot_leftExternal_three :
    (slabLinkExternalSpins 5 sevenCubeSwitchLeftPhysical
      sevenCubeSwitchPivot) 3 = 1 := by
  rw [sevenCubeSwitchLeftExternalSpins_eq]
  rfl

theorem sevenCubeSwitchPivot_leftExternal_four :
    (slabLinkExternalSpins 5 sevenCubeSwitchLeftPhysical
      sevenCubeSwitchPivot) 4 = 0 := by
  rw [sevenCubeSwitchLeftExternalSpins_eq]
  rfl

theorem sevenCubeSwitchPivot_rightExternal_zero :
    (slabLinkExternalSpins 5 sevenCubeSwitchRightPhysical
      sevenCubeSwitchPivot) 0 = 0 := by
  decide

theorem sevenCubeSwitchPivot_rightExternal_one :
    (slabLinkExternalSpins 5 sevenCubeSwitchRightPhysical
      sevenCubeSwitchPivot) 1 = 0 := by
  decide

theorem sevenCubeSwitchPivot_rightExternal_two :
    (slabLinkExternalSpins 5 sevenCubeSwitchRightPhysical
      sevenCubeSwitchPivot) 2 = 0 := by
  decide

theorem sevenCubeSwitchPivot_rightExternal_three :
    (slabLinkExternalSpins 5 sevenCubeSwitchRightPhysical
      sevenCubeSwitchPivot) 3 = 0 := by
  decide

theorem sevenCubeSwitchPivot_rightExternal_four :
    (slabLinkExternalSpins 5 sevenCubeSwitchRightPhysical
      sevenCubeSwitchPivot) 4 = 0 := by
  decide

/-! ## 3. The concrete production coordinate -/

theorem sevenCubeSwitchPivot_kernel_floor
    (source :
      (slabPhysicalPairRecouplingKernelPackageFive
        sevenCubeSwitchPivotRecouplingData).Source)
    (target :
      (slabPhysicalPairRecouplingKernelPackageFive
        sevenCubeSwitchPivotRecouplingData).Target) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingKernelPackageFive
        sevenCubeSwitchPivotRecouplingData).kernel.weight source target :=
  slabPhysicalPairRecouplingKernelPackageFive_fundamentalVacuum_floor
    sevenCubeSwitchPivotRecouplingData
    sevenCubeSwitchPivot_leftExternal_zero
    sevenCubeSwitchPivot_leftExternal_one
    sevenCubeSwitchPivot_leftExternal_two
    sevenCubeSwitchPivot_leftExternal_three
    sevenCubeSwitchPivot_leftExternal_four
    sevenCubeSwitchPivot_rightExternal_zero
    sevenCubeSwitchPivot_rightExternal_one
    sevenCubeSwitchPivot_rightExternal_two
    sevenCubeSwitchPivot_rightExternal_three
    sevenCubeSwitchPivot_rightExternal_four source target

theorem sevenCubeSwitchPivot_kernel_pos
    (source :
      (slabPhysicalPairRecouplingKernelPackageFive
        sevenCubeSwitchPivotRecouplingData).Source)
    (target :
      (slabPhysicalPairRecouplingKernelPackageFive
        sevenCubeSwitchPivotRecouplingData).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFive
        sevenCubeSwitchPivotRecouplingData).kernel.weight source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (sevenCubeSwitchPivot_kernel_floor source target)

end YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor

#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor.sevenCubeSwitchPivotRecouplingData
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor.sevenCubeSwitchPivot_leftExternal_four
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor.sevenCubeSwitchPivot_kernel_floor
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor.sevenCubeSwitchPivot_kernel_pos
