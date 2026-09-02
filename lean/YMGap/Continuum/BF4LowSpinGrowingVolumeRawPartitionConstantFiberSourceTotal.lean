/-
# Positive crossed source total for constant-fiber switching

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingSupport

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

theorem fixedGrowingRawPartitionSourceIndexTotal_pos
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    (0 : Q') <
      listQSum
        (fixedGrowingRawPartitionSourceIndexWeight
          w (Q'.le_of_lt hw) K volume)
        (fixedGrowingRawPartitionSourceIndices
          w (Q'.le_of_lt hw) K volume) := by
  have hfixed :
      (0 : Q') <
        fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K := by
    simpa only [fixedHalfSpinOneRawRow] using
      (centralPhysicalPositiveRawRowMass_pos
        (centralLowerSpinCubeState_mem_centralPositiveHalfStates hw hK))
  have hgrowingPartition :
      (0 : Q') < growingHalfPhysicalPartition w K volume := by
    unfold growingHalfPhysicalPartition
    exact slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw) K (centralExtent (volume + 1))
  have hcross :
      (0 : Q') <
        fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
          growingHalfPhysicalPartition w K volume :=
    Q'.mul_pos hfixed hgrowingPartition
  have heq := fixedGrowingRawPartitionSourceIndexSum_eqv_cross
    (Q'.le_of_lt hw) K volume
  exact Q'.pos_of_lt_of_le hcross (Q'.ge_of_eqv heq)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionSourceIndexTotal_pos
