/-
# Positive crossed totals for finite constant-fiber switching

This file isolates strict positivity of the crossed source and target
occurrence sums, together with pointwise target-weight nonnegativity.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberGrowingRaw

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

theorem fixedGrowingRawPartitionTargetIndexWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume index : Nat) :
    (0 : Q') ≤
      fixedGrowingRawPartitionTargetIndexWeight
        w hw K volume index := by
  unfold fixedGrowingRawPartitionTargetIndexWeight
    fixedGrowingRawPartitionTargetWeight
  exact Q'.mul_nonneg _ _
    (centralPositiveCompletionWeight_nonnegative
      hw K (volume + 1) (lowSpinCentralReferenceState volume) _)
    (centralPhysicalPartitionWeight_nonnegative hw K 0 _)

theorem fixedGrowingRawPartitionTargetIndexTotal_pos
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    (0 : Q') <
      listQSum
        (fixedGrowingRawPartitionTargetIndexWeight
          w (Q'.le_of_lt hw) K volume)
        (fixedGrowingRawPartitionTargetIndices
          w (Q'.le_of_lt hw) K volume) := by
  have hgrowing :
      (0 : Q') <
        growingHalfSpinOneRawRow
          w (Q'.le_of_lt hw) K volume := by
    exact growingHalfSpinOneRawRow_pos hw hK volume
  have hfixedPartition :
      (0 : Q') < fixedHalfPhysicalPartition w K := by
    unfold fixedHalfPhysicalPartition
    exact slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw) K (centralExtent 0)
  have hcross :
      (0 : Q') <
        growingHalfSpinOneRawRow w (Q'.le_of_lt hw) K volume *
          fixedHalfPhysicalPartition w K :=
    Q'.mul_pos hgrowing hfixedPartition
  have heq :
      listQSum
          (fixedGrowingRawPartitionTargetIndexWeight
            w (Q'.le_of_lt hw) K volume)
          (fixedGrowingRawPartitionTargetIndices
            w (Q'.le_of_lt hw) K volume) ≈
        growingHalfSpinOneRawRow w (Q'.le_of_lt hw) K volume *
          fixedHalfPhysicalPartition w K :=
    fixedGrowingRawPartitionTargetIndexSum_eqv_cross
      (w := w) (Q'.le_of_lt hw) K volume
  exact Q'.pos_of_lt_of_le hcross (Q'.ge_of_eqv heq)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionSourceIndexTotal_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionTargetIndexTotal_pos
