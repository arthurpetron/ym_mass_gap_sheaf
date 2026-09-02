/-
# Positive target and ceiling for finite constant-fiber switching

The crossed source and target occurrence totals are strictly positive at every
finite positive-coupling datum.  This file seals a constructively selected
positive target occurrence and the exact source-total/target-weight ceiling
behind an opaque module boundary.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberTotals
import YMGap.Continuum.FiniteBistochasticPositiveTarget

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingSupport
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.FiniteBistochasticPositiveTarget
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

/-- Constructively selected positive target occurrence. -/
opaque fixedGrowingRawPartitionPositiveTargetIndex
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) :
    FinitePositiveEntry
      (fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionTargetIndices
        w (Q'.le_of_lt hw) K volume) :=
  finitePositiveEntryOfSumPos
    (fixedGrowingRawPartitionTargetIndexWeight
      w (Q'.le_of_lt hw) K volume)
    (fun index => fixedGrowingRawPartitionTargetIndexWeight_nonnegative
      (Q'.le_of_lt hw) K volume index)
    (fixedGrowingRawPartitionTargetIndices
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)

/-- Exact finite source-total/selected-target ceiling. -/
def fixedGrowingRawPartitionConstantFiberCeiling
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) : Q' :=
  Q'.divPos
    (listQSum
      (fixedGrowingRawPartitionSourceIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionSourceIndices
        w (Q'.le_of_lt hw) K volume))
    (fixedGrowingRawPartitionTargetIndexWeight
      w (Q'.le_of_lt hw) K volume
      (fixedGrowingRawPartitionPositiveTargetIndex
        w hw K hK volume).item)
    (fixedGrowingRawPartitionPositiveTargetIndex
      w hw K hK volume).value_pos

theorem fixedGrowingRawPartitionConstantFiberCeiling_pos
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    (0 : Q') <
      fixedGrowingRawPartitionConstantFiberCeiling
        w hw K hK volume := by
  unfold fixedGrowingRawPartitionConstantFiberCeiling
  exact Q'.divPos_pos _ _ _
    (fixedGrowingRawPartitionSourceIndexTotal_pos hw hK volume)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionSourceIndexTotal_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionTargetIndexTotal_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionPositiveTargetIndex
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionConstantFiberCeiling_pos
