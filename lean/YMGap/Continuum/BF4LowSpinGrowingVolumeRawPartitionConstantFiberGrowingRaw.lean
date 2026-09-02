/-
# Positive growing-reference raw row for constant-fiber switching

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSourceTotal

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio

theorem growingHalfSpinOneRawRow_pos
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    (0 : Q') <
      growingHalfSpinOneRawRow w (Q'.le_of_lt hw) K volume := by
  have href :=
    (lowSpinCentralKPositiveRawReplication w hw K hK volume).reference_mem
  simpa only [growingHalfSpinOneRawRow] using
    (centralPhysicalPositiveRawRowMass_pos href)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.growingHalfSpinOneRawRow_pos
