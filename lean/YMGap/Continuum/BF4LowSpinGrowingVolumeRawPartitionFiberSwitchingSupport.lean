/-
# Support constraints for weighted raw-partition switching

The occurrence-indexed weighted-fiber producer can cross boundary channels,
so it is not refuted by a zero reference completion at one particular target.
Nevertheless its capacity law forces a sharp support obligation: a zero-weight
target fiber has zero total source mass, and every positive source occurrence
must therefore be repaired to a nonzero target occurrence.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
import YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingSupport

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
open YMGap.Continuum.FiniteDeterministicKernelPushforward

local infix:50 " ≈ " => Q'.eqv

theorem fixedGrowingRawPartitionSourceIndexWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume index : Nat) :
    (0 : Q') ≤
      fixedGrowingRawPartitionSourceIndexWeight
        w hw K volume index := by
  unfold fixedGrowingRawPartitionSourceIndexWeight
    fixedGrowingRawPartitionSourceWeight
  exact Q'.mul_nonneg _ _
    (centralPositiveCompletionWeight_nonnegative hw K 0
      (centralLowerSpinCubeState 1) _)
    (centralPhysicalPartitionWeight_nonnegative
      hw K (volume + 1) _)

/-- A target occurrence with zero weight has an exactly zero repaired source
fiber under every valid weighted switching. -/
theorem LowSpinFixedGrowingRawPartitionFiberSwitching.fiberWeight_eqv_zero_of_target_eqv_zero
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {ceiling : Q'}
    (switching : LowSpinFixedGrowingRawPartitionFiberSwitching
      w hw K volume ceiling)
    {target : Nat}
    (htarget : target ∈
      fixedGrowingRawPartitionTargetIndices w hw K volume)
    (hzero : fixedGrowingRawPartitionTargetIndexWeight
      w hw K volume target ≈ 0) :
    fiberWeight
        (fixedGrowingRawPartitionSourceIndices w hw K volume)
        (fixedGrowingRawPartitionSourceIndexWeight w hw K volume)
        switching.repair target ≈
      0 := by
  have hcapacity := switching.weighted_fiber_capacity target htarget
  have hscaledZero :
      ceiling * fixedGrowingRawPartitionTargetIndexWeight
          w hw K volume target ≈
        0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ceiling _ _ hzero)
      (Q'.mul_zero_eqv ceiling)
  have hnonpositive :
      fiberWeight
          (fixedGrowingRawPartitionSourceIndices w hw K volume)
          (fixedGrowingRawPartitionSourceIndexWeight w hw K volume)
          switching.repair target ≤
        0 :=
    Q'.le_trans' _ _ _ hcapacity (Q'.le_of_eqv hscaledZero)
  have hnonnegative :
      (0 : Q') ≤
        fiberWeight
          (fixedGrowingRawPartitionSourceIndices w hw K volume)
          (fixedGrowingRawPartitionSourceIndexWeight w hw K volume)
          switching.repair target := by
    exact fiberWeight_nonnegative _ _ _ target
      (fun index _ =>
        fixedGrowingRawPartitionSourceIndexWeight_nonnegative
          hw K volume index)
  exact Q'.eqv_of_le_le hnonpositive hnonnegative

/-- A positive source occurrence cannot be assigned to a target occurrence
whose weight is zero. -/
theorem LowSpinFixedGrowingRawPartitionFiberSwitching.repair_ne_target_of_source_pos_of_target_eqv_zero
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {ceiling : Q'}
    (switching : LowSpinFixedGrowingRawPartitionFiberSwitching
      w hw K volume ceiling)
    {source target : Nat}
    (hsource : source ∈
      fixedGrowingRawPartitionSourceIndices w hw K volume)
    (hsourcePos : (0 : Q') <
      fixedGrowingRawPartitionSourceIndexWeight
        w hw K volume source)
    (htarget : target ∈
      fixedGrowingRawPartitionTargetIndices w hw K volume)
    (htargetZero : fixedGrowingRawPartitionTargetIndexWeight
      w hw K volume target ≈ 0) :
    switching.repair source ≠ target := by
  intro heq
  have hsourceFilter : source ∈
      (fixedGrowingRawPartitionSourceIndices w hw K volume).filter
        (fun item => decide (target = switching.repair item)) := by
    exact List.mem_filter.mpr ⟨hsource, by
      simpa only [decide_eq_true_eq] using heq.symm⟩
  have hfiberPos :
      (0 : Q') <
        fiberWeight
          (fixedGrowingRawPartitionSourceIndices w hw K volume)
          (fixedGrowingRawPartitionSourceIndexWeight w hw K volume)
          switching.repair target := by
    unfold fiberWeight
    exact listQSum_pos_of_mem
      (fixedGrowingRawPartitionSourceIndexWeight w hw K volume)
      (fun index =>
        fixedGrowingRawPartitionSourceIndexWeight_nonnegative
          hw K volume index)
      ((fixedGrowingRawPartitionSourceIndices w hw K volume).filter
        (fun item => decide (target = switching.repair item)))
      (item := source) hsourceFilter hsourcePos
  have hfiberZero :=
    LowSpinFixedGrowingRawPartitionFiberSwitching.fiberWeight_eqv_zero_of_target_eqv_zero
      switching htarget htargetZero
  have hnonpositive := Q'.le_of_eqv hfiberZero
  exact (Int.not_lt_of_ge hnonpositive) hfiberPos

/-- In particular, the repair image of every positive source occurrence has
nonzero target weight. -/
theorem LowSpinFixedGrowingRawPartitionFiberSwitching.repairedTargetWeight_not_eqv_zero_of_source_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {ceiling : Q'}
    (switching : LowSpinFixedGrowingRawPartitionFiberSwitching
      w hw K volume ceiling)
    {source : Nat}
    (hsource : source ∈
      fixedGrowingRawPartitionSourceIndices w hw K volume)
    (hsourcePos : (0 : Q') <
      fixedGrowingRawPartitionSourceIndexWeight
        w hw K volume source) :
    ¬ fixedGrowingRawPartitionTargetIndexWeight
      w hw K volume (switching.repair source) ≈ 0 := by
  intro hzero
  have htarget := switching.repair_mem source hsource
  exact
    LowSpinFixedGrowingRawPartitionFiberSwitching.repair_ne_target_of_source_pos_of_target_eqv_zero
      switching hsource hsourcePos htarget hzero rfl

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingSupport

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingSupport.LowSpinFixedGrowingRawPartitionFiberSwitching.fiberWeight_eqv_zero_of_target_eqv_zero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingSupport.LowSpinFixedGrowingRawPartitionFiberSwitching.repair_ne_target_of_source_pos_of_target_eqv_zero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingSupport.LowSpinFixedGrowingRawPartitionFiberSwitching.repairedTargetWeight_not_eqv_zero_of_source_pos
