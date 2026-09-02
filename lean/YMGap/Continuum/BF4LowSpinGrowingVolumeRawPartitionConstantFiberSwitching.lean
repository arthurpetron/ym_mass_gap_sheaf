/-
# A constructive finite constant-fiber raw-partition switch

At every finite positive-coupling datum, the crossed target total is strictly
positive.  Constructive finite search therefore selects one positive target
occurrence.  Sending every source occurrence to that target and choosing the
exact source-total/target-weight ratio gives a valid weighted-fiber switching.

The resulting ceiling is explicit but may depend on cutoff and volume.  This
module proves finite existence and isolates uniform control of that ratio as
the remaining matched/cofinal problem; it does not assert such control.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberTarget

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
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constant fibers -/

private theorem list_filter_true_local {A : Type} :
    ∀ items : List A, items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => by
      change head :: tail.filter (fun _ => true) = head :: tail
      rw [list_filter_true_local tail]

private theorem list_filter_false_local {A : Type} :
    ∀ items : List A, items.filter (fun _ => false) = []
  | [] => rfl
  | _ :: tail => list_filter_false_local tail

theorem fiberWeight_constant_self
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (weight : Source → Q')
    (selected : Target) :
    fiberWeight sources weight (fun _ => selected) selected ≈
      listQSum weight sources := by
  unfold fiberWeight
  have hfilter :
      sources.filter
          (fun item => decide
            (selected = (fun _ : Source => selected) item)) =
        sources := by
    change sources.filter (fun _ : Source => decide (selected = selected)) =
      sources
    rw [decide_eq_true rfl]
    exact list_filter_true_local sources
  rw [hfilter]
  exact Q'.eqv_refl _

theorem fiberWeight_constant_other
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (weight : Source → Q')
    (selected other : Target) (hne : other ≠ selected) :
    fiberWeight sources weight (fun _ => selected) other ≈ 0 := by
  unfold fiberWeight
  have hfilter :
      sources.filter
          (fun item => decide
            (other = (fun _ : Source => selected) item)) =
        [] := by
    change sources.filter (fun _ : Source => decide (other = selected)) = []
    rw [decide_eq_false hne]
    exact list_filter_false_local sources
  rw [hfilter]
  exact Q'.eqv_refl 0

/-! ## 2. A finite switching inhabitant -/

/-- Every finite positive-coupling datum admits a support-aware weighted-fiber
switch.  Its exact ceiling is the displayed finite ratio above. -/
def fixedGrowingRawPartitionConstantFiberSwitching
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) :
    LowSpinFixedGrowingRawPartitionFiberSwitching
      w (Q'.le_of_lt hw) K volume
      (fixedGrowingRawPartitionConstantFiberCeiling
        w hw K hK volume) where
  repair := fun _ =>
    (fixedGrowingRawPartitionPositiveTargetIndex
      w hw K hK volume).item
  repair_mem := by
    intro _source _hsource
    exact (fixedGrowingRawPartitionPositiveTargetIndex
      w hw K hK volume).item_mem
  weighted_fiber_capacity := by
    intro target htarget
    let selected := fixedGrowingRawPartitionPositiveTargetIndex
      w hw K hK volume
    let sources := fixedGrowingRawPartitionSourceIndices
      w (Q'.le_of_lt hw) K volume
    let sourceWeight := fixedGrowingRawPartitionSourceIndexWeight
      w (Q'.le_of_lt hw) K volume
    let targetWeight := fixedGrowingRawPartitionTargetIndexWeight
      w (Q'.le_of_lt hw) K volume
    by_cases heq : target = selected.item
    · subst target
      have hfiber :
          fiberWeight sources sourceWeight (fun _ => selected.item)
              selected.item ≈
            listQSum sourceWeight sources :=
        fiberWeight_constant_self sources sourceWeight selected.item
      have hratio :
          fixedGrowingRawPartitionConstantFiberCeiling
                w hw K hK volume * targetWeight selected.item ≈
            listQSum sourceWeight sources := by
        simpa only [fixedGrowingRawPartitionConstantFiberCeiling,
          selected, sources, sourceWeight, targetWeight] using
          (Q'.divPos_mul_eqv
            (listQSum sourceWeight sources)
            (targetWeight selected.item) selected.value_pos)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfiber)
        (Q'.ge_of_eqv hratio)
    · have hfiberZero :
          fiberWeight sources sourceWeight (fun _ => selected.item)
              target ≈
            0 :=
        fiberWeight_constant_other
          sources sourceWeight selected.item target heq
      have hrightNonnegative :
          (0 : Q') ≤
            fixedGrowingRawPartitionConstantFiberCeiling
                w hw K hK volume * targetWeight target :=
        Q'.mul_nonneg _ _
          (Q'.le_of_lt
            (fixedGrowingRawPartitionConstantFiberCeiling_pos
              hw hK volume))
          (fixedGrowingRawPartitionTargetIndexWeight_nonnegative
            (Q'.le_of_lt hw) K volume target)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfiberZero)
        hrightNonnegative

/-- The finite constant switch immediately yields the exact raw cross
inequality with its explicit datum-dependent ceiling. -/
theorem fixedGrowingRawPartitionConstantFiber_rawCross
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
        growingHalfPhysicalPartition w K volume ≤
      (fixedGrowingRawPartitionConstantFiberCeiling w hw K hK volume *
          growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume) *
        fixedHalfPhysicalPartition w K := by
  exact
    LowSpinFixedGrowingRawPartitionFiberSwitching.rawCross
      (fixedGrowingRawPartitionConstantFiberSwitching
        w hw K hK volume)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionSourceIndexTotal_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionTargetIndexTotal_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionConstantFiberCeiling_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fiberWeight_constant_self
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fiberWeight_constant_other
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionConstantFiberSwitching
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching.fixedGrowingRawPartitionConstantFiber_rawCross
