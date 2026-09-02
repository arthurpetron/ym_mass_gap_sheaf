/-
# Maximum-target finite constant-fiber switching

The first finite constant-fiber switch sends all source occurrences to an
arbitrary constructively found positive target.  This module removes that
selection artifact: it chooses a positive maximum-weight target occurrence
and sends the full source fiber there.  Among one-target constant repairs this
maximizes the paid target weight.

The resulting exact ceiling still depends on coupling, cutoff, and volume.
No uniform bound, cofinal contraction, operator gap, continuum limit, or Clay
theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching
import YMGap.Continuum.FinitePositiveMaximumEntry

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveMaximumEntry
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A positive maximum target occurrence -/

/-- Constructively selected maximum-weight target occurrence. -/
opaque fixedGrowingRawPartitionPositiveMaximumTargetIndex
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) :
    FinitePositiveMaximumEntry
      (fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionTargetIndices
        w (Q'.le_of_lt hw) K volume) :=
  finitePositiveMaximumEntryOfSumPos
    (fixedGrowingRawPartitionTargetIndexWeight
      w (Q'.le_of_lt hw) K volume)
    (fun index => fixedGrowingRawPartitionTargetIndexWeight_nonnegative
      (Q'.le_of_lt hw) K volume index)
    (fixedGrowingRawPartitionTargetIndices
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)

/-- Exact full-source-total/maximum-target-weight ceiling. -/
def fixedGrowingRawPartitionMaximumFiberCeiling
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
      (fixedGrowingRawPartitionPositiveMaximumTargetIndex
        w hw K hK volume).item)
    (fixedGrowingRawPartitionPositiveMaximumTargetIndex
      w hw K hK volume).value_pos

theorem fixedGrowingRawPartitionMaximumFiberCeiling_pos
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    (0 : Q') <
      fixedGrowingRawPartitionMaximumFiberCeiling
        w hw K hK volume := by
  unfold fixedGrowingRawPartitionMaximumFiberCeiling
  exact Q'.divPos_pos _ _ _
    (fixedGrowingRawPartitionSourceIndexTotal_pos hw hK volume)

/-- The maximum selector's target weight dominates the earlier arbitrary
positive selector's target weight. -/
theorem fixedGrowingRawPartitionPositiveTargetWeight_le_maximum
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume
        (fixedGrowingRawPartitionPositiveTargetIndex
          w hw K hK volume).item ≤
      fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume
        (fixedGrowingRawPartitionPositiveMaximumTargetIndex
          w hw K hK volume).item := by
  exact
    (fixedGrowingRawPartitionPositiveMaximumTargetIndex
      w hw K hK volume).maximal
        (fixedGrowingRawPartitionPositiveTargetIndex
          w hw K hK volume).item
        (fixedGrowingRawPartitionPositiveTargetIndex
          w hw K hK volume).item_mem

/-- The full target occurrence total is bounded by target cardinality times
the selected maximum weight.  This exposes the possible carrier-size overhead
of every one-target constant repair. -/
theorem fixedGrowingRawPartitionTargetIndexTotal_le_length_mul_maximum
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    listQSum
        (fixedGrowingRawPartitionTargetIndexWeight
          w (Q'.le_of_lt hw) K volume)
        (fixedGrowingRawPartitionTargetIndices
          w (Q'.le_of_lt hw) K volume) ≤
      Q'.ofNat
          (fixedGrowingRawPartitionTargetIndices
            w (Q'.le_of_lt hw) K volume).length *
        fixedGrowingRawPartitionTargetIndexWeight
          w (Q'.le_of_lt hw) K volume
          (fixedGrowingRawPartitionPositiveMaximumTargetIndex
            w hw K hK volume).item := by
  let maximum := fixedGrowingRawPartitionPositiveMaximumTargetIndex
    w hw K hK volume
  exact
    BF4WeightedJointPerronPerturbation.listQSum_le_length_mul
      (fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (Q'.le_of_lt maximum.value_pos)
      (fixedGrowingRawPartitionTargetIndices
        w (Q'.le_of_lt hw) K volume)
      (fun target htarget => maximum.maximal target htarget)

/-- Maximizing the paid target weight can only improve the exact one-target
constant-fiber ceiling. -/
theorem fixedGrowingRawPartitionMaximumFiberCeiling_le_constant
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    fixedGrowingRawPartitionMaximumFiberCeiling w hw K hK volume ≤
      fixedGrowingRawPartitionConstantFiberCeiling
        w hw K hK volume := by
  unfold fixedGrowingRawPartitionMaximumFiberCeiling
    fixedGrowingRawPartitionConstantFiberCeiling
  let sourceTotal :=
    listQSum
      (fixedGrowingRawPartitionSourceIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionSourceIndices
        w (Q'.le_of_lt hw) K volume)
  let targetWeight := fixedGrowingRawPartitionTargetIndexWeight
    w (Q'.le_of_lt hw) K volume
  let maximum := fixedGrowingRawPartitionPositiveMaximumTargetIndex
    w hw K hK volume
  let first := fixedGrowingRawPartitionPositiveTargetIndex
    w hw K hK volume
  change
    Q'.divPos sourceTotal (targetWeight maximum.item)
        maximum.value_pos ≤
      Q'.divPos sourceTotal (targetWeight first.item)
        first.value_pos
  have htarget : targetWeight first.item ≤ targetWeight maximum.item := by
    exact maximum.maximal first.item first.item_mem
  have hrightNonnegative :
      (0 : Q') ≤
        Q'.divPos sourceTotal (targetWeight first.item)
          first.value_pos :=
    Q'.le_of_lt
      (Q'.divPos_pos _ _ _
        (fixedGrowingRawPartitionSourceIndexTotal_pos hw hK volume))
  have hscaled :
      Q'.divPos sourceTotal (targetWeight first.item) first.value_pos *
          targetWeight first.item ≤
        Q'.divPos sourceTotal (targetWeight first.item) first.value_pos *
          targetWeight maximum.item :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htarget hrightNonnegative
  have hcancel :
      Q'.divPos sourceTotal (targetWeight first.item) first.value_pos *
          targetWeight first.item ≈
        sourceTotal :=
    Q'.divPos_mul_eqv sourceTotal (targetWeight first.item)
      first.value_pos
  have hsource :
      sourceTotal ≤
        Q'.divPos sourceTotal (targetWeight first.item) first.value_pos *
          targetWeight maximum.item :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) hscaled
  exact Q'.divPos_le_of_le_mul sourceTotal
    (targetWeight maximum.item) maximum.value_pos hsource

/-! ## 2. The optimized one-target finite switch -/

/-- Sending every source occurrence to a maximum-weight target gives the
best target payment available to a one-target constant repair. -/
def fixedGrowingRawPartitionMaximumFiberSwitching
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) :
    LowSpinFixedGrowingRawPartitionFiberSwitching
      w (Q'.le_of_lt hw) K volume
      (fixedGrowingRawPartitionMaximumFiberCeiling
        w hw K hK volume) where
  repair := fun _ =>
    (fixedGrowingRawPartitionPositiveMaximumTargetIndex
      w hw K hK volume).item
  repair_mem := by
    intro _source _hsource
    exact (fixedGrowingRawPartitionPositiveMaximumTargetIndex
      w hw K hK volume).item_mem
  weighted_fiber_capacity := by
    intro target htarget
    let selected := fixedGrowingRawPartitionPositiveMaximumTargetIndex
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
          fixedGrowingRawPartitionMaximumFiberCeiling
                w hw K hK volume * targetWeight selected.item ≈
            listQSum sourceWeight sources := by
        simpa only [fixedGrowingRawPartitionMaximumFiberCeiling,
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
            fixedGrowingRawPartitionMaximumFiberCeiling
                w hw K hK volume * targetWeight target :=
        Q'.mul_nonneg _ _
          (Q'.le_of_lt
            (fixedGrowingRawPartitionMaximumFiberCeiling_pos
              hw hK volume))
          (fixedGrowingRawPartitionTargetIndexWeight_nonnegative
            (Q'.le_of_lt hw) K volume target)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfiberZero)
        hrightNonnegative

/-- The maximum-target finite switch yields its exact raw cross inequality. -/
theorem fixedGrowingRawPartitionMaximumFiber_rawCross
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
        growingHalfPhysicalPartition w K volume ≤
      (fixedGrowingRawPartitionMaximumFiberCeiling w hw K hK volume *
          growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume) *
        fixedHalfPhysicalPartition w K := by
  exact
    LowSpinFixedGrowingRawPartitionFiberSwitching.rawCross
      (fixedGrowingRawPartitionMaximumFiberSwitching
        w hw K hK volume)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching.fixedGrowingRawPartitionPositiveMaximumTargetIndex
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching.fixedGrowingRawPartitionMaximumFiberCeiling_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching.fixedGrowingRawPartitionTargetIndexTotal_le_length_mul_maximum
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching.fixedGrowingRawPartitionMaximumFiberCeiling_le_constant
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching.fixedGrowingRawPartitionMaximumFiberSwitching
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching.fixedGrowingRawPartitionMaximumFiber_rawCross
