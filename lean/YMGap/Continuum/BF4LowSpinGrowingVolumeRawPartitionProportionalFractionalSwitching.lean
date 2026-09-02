/-
# Proportional fractional switching for the crossed raw partition

A deterministic repair must place every source occurrence in one target
fiber.  Fractional transport permits one source row to be distributed across
the full target occurrence law.  This module gives that finite interface and
inhabits it by the normalized target weights.

If `S` and `T` are the source and target occurrence totals, the proportional
kernel has exact column load `(S / T) * targetWeight`.  It therefore achieves
the aggregate ratio ceiling `S / T` with no target-cardinality overhead, and
that ceiling is optimal among all normalized fractional switches satisfying
the same column-capacity contract.

This is an exact finite mass-allocation theorem.  It does not prove that
`S / T` is uniformly bounded on the matched trajectory, does not identify a
local geometric recoupling kernel, and makes no cofinal, operator, continuum,
or Clay claim.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket
import YMGap.Continuum.FiniteWeightedProportionalKernel

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedFractionalKernelCapacity
open YMGap.Continuum.FiniteWeightedProportionalKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fractional weighted-column interface -/

/-- A normalized nonnegative rational kernel from source occurrences to
target occurrences, with source-weighted column load bounded by the displayed
multiple of each target weight. -/
structure LowSpinFixedGrowingRawPartitionFractionalSwitching
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (ceiling : Q') : Type where
  kernel : Nat → Nat → Q'
  kernel_nonnegative : ∀ source,
    source ∈ fixedGrowingRawPartitionSourceIndices w hw K volume →
      ∀ target,
        target ∈ fixedGrowingRawPartitionTargetIndices w hw K volume →
          (0 : Q') ≤ kernel source target
  row_normalized : ∀ source,
    source ∈ fixedGrowingRawPartitionSourceIndices w hw K volume →
      listQSum (kernel source)
          (fixedGrowingRawPartitionTargetIndices w hw K volume) ≈
        1
  weighted_column_capacity : ∀ target,
    target ∈ fixedGrowingRawPartitionTargetIndices w hw K volume →
      listQSum
          (fun source =>
            fixedGrowingRawPartitionSourceIndexWeight
                w hw K volume source * kernel source target)
          (fixedGrowingRawPartitionSourceIndices w hw K volume) ≤
        ceiling *
          fixedGrowingRawPartitionTargetIndexWeight
            w hw K volume target

namespace LowSpinFixedGrowingRawPartitionFractionalSwitching

/-- Exact finite Fubini turns normalized rows and column capacities into total
source/target domination. -/
theorem totalCapacity
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat} {ceiling : Q'}
    (switching :
      LowSpinFixedGrowingRawPartitionFractionalSwitching
        w hw K volume ceiling) :
    listQSum
        (fixedGrowingRawPartitionSourceIndexWeight w hw K volume)
        (fixedGrowingRawPartitionSourceIndices w hw K volume) ≤
      ceiling *
        listQSum
          (fixedGrowingRawPartitionTargetIndexWeight w hw K volume)
          (fixedGrowingRawPartitionTargetIndices w hw K volume) := by
  exact sourceWeight_total_le_of_fractionalKernelCapacity
    (fixedGrowingRawPartitionSourceIndices w hw K volume)
    (fixedGrowingRawPartitionSourceIndexWeight w hw K volume)
    (fixedGrowingRawPartitionTargetIndices w hw K volume)
    (fixedGrowingRawPartitionTargetIndexWeight w hw K volume)
    switching.kernel ceiling switching.row_normalized
    switching.weighted_column_capacity

/-- The fractional switch gives the same crossed raw-row inequality as the
deterministic weighted-fiber switch. -/
theorem rawCross
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat} {ceiling : Q'}
    (switching :
      LowSpinFixedGrowingRawPartitionFractionalSwitching
        w hw K volume ceiling) :
    fixedHalfSpinOneRawRow w hw K *
        growingHalfPhysicalPartition w K volume ≤
      (ceiling * growingHalfSpinOneRawRow w hw K volume) *
        fixedHalfPhysicalPartition w K := by
  have hsource := fixedGrowingRawPartitionSourceIndexSum_eqv_cross
    hw K volume
  have htarget := fixedGrowingRawPartitionTargetIndexSum_eqv_cross
    hw K volume
  have htotal := switching.totalCapacity
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsource)
    (Q'.le_trans' _ _ _ htotal
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left ceiling _ _ htarget)
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv ceiling
              (growingHalfSpinOneRawRow w hw K volume)
              (fixedHalfPhysicalPartition w K))))))

end LowSpinFixedGrowingRawPartitionFractionalSwitching

/-- Increasing the ceiling preserves a finite fractional switching. -/
opaque weakenFiniteFractionalSwitchingCeiling
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {smaller larger : Q'}
    (switching :
      LowSpinFixedGrowingRawPartitionFractionalSwitching
        w hw K volume smaller)
    (hle : smaller ≤ larger) :
    LowSpinFixedGrowingRawPartitionFractionalSwitching
      w hw K volume larger :=
  { kernel := switching.kernel
    kernel_nonnegative := switching.kernel_nonnegative
    row_normalized := switching.row_normalized
    weighted_column_capacity := by
      intro target htarget
      exact Q'.le_trans' _ _ _
        (switching.weighted_column_capacity target htarget)
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hle
          (fixedGrowingRawPartitionTargetIndexWeight_nonnegative
            hw K volume target)) }

/-! ## 2. Proportional target-law kernel -/

/-- Every source row is the normalized full target occurrence law. -/
def fixedGrowingRawPartitionProportionalKernel
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume _source target : Nat) : Q' :=
  normalizedTargetWeight
    (fixedGrowingRawPartitionTargetIndexWeight
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndices
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)
    target

theorem fixedGrowingRawPartitionProportionalKernel_nonnegative
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume source target : Nat) :
    (0 : Q') ≤
      fixedGrowingRawPartitionProportionalKernel
        w hw K hK volume source target := by
  unfold fixedGrowingRawPartitionProportionalKernel
  exact normalizedTargetWeight_nonnegative
    (fixedGrowingRawPartitionTargetIndexWeight
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndices
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)
    (fun index => fixedGrowingRawPartitionTargetIndexWeight_nonnegative
      (Q'.le_of_lt hw) K volume index)
    target

theorem fixedGrowingRawPartitionProportionalKernel_row_normalized
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume source : Nat) :
    listQSum
        (fixedGrowingRawPartitionProportionalKernel
          w hw K hK volume source)
        (fixedGrowingRawPartitionTargetIndices
          w (Q'.le_of_lt hw) K volume) ≈
      1 := by
  unfold fixedGrowingRawPartitionProportionalKernel
  exact normalizedTargetWeight_total_one
    (fixedGrowingRawPartitionTargetIndexWeight
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndices
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)

/-- Every target column has exactly aggregate-ratio times its target weight. -/
theorem fixedGrowingRawPartitionProportionalKernel_column_eqv
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume target : Nat) :
    listQSum
        (fun source =>
          fixedGrowingRawPartitionSourceIndexWeight
              w (Q'.le_of_lt hw) K volume source *
            fixedGrowingRawPartitionProportionalKernel
              w hw K hK volume source target)
        (fixedGrowingRawPartitionSourceIndices
          w (Q'.le_of_lt hw) K volume) ≈
      fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume *
        fixedGrowingRawPartitionTargetIndexWeight
          w (Q'.le_of_lt hw) K volume target := by
  unfold fixedGrowingRawPartitionProportionalKernel
    fixedGrowingRawPartitionCrossTotalRatio
  exact proportionalWeightedColumn_eqv
    (fixedGrowingRawPartitionSourceIndices
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionSourceIndexWeight
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndices
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndexWeight
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)
    target

/-! ## 3. Exact optimal finite fractional switch -/

/-- The proportional kernel inhabits the finite fractional switch at the
exact aggregate source/target ratio. -/
opaque fixedGrowingRawPartitionProportionalFractionalSwitching
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) :
    LowSpinFixedGrowingRawPartitionFractionalSwitching
      w (Q'.le_of_lt hw) K volume
      (fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume) :=
  { kernel := fixedGrowingRawPartitionProportionalKernel
      w hw K hK volume
    kernel_nonnegative := by
      intro source _hsource target _htarget
      exact fixedGrowingRawPartitionProportionalKernel_nonnegative
        hw hK volume source target
    row_normalized := by
      intro source _hsource
      exact fixedGrowingRawPartitionProportionalKernel_row_normalized
        hw hK volume source
    weighted_column_capacity := by
      intro target _htarget
      exact Q'.le_of_eqv
        (fixedGrowingRawPartitionProportionalKernel_column_eqv
          hw hK volume target) }

/-- The proportional fractional switch attains the aggregate-ratio raw cross
without the one-target carrier-cardinality overhead. -/
theorem fixedGrowingRawPartitionProportionalFractional_rawCross
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
        growingHalfPhysicalPartition w K volume ≤
      (fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume *
          growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume) *
        fixedHalfPhysicalPartition w K := by
  exact
    LowSpinFixedGrowingRawPartitionFractionalSwitching.rawCross
      (fixedGrowingRawPartitionProportionalFractionalSwitching
        w hw K hK volume)

/-- Any normalized fractional switching ceiling dominates the aggregate
source/target ratio.  The proportional switch therefore attains the smallest
possible ceiling for this finite column-capacity interface. -/
theorem fixedGrowingRawPartitionCrossTotalRatio_le_fractionalCeiling
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) {ceiling : Q'}
    (switching :
      LowSpinFixedGrowingRawPartitionFractionalSwitching
        w (Q'.le_of_lt hw) K volume ceiling) :
    fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume ≤
      ceiling := by
  unfold fixedGrowingRawPartitionCrossTotalRatio
  exact Q'.divPos_le_of_le_mul _ _
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)
    switching.totalCapacity

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching.LowSpinFixedGrowingRawPartitionFractionalSwitching.totalCapacity
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching.LowSpinFixedGrowingRawPartitionFractionalSwitching.rawCross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching.weakenFiniteFractionalSwitchingCeiling
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching.fixedGrowingRawPartitionProportionalKernel_row_normalized
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching.fixedGrowingRawPartitionProportionalKernel_column_eqv
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching.fixedGrowingRawPartitionProportionalFractionalSwitching
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching.fixedGrowingRawPartitionProportionalFractional_rawCross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching.fixedGrowingRawPartitionCrossTotalRatio_le_fractionalCeiling
