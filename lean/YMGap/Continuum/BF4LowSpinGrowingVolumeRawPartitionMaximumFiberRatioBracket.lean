/-
# Ratio bracket for the maximum-target finite switch

Write `S` for the crossed source occurrence total, `T` for the crossed target
occurrence total, `M` for the maximum target occurrence weight, and `N` for
the number of target occurrences.  The optimized one-target ceiling is
exactly `S / M`; this module proves the finite sandwich

    S / T <= S / M <= N * (S / T).

The lower endpoint is the aggregate raw cross ratio.  The upper endpoint
isolates the carrier-cardinality overhead of concentrating the full source
fiber on one target.  This bracket does not bound that cardinality uniformly,
does not produce a cofinal contraction, and makes no operator, continuum, or
Clay claim.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching
open YMGap.Continuum.FinitePositiveMaximumEntry
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Aggregate crossed-total ratio -/

/-- Crossed source occurrence total divided by crossed target occurrence
total.  Both totals are strictly positive on the present finite ray. -/
def fixedGrowingRawPartitionCrossTotalRatio
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) : Q' :=
  Q'.divPos
    (listQSum
      (fixedGrowingRawPartitionSourceIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionSourceIndices
        w (Q'.le_of_lt hw) K volume))
    (listQSum
      (fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionTargetIndices
        w (Q'.le_of_lt hw) K volume))
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)

theorem fixedGrowingRawPartitionCrossTotalRatio_pos
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    (0 : Q') < fixedGrowingRawPartitionCrossTotalRatio
      w hw K hK volume := by
  unfold fixedGrowingRawPartitionCrossTotalRatio
  exact Q'.divPos_pos _ _ _
    (fixedGrowingRawPartitionSourceIndexTotal_pos hw hK volume)

/-! ## 2. Maximum target weight versus the target total -/

/-- The selected maximum target occurrence is one nonnegative summand of the
complete target occurrence total. -/
theorem fixedGrowingRawPartitionMaximumTargetWeight_le_targetTotal
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume
        (fixedGrowingRawPartitionPositiveMaximumTargetIndex
          w hw K hK volume).item ≤
      listQSum
        (fixedGrowingRawPartitionTargetIndexWeight
          w (Q'.le_of_lt hw) K volume)
        (fixedGrowingRawPartitionTargetIndices
          w (Q'.le_of_lt hw) K volume) := by
  let maximum := fixedGrowingRawPartitionPositiveMaximumTargetIndex
    w hw K hK volume
  exact le_listQSum_of_mem_nonnegative
    (fixedGrowingRawPartitionTargetIndexWeight
      w (Q'.le_of_lt hw) K volume)
    (fixedGrowingRawPartitionTargetIndices
      w (Q'.le_of_lt hw) K volume)
    maximum.item maximum.item_mem
    (fun index _hindex =>
      fixedGrowingRawPartitionTargetIndexWeight_nonnegative
        (Q'.le_of_lt hw) K volume index)

/-! ## 3. Exact finite ratio bracket -/

/-- The aggregate total ratio is a lower bound for the optimized one-target
ceiling.  Any one-target switch must pay at least the mass ratio `S / T`. -/
theorem fixedGrowingRawPartitionCrossTotalRatio_le_maximumFiberCeiling
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume ≤
      fixedGrowingRawPartitionMaximumFiberCeiling w hw K hK volume := by
  let sourceTotal :=
    listQSum
      (fixedGrowingRawPartitionSourceIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionSourceIndices
        w (Q'.le_of_lt hw) K volume)
  let targetTotal :=
    listQSum
      (fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionTargetIndices
        w (Q'.le_of_lt hw) K volume)
  let targetWeight := fixedGrowingRawPartitionTargetIndexWeight
    w (Q'.le_of_lt hw) K volume
  let maximum := fixedGrowingRawPartitionPositiveMaximumTargetIndex
    w hw K hK volume
  let ceiling := Q'.divPos sourceTotal (targetWeight maximum.item)
    maximum.value_pos
  change
    Q'.divPos sourceTotal targetTotal
        (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume) ≤
      ceiling
  have hmaximumLeTotal : targetWeight maximum.item ≤ targetTotal := by
    exact fixedGrowingRawPartitionMaximumTargetWeight_le_targetTotal
      hw hK volume
  have hceilingNonnegative : (0 : Q') ≤ ceiling :=
    Q'.le_of_lt
      (Q'.divPos_pos _ _ _
        (fixedGrowingRawPartitionSourceIndexTotal_pos hw hK volume))
  have hscaled :
      ceiling * targetWeight maximum.item ≤ ceiling * targetTotal :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmaximumLeTotal
      hceilingNonnegative
  have hcancel : ceiling * targetWeight maximum.item ≈ sourceTotal :=
    Q'.divPos_mul_eqv sourceTotal (targetWeight maximum.item)
      maximum.value_pos
  have hsource : sourceTotal ≤ ceiling * targetTotal :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) hscaled
  exact Q'.divPos_le_of_le_mul sourceTotal targetTotal
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume) hsource

/-- The optimized one-target ceiling is at most target cardinality times the
aggregate total ratio.  This is an exact finite statement, not a uniform
cardinality bound. -/
theorem fixedGrowingRawPartitionMaximumFiberCeiling_le_length_mul_crossTotalRatio
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    fixedGrowingRawPartitionMaximumFiberCeiling w hw K hK volume ≤
      Q'.ofNat
          (fixedGrowingRawPartitionTargetIndices
            w (Q'.le_of_lt hw) K volume).length *
        fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume := by
  let sourceTotal :=
    listQSum
      (fixedGrowingRawPartitionSourceIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionSourceIndices
        w (Q'.le_of_lt hw) K volume)
  let targetTotal :=
    listQSum
      (fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionTargetIndices
        w (Q'.le_of_lt hw) K volume)
  let targetWeight := fixedGrowingRawPartitionTargetIndexWeight
    w (Q'.le_of_lt hw) K volume
  let maximum := fixedGrowingRawPartitionPositiveMaximumTargetIndex
    w hw K hK volume
  let cardinality := Q'.ofNat
    (fixedGrowingRawPartitionTargetIndices
      w (Q'.le_of_lt hw) K volume).length
  let ratio := Q'.divPos sourceTotal targetTotal
    (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)
  change
    Q'.divPos sourceTotal (targetWeight maximum.item)
        maximum.value_pos ≤
      cardinality * ratio
  have htotalLe : targetTotal ≤ cardinality * targetWeight maximum.item := by
    exact fixedGrowingRawPartitionTargetIndexTotal_le_length_mul_maximum
      hw hK volume
  have hratioNonnegative : (0 : Q') ≤ ratio :=
    Q'.le_of_lt
      (Q'.divPos_pos _ _ _
        (fixedGrowingRawPartitionSourceIndexTotal_pos hw hK volume))
  have hscaled :
      ratio * targetTotal ≤
        ratio * (cardinality * targetWeight maximum.item) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htotalLe hratioNonnegative
  have hcancel : ratio * targetTotal ≈ sourceTotal :=
    Q'.divPos_mul_eqv sourceTotal targetTotal
      (fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume)
  have hreassociate :
      ratio * (cardinality * targetWeight maximum.item) ≈
        (cardinality * ratio) * targetWeight maximum.item := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv ratio cardinality
          (targetWeight maximum.item)))
      (Q'.mul_eqv_congr_right _ _ (targetWeight maximum.item)
        (Q'.mul_comm_eqv ratio cardinality))
  have hsource :
      sourceTotal ≤ (cardinality * ratio) * targetWeight maximum.item :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hreassociate))
  exact Q'.divPos_le_of_le_mul sourceTotal
    (targetWeight maximum.item) maximum.value_pos hsource

/-- Combined finite sandwich for the optimized one-target ceiling. -/
theorem fixedGrowingRawPartitionMaximumFiberRatioBracket
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume ≤
        fixedGrowingRawPartitionMaximumFiberCeiling w hw K hK volume ∧
      fixedGrowingRawPartitionMaximumFiberCeiling w hw K hK volume ≤
        Q'.ofNat
            (fixedGrowingRawPartitionTargetIndices
              w (Q'.le_of_lt hw) K volume).length *
          fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume := by
  exact ⟨
    fixedGrowingRawPartitionCrossTotalRatio_le_maximumFiberCeiling
      hw hK volume,
    fixedGrowingRawPartitionMaximumFiberCeiling_le_length_mul_crossTotalRatio
      hw hK volume⟩

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket.fixedGrowingRawPartitionCrossTotalRatio_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket.fixedGrowingRawPartitionMaximumTargetWeight_le_targetTotal
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket.fixedGrowingRawPartitionCrossTotalRatio_le_maximumFiberCeiling
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket.fixedGrowingRawPartitionMaximumFiberCeiling_le_length_mul_crossTotalRatio
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket.fixedGrowingRawPartitionMaximumFiberRatioBracket
