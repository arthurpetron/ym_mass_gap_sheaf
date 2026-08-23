/-
# Exact cutoff-two obstruction to a subunit row-distance rate

The canonical 65-state cutoff-two sector has a verified signed-form gap at
rate `49/50`, but the stronger mass-normalized row-total-variation criterion
need not share that rate.  This module evaluates one literal table row after
clearing the positive component-mass denominator.

For raw symmetric joint `K`, row weights `d`, and component mass `M`, the
normalized row rate is

    sum_y |M * K(x,y) - d(x) * d(y)| / (M * d(x)).

At stored row ten the numerator is strictly larger than `M * d(10)`, so its
row rate is strictly larger than one.  This is a finite cutoff-two
obstruction only.  It does not contradict the checked `49/50` signed-form gap
and does not rule out a subunit row bound on a later cofinal cutoff family.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalFormTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr_local {a b c d : Q'}
    (hac : a ≈ c) (hbd : b ≈ d) : a * b ≈ c * d :=
  Q'.eqv_trans _ (c * b) _
    (Q'.mul_eqv_congr_right _ _ b hac)
    (Q'.mul_eqv_congr_left c _ _ hbd)

/-! ## 1. The exact raw component mass -/

def cutoffTwoSectorRawMass : Q' :=
  listQSum cutoffTwoSectorRawRowSum (List.range 65)

def cutoffTwoSectorRawMassValue : Q' :=
  Q'.mkPos
    6280167100747004266260229105393860824732559645509611405537
    6277101735386680763835789423207666416102355444464034512896
    (by decide)

theorem cutoffTwoSectorRawMass_eqv_value :
    cutoffTwoSectorRawMass ≈ cutoffTwoSectorRawMassValue := by
  decide

theorem cutoffTwoSectorRawMassValue_pos :
    (0 : Q') < cutoffTwoSectorRawMassValue := by
  decide

/-! ## 2. Denominator-cleared row ten -/

def cutoffTwoSectorClearedMassNormalizedRowDistance
    (mass : Q') (row : Nat) : Q' :=
  listQSum
    (fun column =>
      Q'.abs
        (mass * cutoffTwoSectorRawKernel row column +
          (-(cutoffTwoSectorRawRowSum row *
            cutoffTwoSectorRawRowSum column))))
    (List.range 65)

def cutoffTwoSectorClearedRowTenValue : Q' :=
  Q'.mkPos
    38877615513813021413084794401595443043122231183387964719725075728643211
    1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512
    (by decide)

theorem cutoffTwoSectorClearedRowTen_eqv_value :
    cutoffTwoSectorClearedMassNormalizedRowDistance
        cutoffTwoSectorRawMassValue 10 ≈
      cutoffTwoSectorClearedRowTenValue := by
  decide

theorem cutoffTwoSectorRawRowSum_ten_eqv_value :
    cutoffTwoSectorRawRowSum 10 ≈
      Q'.mkPos 6340658942881089
        340282366920938463463374607431768211456 (by decide) := by
  decide

/-- The exact denominator-cleared row-ten distance is strictly larger than
its unit-rate denominator. -/
theorem cutoffTwoSectorClearedRowTen_gt_mass_mul_rowSum :
    cutoffTwoSectorRawMassValue * cutoffTwoSectorRawRowSum 10 <
      cutoffTwoSectorClearedMassNormalizedRowDistance
        cutoffTwoSectorRawMassValue 10 := by
  decide

/-! ## 3. Transport to the production reflected kernel -/

def cutoffTwoSectorPhysicalMass : Q' :=
  listQSum cutoffTwoSectorPhysicalRowSum (List.range 65)

def cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance
    (mass : Q') (row : Nat) : Q' :=
  listQSum
    (fun column =>
      Q'.abs
        (mass * cutoffTwoSectorPhysicalKernel row column +
          (-(cutoffTwoSectorPhysicalRowSum row *
            cutoffTwoSectorPhysicalRowSum column))))
    (List.range 65)

theorem cutoffTwoSectorPhysicalMass_eqv_rawMass :
    cutoffTwoSectorPhysicalMass ≈ cutoffTwoSectorRawMass := by
  unfold cutoffTwoSectorPhysicalMass cutoffTwoSectorRawMass
  apply listQSum_congr_on
  intro row hrow
  exact cutoffTwoSectorPhysicalRowSum_eqv_raw
    (List.mem_range.mp hrow)

theorem cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance_eqv_raw
    {physicalMass rawMass : Q'} (hmass : physicalMass ≈ rawMass)
    {row : Nat} (hrow : row < 65) :
    cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance
        physicalMass row ≈
      cutoffTwoSectorClearedMassNormalizedRowDistance rawMass row := by
  unfold cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance
    cutoffTwoSectorClearedMassNormalizedRowDistance
  apply listQSum_congr_on
  intro column hcolumn
  apply Q'.abs_eqv_congr
  apply Q'.add_eqv_congr'
  · exact mul_eqv_congr_local hmass
      (cutoffTwoSectorPhysicalKernel_eqv_raw hrow
        (List.mem_range.mp hcolumn))
  · exact Q'.neg_eqv_congr _ _
      (mul_eqv_congr_local
        (cutoffTwoSectorPhysicalRowSum_eqv_raw hrow)
        (cutoffTwoSectorPhysicalRowSum_eqv_raw
          (List.mem_range.mp hcolumn)))

/-- In production-kernel coordinates, row ten violates the unit
mass-normalized row-distance bound. -/
theorem cutoffTwoSectorPhysicalClearedRowTen_gt_mass_mul_rowSum :
    cutoffTwoSectorPhysicalMass * cutoffTwoSectorPhysicalRowSum 10 <
      cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance
        cutoffTwoSectorPhysicalMass 10 := by
  have hmass : cutoffTwoSectorPhysicalMass ≈
      cutoffTwoSectorRawMassValue :=
    Q'.eqv_trans _ _ _ cutoffTwoSectorPhysicalMass_eqv_rawMass
      cutoffTwoSectorRawMass_eqv_value
  have hdenominator :
      cutoffTwoSectorPhysicalMass * cutoffTwoSectorPhysicalRowSum 10 ≈
        cutoffTwoSectorRawMassValue * cutoffTwoSectorRawRowSum 10 :=
    mul_eqv_congr_local hmass
      (cutoffTwoSectorPhysicalRowSum_eqv_raw (by decide))
  have hdistance :
      cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance
          cutoffTwoSectorPhysicalMass 10 ≈
        cutoffTwoSectorClearedMassNormalizedRowDistance
          cutoffTwoSectorRawMassValue 10 :=
    cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance_eqv_raw
      hmass (by decide)
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hdenominator)
      cutoffTwoSectorClearedRowTen_gt_mass_mul_rowSum)
    (Q'.ge_of_eqv hdistance)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction.cutoffTwoSectorRawMass_eqv_value
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction.cutoffTwoSectorClearedRowTen_eqv_value
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction.cutoffTwoSectorClearedRowTen_gt_mass_mul_rowSum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction.cutoffTwoSectorPhysicalMass_eqv_rawMass
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction.cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance_eqv_raw
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction.cutoffTwoSectorPhysicalClearedRowTen_gt_mass_mul_rowSum
