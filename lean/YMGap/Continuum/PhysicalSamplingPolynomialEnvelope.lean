/-
  A finite rational envelope for inverse physical spacing at the sampled scale.

  The point is only to expose the elementary polynomial envelope needed by
  scale-dependent norm estimates: at positive integer time, `1/a_j` is at
  most one more than the sampled step count.
-/

import YMGap.Continuum.PhysicalSeparationSamplingEscape
import YMGap.Continuum.PartitionUpperBound
import YMGap.Continuum.CasimirMoment
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Continuum.PhysicalSamplingPolynomialEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)

/-- The reciprocal of the positive physical spacing at scale `j`. -/
def inverseSpacing (A : PhysicalSpacing) (j : Nat) : Q' :=
  Q'.divPos 1 (A.spacing j) (A.spacing_pos j)

theorem inverseSpacing_nonneg (A : PhysicalSpacing) (j : Nat) :
    (0 : Q') ≤ inverseSpacing A j := by
  exact Q'.le_of_lt (Q'.divPos_pos 1 (A.spacing j) (A.spacing_pos j) (by decide))

private theorem sampled_succ_mul_spacing_le
    (A : PhysicalSpacing) {j t : Nat} (ht : 0 < t) :
    (1 : Q') ≤ Q'.ofNat (floorLatticeSteps A j t + 1) * A.spacing j := by
  have htime : (1 : Q') ≤ Q'.ofNat t := by
    change (1 : Int) * 1 ≤ (t : Int) * 1
    simpa only [Int.mul_one] using (Int.ofNat_le.mpr (show 1 ≤ t by omega))
  have hsample := le_sampledDistance_add_spacing A j t
  have heq : Q'.eqv (Q'.ofNat (floorLatticeSteps A j t + 1) * A.spacing j)
      (A.spacing j * Q'.ofNat (floorLatticeSteps A j t) + A.spacing j) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (A.spacing j)
        (BondMovingMoment.ofNat_succ_eqv (floorLatticeSteps A j t)))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr' (Q'.mul_comm_eqv _ _) (Q'.one_mul_eqv _)))
  exact Q'.le_trans' _ _ _ htime (Q'.le_trans' _ _ _ hsample (Q'.ge_of_eqv heq))

theorem inverseSpacing_le_sampledSucc
    (A : PhysicalSpacing) {j t : Nat} (ht : 0 < t) :
    inverseSpacing A j ≤
      Q'.ofNat (floorLatticeSteps A j t + 1) := by
  exact Q'.divPos_le_of_le_mul 1 (A.spacing j) (A.spacing_pos j)
    (sampled_succ_mul_spacing_le A ht)

private theorem ofNat_pow_eqv (d p : Nat) :
    (Q'.ofNat (d ^ p)).eqv (Q'.ofNat d ^ p) := by
  have hleft :
      (Q'.ofNat (d ^ p) * (1 : Q') ^ p).eqv (Q'.ofNat (d ^ p)) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (d ^ p)) ((1 : Q') ^ p) 1
        (CasimirMoment.one_pow_eqv p))
      (Q'.mul_one_eqv (Q'.ofNat (d ^ p)))
  have hright :
      ((Q'.ofNat d * (1 : Q')) ^ p).eqv (Q'.ofNat d ^ p) := by
    exact Q'.pow_eqv_congr (Q'.mul_one_eqv (Q'.ofNat d)) p
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ (PartitionUpperBound.ofNat_pow_mul d 1 p) hright)

theorem inverseSpacing_power_le
    (A : PhysicalSpacing) {j t : Nat} (ht : 0 < t) (p : Nat) :
    inverseSpacing A j ^ p ≤
      Q'.ofNat ((floorLatticeSteps A j t + 1) ^ p) := by
  have hpow := YMGap.Continuum.BondMovingMoment.pow_le_pow_of_le
    (inverseSpacing_nonneg A j)
    (inverseSpacing_le_sampledSucc A ht) p
  exact Q'.le_trans' _ _ _ hpow
    (Q'.le_of_eqv
      (Q'.eqv_symm (ofNat_pow_eqv (floorLatticeSteps A j t + 1) p)))

#print axioms inverseSpacing
#print axioms inverseSpacing_nonneg
#print axioms inverseSpacing_le_sampledSucc
#print axioms inverseSpacing_power_le

end YMGap.Continuum.PhysicalSamplingPolynomialEnvelope
