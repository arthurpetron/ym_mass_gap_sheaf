/-
# A surviving geometric response bounds the margin per physical spacing

If f <= C*q^n and 0<=q<=1, multiplicative Bernoulli gives n*(1-q)*f<=C.
For n=floor(t/a), a<=t/2 implies a*n>=t/2. Thus

    (1-q)/a <= C/(f*(t/2)).

The positive response floor and norm ceiling are inputs, not constructed
here. This quantitative necessary condition has the original Wilson
autocorrelation as its immediate consumer. All constants are rational data.
-/

import YMGap.Continuum.PhysicalSeparationSamplingEscape
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.PhysicalSamplingSurvivalMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero

local infix:50 " ≈ " => Q'.eqv

theorem powerWeightedMargin_le_one {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) (n : Nat) :
    (Q'.ofNat n * (1 + -q)) * q^n ≤ (1 : Q') :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (HKConvGen.ofNat_mul_le_bScale (Q'.sub_nonneg_of_le hq1) n)
      (Q'.pow_nonneg q hq0 n))
    (HKConvGen.bernoulli_pow hq0 hq1 n)

/-- The response floor bounds the accumulated dimensionless margin. -/
theorem steps_margin_mul_floor_le {q C floor : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) (hC : (0 : Q') ≤ C)
    (n : Nat) (hfloor : floor ≤ q^n * C) :
    (Q'.ofNat n * (1 + -q)) * floor ≤ C := by
  have hn : (0 : Q') ≤ Q'.ofNat n * (1 + -q) :=
    Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg n) (Q'.sub_nonneg_of_le hq1)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor hn)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ C (powerWeightedMargin_le_one hq0 hq1 n) hC)
        (Q'.le_of_eqv (Q'.one_mul_eqv C))))

private theorem sub_half (x : Q') :
    (x + -(HalfPow.half * x)) ≈ HalfPow.half * x := by
  let h := HalfPow.half * x
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right x (h+h) (-h) (Q'.eqv_symm (ExpNeg.two_halves x)))
    (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv h h (-h))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left h _ _ (Q'.add_neg_self_eqv h))
        (Q'.eqv_of_eq (Q'.add_zero' h))))

/-- After a<=t/2, the actual floor sampler retains at least half the physical time. -/
theorem half_time_le_sampledDistance (A : PhysicalSpacing) (j t : Nat)
    (ha : A.spacing j ≤ HalfPow.half * Q'.ofNat t) :
    HalfPow.half * Q'.ofNat t ≤ A.spacing j * Q'.ofNat (floorLatticeSteps A j t) := by
  have h := Q'.le_trans' _ _ _ (le_sampledDistance_add_spacing A j t)
    (Q'.add_le_add_left _ _ _ ha)
  have hc := Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (sub_half (Q'.ofNat t)))
    (Q'.sub_le_of_le_add hc)

theorem positive_physical_time {t : Nat} (ht : 0 < t) : (0 : Q') < Q'.ofNat t := by
  change (0 : Int)*1 < (t : Int)*1
  simpa only [Int.mul_one] using (Int.ofNat_lt.mpr ht)

/-- The positive denominator f*(t/2) is retained, rather than divided out implicitly. -/
theorem responseDenominator_pos {floor : Q'} (hf : (0 : Q') < floor)
    {t : Nat} (ht : 0 < t) : (0 : Q') < floor * (HalfPow.half * Q'.ofNat t) :=
  Q'.mul_pos hf (ExpNeg.half_mul_pos _ (positive_physical_time ht))

/-- Computed finite ceiling 2*C/(f*t) for the certified margin per two-step spacing. -/
def responseMarginCeiling (C floor : Q') (hf : (0 : Q') < floor)
    (t : Nat) (ht : 0 < t) : Q' :=
  Q'.divPos C (floor * (HalfPow.half * Q'.ofNat t)) (responseDenominator_pos hf ht)

theorem responseMarginCeiling_nonnegative {C floor : Q'} (hC : (0 : Q') ≤ C)
    (hf : (0 : Q') < floor) {t : Nat} (ht : 0 < t) :
    (0 : Q') ≤ responseMarginCeiling C floor hf t ht :=
  Q'.mul_nonneg _ _ hC (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem shuffle (a b c : Q') : (a*b)*c ≈ b*(c*a) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- A pointwise original response floor implies the quantitative O(a) margin bound. -/
theorem margin_le_spacing_mul_ceiling {q C floor : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) (hC : (0 : Q') ≤ C)
    (hf : (0 : Q') < floor) (A : PhysicalSpacing) (j t : Nat) (ht : 0 < t)
    (ha : A.spacing j ≤ HalfPow.half * Q'.ofNat t)
    (hfloor : floor ≤ q^(floorLatticeSteps A j t) * C) :
    1 + -q ≤ A.spacing j * responseMarginCeiling C floor hf t ht := by
  let n := floorLatticeSteps A j t
  let d := (1 : Q') + -q
  let den := floor * (HalfPow.half * Q'.ofNat t)
  have hdf : (0 : Q') ≤ d*floor :=
    Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hq1) (Q'.le_of_lt hf)
  have hsample := Q'.mul_le_mul_of_nonneg_right _ _ (d*floor)
    (half_time_le_sampledDistance A j t ha) hdf
  have hsteps := Q'.mul_le_mul_of_nonneg_left _ _ (A.spacing j)
    (steps_margin_mul_floor_le hq0 hq1 hC n hfloor) (Q'.le_of_lt (A.spacing_pos j))
  have hregroup : ((A.spacing j * Q'.ofNat n) * (d*floor)) ≈
      A.spacing j * ((Q'.ofNat n*d)*floor) := by
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    ac_rfl
  have hprod : den * d ≤ A.spacing j * C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (shuffle floor (HalfPow.half * Q'.ofNat t) d))
      (Q'.le_trans' _ _ _ hsample (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) hsteps))
  apply HKConvGen.mul_le_mul_left_cancel (responseDenominator_pos hf ht)
  have hcancel : den * (A.spacing j * responseMarginCeiling C floor hf t ht) ≈
      A.spacing j * C := by
    exact Q'.eqv_trans _ _ _ (ClusteringImpliesGap.mul_comm_assoc _ _ _)
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.divPos_mul_eqv C den (responseDenominator_pos hf ht))))
  exact Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv hcancel)

/-- The same estimate after explicit division by the supplied positive spacing. -/
theorem marginRate_le_ceiling {q C floor : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) (hC : (0 : Q') ≤ C)
    (hf : (0 : Q') < floor) (A : PhysicalSpacing) (j t : Nat) (ht : 0 < t)
    (ha : A.spacing j ≤ HalfPow.half * Q'.ofNat t)
    (hfloor : floor ≤ q^(floorLatticeSteps A j t) * C) :
    Q'.divPos (1 + -q) (A.spacing j) (A.spacing_pos j) ≤
      responseMarginCeiling C floor hf t ht := by
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ (margin_le_spacing_mul_ceiling hq0 hq1 hC hf A j t ht ha hfloor)
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

#print axioms powerWeightedMargin_le_one
#print axioms steps_margin_mul_floor_le
#print axioms half_time_le_sampledDistance
#print axioms positive_physical_time
#print axioms responseDenominator_pos
#print axioms responseMarginCeiling
#print axioms responseMarginCeiling_nonnegative
#print axioms margin_le_spacing_mul_ceiling
#print axioms marginRate_le_ceiling

end YMGap.Continuum.PhysicalSamplingSurvivalMargin
