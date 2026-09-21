/-
# Relative slope budget for the positive shifted Jacobi factors

Each affine shifted factor has a positive constant coefficient.  This file
bounds its slope by that constant coefficient times the same base-`q^2`
geometric rate already used for the Jacobi logarithmic derivative.  Summing
the rates costs only the explicit geometric budget; no global theta-product
floor or reciprocal of such a floor is used.

This is finite rational coefficient algebra.  It does not differentiate the
original unweighted heat limit or remove the finite Jacobi weights.
-/

import YMGap.Continuum.JacobiShiftedPositiveCoefficients
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.JacobiShiftedRelativeSlope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.JTPFullProductDerivativeNormalization
open YMGap.Continuum.JacobiShiftedPositiveCoefficients

local infix:50 " ≈ " => Q'.eqv

/-- The geometric relative-slope rate at Jacobi factor `k`. -/
def rate (q : Q') (k : Nat) : Q' :=
  HKConvGen.geoIncrBase (HKConv.Cstar q) (q * q) k

/-- The sum budget for all finite prefixes of the relative-slope rates. -/
def budget (q : Q') : Q' :=
  HKConvGen.geoTailBase (HKConv.Cstar q) (q * q) 0

theorem rate_nonnegative {q : Q'} (hq0 : (0 : Q') < q) (k : Nat) :
    (0 : Q') ≤ rate q k :=
  HKConvGen.geoIncrBase_nonneg
    (Q'.le_of_lt (CReal.pos_of_num_pos (HKConv.Cstar_num_pos hq0)))
    (Q'.mul_nonneg q q (Q'.le_of_lt hq0) (Q'.le_of_lt hq0)) k

theorem budget_nonnegative {q : Q'} (hq0 : (0 : Q') < q) :
    (0 : Q') ≤ budget q :=
  HKConvGen.geoTailBase_nonneg
    (Q'.le_of_lt (CReal.pos_of_num_pos (HKConv.Cstar_num_pos hq0)))
    (Q'.mul_nonneg q q (Q'.le_of_lt hq0) (Q'.le_of_lt hq0)) 0

private theorem rate_mul_factorLB_rearrange (q : Q') (k : Nat) :
    (HKConv.Cstar q * HKPos.factorLB q) * (q * q) ^ k ≈
      rate q k * HKPos.factorLB q := by
  unfold rate HKConvGen.geoIncrBase
  exact Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (HKConv.Cstar q) (HKPos.factorLB q) ((q * q) ^ k))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (HKConv.Cstar q) _ _
        (Q'.mul_comm_eqv (HKPos.factorLB q) ((q * q) ^ k)))
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (HKConv.Cstar q) ((q * q) ^ k) (HKPos.factorLB q))))

private theorem slope_rearrange (q : Q') (k : Nat) :
    (1 + (-(ThetaConv.uAmp q k))) *
        (rate q k * HKPos.factorLB (HKPos.geoAmp q k)) ≈
      rate q k * base q k := by
  unfold base
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (1 + (-(ThetaConv.uAmp q k))) (rate q k)
        (HKPos.factorLB (HKPos.geoAmp q k))))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (HKPos.factorLB (HKPos.geoAmp q k))
        (Q'.mul_comm_eqv (1 + (-(ThetaConv.uAmp q k))) (rate q k)))
      (Q'.mul_assoc_eqv (rate q k) (1 + (-(ThetaConv.uAmp q k)))
        (HKPos.factorLB (HKPos.geoAmp q k))))

/-- The affine slope is bounded by the positive constant coefficient times a
geometrically summable rate.  This is denominator-cleared and therefore does
not divide by the full Jacobi product. -/
theorem slope_le_rate_mul_base {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (k : Nat) :
    gFacDx q k ≤ rate q k * base q k := by
  have hq0' : (0 : Q') ≤ q := Q'.le_of_lt hq0
  have hq1' : q ≤ (1 : Q') := Q'.le_of_lt hq1
  have hpow0 : (0 : Q') ≤ (q * q) ^ k :=
    Q'.pow_nonneg (q * q) (Q'.mul_nonneg q q hq0' hq0') k
  have hscaled : HKPos.two q * (q * q) ^ k ≤
      (HKConv.Cstar q * HKPos.factorLB q) * (q * q) ^ k :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (HKConv.Cstar_bound hq1) hpow0
  have htwo_q : HKPos.two (HKPos.geoAmp q k) ≤ rate q k * HKPos.factorLB q :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (HKConv.two_geoAmp_eqv q k))
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (rate_mul_factorLB_rearrange q k)))
  have hc0 : (0 : Q') ≤ HKPos.geoAmp q k :=
    Q'.le_of_lt ((HKPos.pow_succ_pos_lt_one hq0 hq1 (2 * k)).1)
  have hcq : HKPos.geoAmp q k ≤ q := HKPos.pow_succ_le_self hq0' hq1' (2 * k)
  have hLB : HKPos.factorLB q ≤ HKPos.factorLB (HKPos.geoAmp q k) :=
    HKConv.factorLB_antitone hc0 hcq hq1'
  have hr0 : (0 : Q') ≤ rate q k := rate_nonnegative hq0 k
  have htwo : HKPos.two (HKPos.geoAmp q k) ≤
      rate q k * HKPos.factorLB (HKPos.geoAmp q k) :=
    Q'.le_trans' _ _ _ htwo_q
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hLB hr0)
  have he0 : (0 : Q') ≤ 1 + (-(ThetaConv.uAmp q k)) :=
    Q'.le_of_lt (HKPos.one_sub_pos (ThetaConv.uAmp_pos_lt_one hq0 hq1 k).2)
  have hscaledEuler := Q'.mul_le_mul_of_nonneg_left _ _
    (1 + (-(ThetaConv.uAmp q k))) htwo he0
  exact Q'.le_trans' _ _ _ hscaledEuler
    (Q'.le_of_eqv (slope_rearrange q k))

/-- Every finite prefix of the relative-slope rates is bounded by the explicit
base-`q^2` geometric budget. -/
theorem prefix_le_budget {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (N : Nat) :
    finSum (rate q) N ≤ budget q := by
  have hqq0 : (0 : Q') < q * q := HKPos.q_mul_pos hq0 hq0
  have hqq1 : q * q < (1 : Q') := by
    have hqq_le_q : q * q ≤ q := by
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right q 1 q (Q'.le_of_lt hq1) (Q'.le_of_lt hq0)) ?_
      exact Q'.le_of_eqv (Q'.one_mul_eqv q)
    exact HKPos.q_lt_of_le_of_lt hqq_le_q hq1
  simpa only [rate, budget, Nat.zero_add] using
    (HKConvGen.geoTailBase_series_le
      (Q'.le_of_lt (CReal.pos_of_num_pos (HKConv.Cstar_num_pos hq0)))
      hqq0 hqq1 0 N)

end YMGap.Continuum.JacobiShiftedRelativeSlope

#print axioms YMGap.Continuum.JacobiShiftedRelativeSlope.rate
#print axioms YMGap.Continuum.JacobiShiftedRelativeSlope.budget
#print axioms YMGap.Continuum.JacobiShiftedRelativeSlope.rate_nonnegative
#print axioms YMGap.Continuum.JacobiShiftedRelativeSlope.budget_nonnegative
#print axioms YMGap.Continuum.JacobiShiftedRelativeSlope.slope_le_rate_mul_base
#print axioms YMGap.Continuum.JacobiShiftedRelativeSlope.prefix_le_budget
