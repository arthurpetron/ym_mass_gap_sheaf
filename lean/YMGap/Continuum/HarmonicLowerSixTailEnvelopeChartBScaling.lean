/-
# Exact chart-B raw scaling for the lower-six E8/E9 envelopes

E9 has the same native residual degree on both projective charts.  E8's
chart-B affine transform has native degree 85, whereas the production raw
evaluator stops at degree 83.  The two extra residual rows are proved zero
below before either evaluator is identified with the other.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeRawScaling
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffinePhysical
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAffinePhysical

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeChartBScaling

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeRawScaling
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartAPhysical
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffinePhysical
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAffinePhysical
open YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

private theorem tailEnvelopeE8Cleared_highResidualRows_zero :
    allNat 2 (fun offset =>
      allNat 45 (fun i =>
        decide
          (quadraticRawLift 89 (gridCoeff tailEnvelopeE8ClearedRows)
              (84 + offset) i = 0))) = true := by
  rfl

private theorem tailEnvelopeE8Cleared_highResidualRows_zero_at
    {offset i : Nat} (hoffset : offset < 2) (hi : i < 45) :
    quadraticRawLift 89 (gridCoeff tailEnvelopeE8ClearedRows)
        (84 + offset) i = 0 := by
  have hoffsetTrue := allNat_true_at
    tailEnvelopeE8Cleared_highResidualRows_zero hoffset
  have hiTrue := allNat_true_at hoffsetTrue hi
  exact of_decide_eq_true hiTrue

private theorem tailEnvelopeE8Cleared_outerRow_zero
    (D n : Q') {offset : Nat} (hoffset : offset < 2) :
    finSum (fun i =>
      Q'.ofInt
          (quadraticRawLift 89 (gridCoeff tailEnvelopeE8ClearedRows)
            (84 + offset) i) *
        (D ^ i * n ^ (89 - (84 + offset) - 2 * i))) 45 ≈ 0 := by
  refine Q'.eqv_trans _
    (finSum (fun _ => (0 : Q')) 45) _ ?_ ?_
  · exact finSum_eqv_congr_lt _ _ 45 (fun i hi => by
      rw [tailEnvelopeE8Cleared_highResidualRows_zero_at hoffset hi,
        RingNormaliser.ofInt_zero]
      exact Q'.zero_mul_eqv _)
  · rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

/-- Increasing E8's residual-degree cutoff from 83 to 85 adds exactly two
zero rows.  This is the normalization bridge between the two projective
charts, rather than a definitional identification of their native degrees. -/
theorem tailEnvelopeE8ClearedEval_degree85_eqv_degree83 (D n : Q') :
    quadraticPowerEval 85 44 89
        (gridCoeff tailEnvelopeE8ClearedRows) D n ≈
      tailEnvelopeE8ClearedEval D n := by
  unfold quadraticPowerEval tailEnvelopeE8ClearedEval
  let outer := fun u =>
    finSum (fun i =>
      Q'.ofInt
          (quadraticRawLift 89 (gridCoeff tailEnvelopeE8ClearedRows) u i) *
        (D ^ i * n ^ (89 - u - 2 * i))) 45
  change ((finSum outer 84 + outer 84) + outer 85) ≈ finSum outer 84
  have h84 : outer 84 ≈ 0 := by
    change
      finSum (fun i =>
        Q'.ofInt
            (quadraticRawLift 89 (gridCoeff tailEnvelopeE8ClearedRows)
              (84 + 0) i) *
          (D ^ i * n ^ (89 - (84 + 0) - 2 * i))) 45 ≈ 0
    exact tailEnvelopeE8Cleared_outerRow_zero D n (by decide)
  have h85 : outer 85 ≈ 0 := by
    change
      finSum (fun i =>
        Q'.ofInt
            (quadraticRawLift 89 (gridCoeff tailEnvelopeE8ClearedRows)
              (84 + 1) i) *
          (D ^ i * n ^ (89 - (84 + 1) - 2 * i))) 45 ≈ 0
    exact tailEnvelopeE8Cleared_outerRow_zero D n (by decide)
  have hfirst : finSum outer 84 + outer 84 ≈
      finSum outer 84 + 0 :=
    Q'.add_eqv_congr_left _ _ _ h84
  have hcombined :
      (finSum outer 84 + outer 84) + outer 85 ≈
        (finSum outer 84 + 0) + 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hfirst)
      (Q'.add_eqv_congr_left _ _ _ h85)
  exact Q'.eqv_trans _ _ _ hcombined (by
      rw [Q'.add_zero', Q'.add_zero']
      exact Q'.eqv_refl _)

theorem tailEnvelopeE8ChartBRawEval_eqv_cleared (D n : Q') :
    tailEnvelopeE8ChartBRawEval D n ≈
      tailEnvelopeE8ClearedEval D n *
        Q'.ofInt (Int.ofNat tailEnvelopeE8ChartBChartQuotient) := by
  unfold tailEnvelopeE8ChartBRawEval tailEnvelopeE8ChartBScaledRaw
  exact Q'.eqv_trans _ _ _
    (quadraticPowerEval_scale_left 85 44 89
      (gridCoeff tailEnvelopeE8ClearedRows)
      (Int.ofNat tailEnvelopeE8ChartBChartQuotient) D n)
    (Q'.mul_eqv_congr_right _ _ _
      (tailEnvelopeE8ClearedEval_degree85_eqv_degree83 D n))

theorem tailEnvelopeE9ChartBRawEval_eqv_cleared (D n : Q') :
    tailEnvelopeE9ChartBRawEval D n ≈
      tailEnvelopeE9ClearedEval D n *
        Q'.ofInt (Int.ofNat tailEnvelopeE9ChartBChartQuotient) := by
  unfold tailEnvelopeE9ChartBRawEval tailEnvelopeE9ChartBScaledRaw
    tailEnvelopeE9ClearedEval
  exact quadraticPowerEval_scale_left 87 44 89
    (gridCoeff tailEnvelopeE9ClearedRows)
    (Int.ofNat tailEnvelopeE9ChartBChartQuotient) D n

private theorem cleared_nonnegative_of_positive_scale
    {cleared raw scale : Q'} (hraw : (0 : Q') ≤ raw)
    (heq : raw ≈ cleared * scale) (hscale : (0 : Q') < scale) :
    (0 : Q') ≤ cleared := by
  have hproduct : (0 : Q') ≤ cleared * scale :=
    Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv heq)
  have hproduct' : (0 : Q') ≤ scale * cleared :=
    Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv (Q'.mul_comm_eqv cleared scale))
  exact Q'.nonneg_of_mul_pos hscale hproduct'

theorem tailEnvelopeE8ClearedEval_nonnegative_chartA
    (D n : Nat) (hn : tailEnvelopeModeChartBase ≤ n)
    (hDlow : n * n ≤ D) (hDhigh : D ≤ 2 * (n * n)) :
    (0 : Q') ≤ tailEnvelopeE8ClearedEval (Q'.ofNat D) (Q'.ofNat n) := by
  let scale := Q'.ofInt (Int.ofNat tailEnvelopeE8ChartAChartQuotient)
  have hscale : (0 : Q') < scale := by
    change (0 : Q') < Q'.ofNat tailEnvelopeE8ChartAChartQuotient
    exact ofNat_pos_of_pos _ (by decide)
  exact cleared_nonnegative_of_positive_scale
    (tailEnvelopeE8ChartARawEval_nonnegative D n hn hDlow hDhigh)
    (tailEnvelopeE8ChartARawEval_eqv_cleared
      (Q'.ofNat D) (Q'.ofNat n)) hscale

theorem tailEnvelopeE9ClearedEval_nonnegative_chartA
    (D n : Nat) (hn : tailEnvelopeModeChartBase ≤ n)
    (hDlow : n * n ≤ D) (hDhigh : D ≤ 2 * (n * n)) :
    (0 : Q') ≤ tailEnvelopeE9ClearedEval (Q'.ofNat D) (Q'.ofNat n) := by
  let scale := Q'.ofInt (Int.ofNat tailEnvelopeE9ChartAChartQuotient)
  have hscale : (0 : Q') < scale := by
    change (0 : Q') < Q'.ofNat tailEnvelopeE9ChartAChartQuotient
    exact ofNat_pos_of_pos _ (by decide)
  exact cleared_nonnegative_of_positive_scale
    (tailEnvelopeE9ChartARawEval_nonnegative D n hn hDlow hDhigh)
    (tailEnvelopeE9ChartARawEval_eqv_cleared
      (Q'.ofNat D) (Q'.ofNat n)) hscale

theorem tailEnvelopeE8ClearedEval_nonnegative_chartB
    (D n : Nat) (hn : tailEnvelopeModeChartBase ≤ n)
    (hn2D : n ≤ 2 * D) (hDhigh : D ≤ n * n) :
    (0 : Q') ≤ tailEnvelopeE8ClearedEval (Q'.ofNat D) (Q'.ofNat n) := by
  let scale := Q'.ofInt (Int.ofNat tailEnvelopeE8ChartBChartQuotient)
  have hscale : (0 : Q') < scale := by
    change (0 : Q') < Q'.ofNat tailEnvelopeE8ChartBChartQuotient
    exact ofNat_pos_of_pos _ (by decide)
  exact cleared_nonnegative_of_positive_scale
    (tailEnvelopeE8ChartBRawEval_nonnegative D n hn hn2D hDhigh)
    (tailEnvelopeE8ChartBRawEval_eqv_cleared
      (Q'.ofNat D) (Q'.ofNat n)) hscale

theorem tailEnvelopeE9ClearedEval_nonnegative_chartB
    (D n : Nat) (hn : tailEnvelopeModeChartBase ≤ n)
    (hn2D : n ≤ 2 * D) (hDhigh : D ≤ n * n) :
    (0 : Q') ≤ tailEnvelopeE9ClearedEval (Q'.ofNat D) (Q'.ofNat n) := by
  let scale := Q'.ofInt (Int.ofNat tailEnvelopeE9ChartBChartQuotient)
  have hscale : (0 : Q') < scale := by
    change (0 : Q') < Q'.ofNat tailEnvelopeE9ChartBChartQuotient
    exact ofNat_pos_of_pos _ (by decide)
  exact cleared_nonnegative_of_positive_scale
    (tailEnvelopeE9ChartBRawEval_nonnegative D n hn hn2D hDhigh)
    (tailEnvelopeE9ChartBRawEval_eqv_cleared
      (Q'.ofNat D) (Q'.ofNat n)) hscale

#print axioms tailEnvelopeE8ClearedEval_degree85_eqv_degree83
#print axioms tailEnvelopeE8ChartBRawEval_eqv_cleared
#print axioms tailEnvelopeE9ChartBRawEval_eqv_cleared
#print axioms tailEnvelopeE8ClearedEval_nonnegative_chartA
#print axioms tailEnvelopeE9ClearedEval_nonnegative_chartA
#print axioms tailEnvelopeE8ClearedEval_nonnegative_chartB
#print axioms tailEnvelopeE9ClearedEval_nonnegative_chartB

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeChartBScaling
